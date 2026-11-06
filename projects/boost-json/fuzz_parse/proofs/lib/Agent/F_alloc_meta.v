(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require MallocKit_A2.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls F_mm_syscalls MallocRep F_malloc_free MallocTree MallocFacts_B MallocFacts_Bpres.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_B MallocModel_B MallocKit_B2 MallocKit_B3 F_ntf_B.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_am_A F_am_K F_am_K2 F_am_C F_am_D F_am_E F_am_F F_am_G F_am_H F_am_P.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~03mem37Corelib7Numbers7BinNumsk81Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~m52wa37Corelib4Init9Datatypesq46option37Corelib4Init5Logics53ands52eqs53notk84Npos46Stdlib6ZArith6BinInt1Zv12lev12ltv13pow35stdpp9bitvectorbdefinitionshh92bv89OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcF_alloc_meta3HCW~~~~~~hjc6magreeq44list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentbMallocKit_B~~~~~~hp6bivs_covered79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~hu93ivlhu95munch" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module A2 := MallocKit_A2.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Definition magree : ltac2:(zQ "20!k3!m1>1C>0$1P>1m$0>2m'$0P") := ltac2:(zQ "c0!m1!k3!pf!rc!t9!tf!u4!ua!hg9!hge!hh3!hj6\1C>0$0P\1m$1\2m'$1>1a$0>0@2$4@2$8Z^1@2$9^1@2$a+2+k0>0@1$6@1^5^2@3$5@1$3@1$b@1$7#8@1^4@1$2^3@1^5@1$2^3").
Lemma magree_trans : ltac2:(zQ "30!m1!ho5!k3>2C1>0$0P>2C2>0$0P>2C3>0$0P>2m1$2>2m2$2>2m3$2>0@3$1^6^3^2>0@3$1^6^3^2>0>1a$0>0@1^9^1@1^8^2>0>1a$0>0@1^9^1@1^9^2@3$1^8^7^5").
Proof. intros C1 C2 C3 m1 m2 m3. intros A B I1 I2 a Ha Hc. rewrite (B a Ha) by (intros X; apply Hc, I2, X). apply A; [exact Ha|]. intros X; apply Hc, I1, X. Qed.
Lemma magree_of_munch : ltac2:(zQ "91!ua!hj6!rc!hof!m1!ho5!hta!ii5!iic&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1C>0$4P>1W@1$3$7>1m~0>2m'~0>0@3$8^3^2^1>0@2$6^5^4@3$5^6^4^3").
Proof. intros C W m m'.
  intros MU COV a Ha Hc. apply MU. rewrite wa_unsigned by lia.
  revert COV Hc. clear. induction W as [|[lo hi] W IH]; cbn; intros COV Hc; [exact I|].
  destruct COV as [C1 COV]. split; [| apply IH; assumption]. intros Hin. apply Hc. apply C1. exact Hin.
Qed.

(* [comment removed for export] *)
Section ASM.
Variables (R : Type) (k : mstate -> optr -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word).
Hypothesis AMP : AMpre st.
Hypothesis MR : mrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : auxv_ok m (bv_unsigned sp).
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - AM_STACK.
Hypothesis ERR : rw_cells asegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv asegs m.
Hypothesis GP : gp = Z_to_bv 64 0x1a800.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis KH : forall st1 mo s' ms',
     am_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' ->
     brk_link_ps st1 s' ->
     implT o (k st1 mo) s' Q ms'.

End ASM.

End HCW.

(* [comment removed for export] *)
