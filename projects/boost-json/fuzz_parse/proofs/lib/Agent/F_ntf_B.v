(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocTree.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_B.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~04aptr06mstate37Corelib4Init5Logickc3andkc2eq37Corelib4Init9Datatypesmb4Somekc3not79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~p09meta_slot04optrkc2ex0h0c_free_meta_head03ctx0cget_meta_rec06m_prev37Corelib7Numbers7BinNumshh71Zp09meta_word05meta0" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition fm_facts : ltac2:(zQ "20!je!k4>2st$1>1g$0P") := ltac2:(zQ "d0!je!m0!m6!o3!oa!t2!te!u4!u9!vc!hg1!hgf!k4\2st$c\1g$0>4head$0>0@3$2$6@1$8@1$9^3@2$3$0^1@2$1@1$4@3$2$0^2^3@2$1@2$5^4^2@2$7$0\2pv$0@2$1@3$2$6@1$b@2$a^5^3@2$3$0^1@2$1@1$4@3$2$0^1^4@2$5^5^1").

Lemma meta_word_meta0 : ltac2:(zQ "40!m6!hj0!hj5!hk1@3$0$1@1$2$3Z"). Proof. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
