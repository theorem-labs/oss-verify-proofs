(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_B.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~06mstate37Corelib7Numbers7BinNumsk61Z04aptr37Corelib4Init9Datatypesm94Some79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentdMallocModel_B~~~~~~o89clr_links09META_SIZE04aadd04mctx0eset_avail_meta0h4set_avail_meta_count07upd_ctx08upd_meta" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition am_took : ltac2:(zQ "30!je!lf!m3>2st$0>1q$2>3cnt$1$0") := ltac2:(zQ "c0!m3!o1!lf!se!ta!u5!ub!je!v1!hg1!hh8!hi1\2st$7\1q$0\3cnt$2@3$b^2$3@2$a\1c$6@2$8@2$1$0@2$5^3$4@2$9^2^1^3").
(* [comment removed for export] *)
