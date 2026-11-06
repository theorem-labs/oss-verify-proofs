(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls F_mm_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_B.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_am_A F_am_K F_am_C F_am_F.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~06mstate37Corelib7Numbers7BinNumsk61Nk61Z37Corelib4Init9Datatypesm74Somem74pairm74prod0h2c_meta_alloc_shift04mctx0h9set_avail_meta_area_count0h4set_avail_meta_areas0h4set_meta_alloc_shift07upd_ctx46Stdlib6ZArith6BinInt1Zhg23addhg23sub" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mm_ok_st : ltac2:(zQ "30!je!lf!m3>2st$0>3rid$1>1n$2$0") := ltac2:(zQ "e0!lf!m3!nf!o6!od!p4!q9!je!qf!sb!u2!v9!hha!hi1\2st$7\3rid$0\1n$1@2$b\1c$6@2$a@2$c@1$5^1+1@2$8@2$d^2+1@2$9@2$2@2$4$0$1@4$3$0$1^3+hgg0^1^3").
(* [comment removed for export] *)
