(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls F_mm_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_B.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_am_A F_am_K F_am_C.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~09s_regions37Corelib4Init5Logick92eq37Corelib7Numbers7BinNumsm21N79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent6F_am_K~~~~~~nf8carve_st04aptr06mstate06region25stdpp9countabletfbN_countable25stdpp4gmapve4gmap35stdpp7numbers1Nhh16eq_dec79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6Decode~~~~~~hic9range_ans37Corelib4Init9Datatypeshn64boolm21Zhn64truek93nothn64Somehn66optionk93and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent6F_am_F~~~~~~hs09mp_stricthiccdec_mprotect79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5ITree~~~~~~ihc4resp79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~im0fdec_mprotect_rw" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma carve_st_regions : ltac2:(zQ "a0!je!ld!nb!re!s9!sf!t7!v0!hga!hi2>2st$5>1p$4@3$1@4$8$2$9$7$6@1$0@2$3^2^1@1$0^2").
Proof. intros st p.
  unfold carve_st. cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail].
  destruct (c_meta_area_tail (s_ctx st)); reflexivity.
Qed.

(* [comment removed for export] *)
Definition mp_strict : ltac2:(zQ "10!hm9>1a$0P") := ltac2:(zQ "60!hm9!hoe!ld!hp6!hpa!hq2\1a$0M0\1a$0P^1\1e$3@1$5@3$2$3^1+i6\1b$1@3$2$1^1$4").
Lemma dec_mprotect_rw_weaken : ltac2:(zQ "a0!hm9!hq8!hr0!ld!hp6!hra!hvf!igc!il8!ipc>1A$4>1L$4>3rsp$8>1a$0>0@3$3@1$2$0@3$9^4^3^2@2$1$0^1@2$5@3$3@1$2$0@3$7^5^4^3@2$1$0^2@1$6^2").
Proof. intros A L rsp a.
  unfold dec_mprotect_rw. destruct (dec_mprotect A L rsp) as [[e|b]|]; [| | discriminate].
  - destruct (Z.eqb_spec e ENOSYS); [discriminate|]. intros H; inversion H; subst. split; [reflexivity|]. cbn. unfold ENOSYS in *. exact n.
  - destruct b; [| discriminate]. intros H; inversion H; subst. split; reflexivity.
Qed.
(* [comment removed for export] *)
