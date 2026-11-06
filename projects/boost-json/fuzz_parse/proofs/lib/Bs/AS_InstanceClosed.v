(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil PropExec AsanAllocModel BsMainState.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsIface AsInstance AsInstanceMain AS_InstTR AS_InstFree AS_InstFreePass AS_InstanceKit.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsbAS_InstFree~~~~~~0dfree_stmt_big79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BseAS_InstanceKit~~~~~~l03kip79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BseAsInstanceMain~~~~~~pa5KCEILpa4mctx79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsaAsInstance~~~~~~udh0as_instance_stmt69OSSVerify6Proofsaboost_jsonafuzz_parse3libbBsMainState~~~~~~hk16P_main69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~ho93fx0" s.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Existing Instance fx0.

(* [comment removed for export] *)
Lemma R_freebig_proved : ltac2:(zQ "40!k1!p4!te!u6>1k$3@2$0@1$2^1@1$1^1").
Proof. intros k. exact (@inst_free_big (KCEIL k) (kip k) TRLIST_length). Qed.

Theorem as_instance_closed : ltac2:(zQ "30!hid!hnf!hs4@2$0$2$1").
Proof. exact (as_instance_kit R_freebig_proved). Qed.
