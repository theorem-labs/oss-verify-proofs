(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require Import HeapMF_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require BJEhTabs.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import EhIface EhGlue.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EhX_plain EhSums.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require MallocMF.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref8MallocMF~~~~~~03HMF79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJcHeapMF_iface~~~~~~k4cheap_mf_hyps89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhIface3EHI~~~~~~p53EHK79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ8BJEhTabs~~~~~~tc9bj_ehtabs" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EHC.
Section Plain.
Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Theorem heap_mf_hyps_plain : ltac2:(zQ "30!jf!o6!t6@3$1?5HCEIL@2$0?5HCEIL?4HSEC@1$2@2$0?5HCEIL?4HSEC").
Proof. exact (EHG.heap_mf_hyps_HMF EhSums.eh_copy_spec EhSums.eh_fill_spec). Qed.

(* [comment removed for export] *)
Theorem bj_ehtabs_plain : ltac2:(zQ "30!hha!t6!jf@1$0@1$1@2$2?5HCEIL?4HSEC").
Proof. exact (EHG.L_tabs MallocMF.HMF). Qed.

End Plain.
End EHC.
(* [comment removed for export] *)
