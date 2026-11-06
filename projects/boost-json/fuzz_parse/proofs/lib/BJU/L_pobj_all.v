(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep TacX ZBridge Exec CellsX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import BJFrame HeapMF_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJU Require Import BJRep BJHeap BJIface BJIfaceObj BJIfaceObjL BJEhTabs BJHeapFloor
     W_find L_octorL L_octor L_pobj.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU8BJEhTabs~~~~~~09bj_ehtabs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJUbBJHeapFloor~~~~~~kaaheap_floor79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU7BJIface~~~~~~p9h0push_object_stmt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUcHeapMF_iface~~~~~~ub3ehkubcheap_mf_hypsub3hmf" s.
Open Scope bv_scope.
Open Scope Z_scope.

Section W.
  Context {HCEIL : HeapCeil}.

  Theorem push_object_spec_closed : ltac2:(zQ "60!jf!oc!t7!hif!hj5!hk4>1H$5>1E$3>0@3$4?5HCEIL^2^1>0@1$1^3>0@1$0^3@3$2?5HCEIL^5^4").
  Proof.
    intros H E HH HFL TABS.
    exact (push_object_spec H E HH HFL TABS (octor_spec H E HH HFL TABS find_spec (octorL_spec H E HH HFL))).
  Qed.

  (* [comment removed for export] *)
End W.
(* [comment removed for export] *)
