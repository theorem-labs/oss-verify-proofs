(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require BJ0Gc2. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep TacX ZBridge Exec CellsX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require Import BJRep BJFrame HeapMF_iface BJHeap BJIface BJIfaceStr BJIfaceTop BJIfaceLL BJEhTabs BJChainAbove.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require Import
     L_parse_value L_parse_array L_parse_object
     L_lit_null L_lit_true L_lit_false L_num0 L_numneg L_numpos
     W_dtor_value2 L_pdoc L_wsome L_jparse L_fuzz L_llvm
     BJIfaceObj BJIfaceObjL L_octor L_octorL L_pobj L_pstr L_pkey.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ7BJIface~~~~~~0eparse_key_stmt0h1parse_string_stmt0h1parse_numpos_stmt0h0push_object_stmt37Corelib4Init5Logico83and0h0parse_array_stmt0h1parse_object_stmt0h0parse_value_stmt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJaBJIfaceTop~~~~~~tcbjparse_stmt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ9BJIfaceLL~~~~~~hiafllvm_fuzz_stmt279OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJcHeapMF_iface~~~~~~hnc3hmfhnc3ehkhnccheap_mf_hyps79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ8BJEhTabs~~~~~~htc9bj_ehtabs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJcBJChainAbove~~~~~~ii7eeh_chain_above" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!hre$0").
  Variable E : ltac2:(zQ "10!hs5$0").
  Hypothesis HH : ltac2:(zQ "10!hsc@3$0?5HCEIL?1H?1E").
  Hypothesis TABS : ltac2:(zQ "10!iha@1$0?1E").
  Hypothesis HCA : ltac2:(zQ "10!im9@1$0?1E").          (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma PK : ltac2:(zQ "10!jd@3$0?5HCEIL?1H?1E").
  Proof. exact (parse_key_spec H E HH TABS HCA). Qed.

  (* [comment removed for export] *)
  Lemma ps_all : ltac2:(zQ "10!kd@3$0?5HCEIL?1H?1E").
  Proof. exact (parse_string_spec H E HH TABS HCA). Qed.

  (* [comment removed for export] *)
  Lemma pnp_all : ltac2:(zQ "10!m1@3$0?5HCEIL?1H?1E").
  Proof. exact (parse_numpos_spec H E HH TABS). Qed.
  Lemma pobj_all : ltac2:(zQ "10!n5@3$0?5HCEIL?1H?1E").
  Proof. exact (push_object_spec H E HH TABS (octor_spec H E HH TABS (octorL_spec H E HH))). Qed.

  (* [comment removed for export] *)
  Lemma parse_family : ltac2:(zQ "40!pc!q2!r5!s9@2$0@3$3?5HCEIL?1H?1E@2$0@3$1?5HCEIL?1H?1E@3$2?5HCEIL?1H?1E").
  Proof.
    apply (parse_family_by_depth H E).
    - intros d PV. exact (PA_STEP H E HH TABS d PV).
    - intros d PV. exact (PO_STEP H E HH TABS PK pobj_all d PV).
    - intros d PA PO. exact (PV_STEP H E HH d PA PO ps_all (parse_num0_spec H E HH TABS) (parse_numneg_spec H E HH TABS) pnp_all
                               (parse_null_spec H E HH TABS) (parse_true_spec H E HH TABS) (parse_false_spec H E HH TABS)).
  Qed.

  Lemma parse_value_all : ltac2:(zQ "10!s9@3$0?5HCEIL?1H?1E").
  Proof. exact (proj1 parse_family). Qed.

  (* [comment removed for export] *)

  Lemma jparse_all : ltac2:(zQ "10!hhc@3$0?5HCEIL?1H?1E").
  Proof. exact (jparse_spec H E HH TABS parse_value_all). Qed.

  Theorem llvm_fuzz_all : ltac2:(zQ "10!hm9@3$0?5HCEIL?1H?1E").
  Proof. exact (llvm_fuzz_spec H E HH TABS jparse_all (dtor_value_spec H E HH)). Qed.
End W.
(* [comment removed for export] *)
