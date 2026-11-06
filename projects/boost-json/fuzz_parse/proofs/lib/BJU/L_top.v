(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep TacX ZBridge Exec CellsX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs RMalloc_iface_stmt BJFrame HeapMF_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJU Require Import BJRep BJHeap BJIface BJIfaceStr BJIfaceEsc BJIfaceTop BJIfaceLL BJEhTabs BJHeapFloor BJChainAbove.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJU Require Import
     L_parse_value L_parse_array L_parse_object
     L_lit_null L_lit_true L_lit_false L_unum0 L_unumneg L_numpos
     W_dtor_value2 L_pdoc L_wsome L_write L_jparse L_fuzz L_llvm
     L_pobj_all L_upstr L_pkey L_upesc.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJUaBJIfaceEsc~~~~~~0h2parse_escaped_stmt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU7BJIface~~~~~~l6eparse_key_stmtl6h1parse_string_stmtl6h0push_object_stmt37Corelib4Init5Logicse3andl6h0parse_array_stmtl6h1parse_object_stmtl6h0parse_value_stmt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJUaBJIfaceTop~~~~~~hi5bjparse_stmt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU9BJIfaceLL~~~~~~hn5fllvm_fuzz_stmt279OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUcHeapMF_iface~~~~~~hs83hmfhs83ehkhs8cheap_mf_hyps79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU8BJEhTabs~~~~~~iia9bj_ehtabs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJUbBJHeapFloor~~~~~~in6aheap_floor79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJUcBJChainAbove~~~~~~is6eeh_chain_above" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!igc$0").
  Variable E : ltac2:(zQ "10!ih3$0").
  Hypothesis HH : ltac2:(zQ "10!iha@3$0?5HCEIL?1H?1E").
  Hypothesis TABS : ltac2:(zQ "10!im9@1$0?1E").
  Hypothesis HFL : ltac2:(zQ "10!ir8@1$0?1H").
  Hypothesis HCA : ltac2:(zQ "10!jg9@1$0?1E").

  (* [comment removed for export] *)
  Lemma PESC : ltac2:(zQ "10!k1@3$0?5HCEIL?1H?1E").      (* [comment removed for export] *)
  Proof. exact (parse_escaped_spec H E HH TABS). Qed.

  (* [comment removed for export] *)
  Lemma PK : ltac2:(zQ "10!p4@3$0?5HCEIL?1H?1E").           (* [comment removed for export] *)
  Proof. exact (parse_key_spec H E HH TABS HFL HCA PESC). Qed.
  Lemma ps_all : ltac2:(zQ "10!q5@3$0?5HCEIL?1H?1E").     (* [comment removed for export] *)
  Proof. exact (parse_string_spec H E HH TABS HFL HCA PESC). Qed.
  Lemma pobj_all : ltac2:(zQ "10!ra@3$0?5HCEIL?1H?1E").
  Proof. exact (push_object_spec_closed H E HH HFL TABS). Qed.

  (* [comment removed for export] *)
  Lemma parse_family : ltac2:(zQ "40!u2!u8!vc!hh1@2$0@3$3?5HCEIL?1H?1E@2$0@3$1?5HCEIL?1H?1E@3$2?5HCEIL?1H?1E").
  Proof.
    apply (parse_family_by_depth H E).
    - intros d PV. exact (PA_STEP H E HH TABS HFL d PV).
    - intros d PV. exact (PO_STEP H E HH TABS PK pobj_all d PV).
    - intros d PA PO. exact (PV_STEP H E HH TABS d PA PO ps_all (parse_unum0_spec H E HH TABS) (parse_unumneg_spec H E HH TABS) (parse_numpos_spec H E HH TABS)
                               (parse_null_spec H E HH TABS HFL) (parse_true_spec H E HH TABS HFL) (parse_false_spec H E HH TABS HFL)).
  Qed.

  Lemma parse_value_all : ltac2:(zQ "10!hh1@3$0?5HCEIL?1H?1E").
  Proof. exact (proj1 parse_family). Qed.

  (* [comment removed for export] *)

  Lemma jparse_all : ltac2:(zQ "10!hm6@3$0?5HCEIL?1H?1E").
  Proof. exact (jparse_spec H E HH TABS HFL parse_value_all). Qed.

  Theorem llvm_fuzz_all : ltac2:(zQ "10!hr5@3$0?5HCEIL?1H?1E").
  Proof. exact (llvm_fuzz_spec H E HH TABS jparse_all (dtor_value_spec H E HH HFL)). Qed.
End W.
(* [comment removed for export] *)
