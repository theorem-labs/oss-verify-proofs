(* Case 4 of the ubsan LLVMFuzzerTestOneInput (0x13a48, op_submit inlined, fuzz_transport.c:1068-1122), from the case
   entry to the latch 0x14574: llvm_op4_of_tag (_op4_comp.v: the prefix and the raw arm) with the tagged arm
   llvm_op4_tag_holds (_op4_tag.v). *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memset_c memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import
  diginet_session_submit_c check_refusal_submit_c check_latest_submit_c settle_c
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_op4_comp LLVMFuzzerTestOneInput_op4_tag.
Open Scope Z_scope.

Theorem llvm_op4_holds : memset_contract -> memcpy_contract -> diginet_session_submit_contract -> check_refusal_submit_contract -> check_latest_submit_contract -> settle_contract -> llvm_op_stmt 4.
Proof.
  intros MSC MCP SUB CRS CLS STL.
  exact (llvm_op4_of_tag MSC MCP SUB CRS STL (llvm_op4_tag_holds MSC MCP SUB CRS CLS STL)).
Qed.
