(* Case 4 of the ubsan LLVMFuzzerTestOneInput, the tagged path (op_submit's g_raw == 0 arm,
   fuzz/fuzz_transport.c:1085-1121): from 0x141a4 (LLVMFuzzerTestOneInput_op4_mid.v llvm_op4_mid) to the latch
   0x14574, against op4_tagged_m. The stretches 0x141a4 .. 0x143f0 are _op4_tag_a1 / _a / _b / _c / _d.v, composed in
   _op4_tag_f.v; the record, g_ncmd++ and settle(0) from 0x143f0 are _op4_tag_recp.v's t4r_rec_holds. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memset_c memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import
  diginet_session_submit_c check_refusal_submit_c check_latest_submit_c settle_c
  LLVMFuzzerTestOneInput_op4_mid LLVMFuzzerTestOneInput_op4_tag_f LLVMFuzzerTestOneInput_op4_tag_recp.

Theorem llvm_op4_tag_holds : memset_contract -> memcpy_contract -> diginet_session_submit_contract ->
  check_refusal_submit_contract -> check_latest_submit_contract -> settle_contract -> llvm_op4_tag_stmt.
Proof.
  intros MSET MCPY SUB CRS CLS STL.
  exact (t4_front MSET MCPY SUB CRS CLS (t4r_rec_holds MCPY STL)).
Qed.
