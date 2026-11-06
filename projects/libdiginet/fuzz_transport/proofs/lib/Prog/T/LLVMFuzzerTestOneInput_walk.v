(* The walk of LLVMFuzzerTestOneInput in the plain image, closed: WalkAll.v's LLVMFuzzerTestOneInput_walk
   (the walk contract at the frame's allocator and sink words, from the contracts of its callees) as a lemma with
   no hypothesis. LLVMFuzzerTestOneInput_glue.v proves it from three pieces, and this file gives it the three:

     llvm_op2_sr            case 2 of the op loop (op_announce, build_and_receive)   _op2.v
     llvm_op4               case 4 of the op loop (op_submit, inlined)               _op4.v
     llvm_entry_stmt_holds  the entry, 0x13664 to the loop head or the early return  _entry.v

   Everything else the walk needs is proved in the files those import: the four program-point predicates and
   the memory invariant (_lh.v), the switch (_disp.v), the latch (_lat.v), the loop at the evt and SR layers
   (_loop.v, _loopsr.v, _lift.v), the SR seam (_sr.v), the memory transports (_fr.v), the epilogue (_exit.v),
   and cases 0, 1, 3, 5, 6, 7, 8 (_op08.v, _op1.v, _op3.v, _op5.v, _op6.v, _op7.v). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require WalkAll
  LLVMFuzzerTestOneInput_glue LLVMFuzzerTestOneInput_op2 LLVMFuzzerTestOneInput_op4 LLVMFuzzerTestOneInput_entry.

Lemma LLVMFuzzerTestOneInput_walk_holds : WalkAll.LLVMFuzzerTestOneInput_walk.
Proof.
  exact (LLVMFuzzerTestOneInput_glue.LLVMFuzzerTestOneInput_holds
           (@LLVMFuzzerTestOneInput_op2.llvm_op2_sr)
           LLVMFuzzerTestOneInput_op4.llvm_op4
           LLVMFuzzerTestOneInput_entry.llvm_entry_stmt_holds).
Qed.
