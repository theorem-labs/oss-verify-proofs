(* The unit's tops, as libreac/fuzz_decode's released lib/Theorems.v and libdiginet/fuzz_decode's: plain_halts
   (Prog/T/SlotFrame.v plain_halts_of_walk), ubsan_halts (U/Prog/T/SlotFrame.v ubsan_halts_of_walk) and ubsan_agrees
   (Prog/T/SlotAgreeFrame.v ubsan_agrees_of_walks), each from the walk contracts of LLVMFuzzerTestOneInput that
   Prog/T/WalkAll.v and U/Prog/T/WalkAll.v assemble, given the walks of LLVMFuzzerTestOneInput itself
   (Prog/T/LLVMFuzzerTestOneInput_walk.v; U/Prog/T/LLVMFuzzerTestOneInput.v, SR and cut-free forms).
   The plain side of the ASan agreements is lib/A/TransportPlainRz.v transport_plain_rz applied to plain_walk, on
   the ASan side (this file Requires nothing of lib/A, so a plain / UBSan release drops lib/A whole). *)
From OSSVerify.libdiginet.fuzz_transport Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require WalkAll SlotFrame SlotAgreeFrame
  LLVMFuzzerTestOneInput_walk.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require WalkAll SlotFrame LLVMFuzzerTestOneInput.

Module PW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.WalkAll.
Module PF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.SlotFrame.
Module PA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.SlotAgreeFrame.
Module PL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.LLVMFuzzerTestOneInput_walk.
Module UW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T.WalkAll.
Module UF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T.SlotFrame.
Module UL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T.LLVMFuzzerTestOneInput.

Definition ubsan_walk : UW.llvm_walk_at_frame :=
  UW.llvm_walk_all UL.LLVMFuzzerTestOneInput_holds.

Definition ubsan_walk_cf : UW.llvm_walk_cf_at_frame :=
  UW.llvm_walk_all_cf UL.LLVMFuzzerTestOneInput_holds_cf.

Definition libdiginet_fuzz_transport_ubsan_halts : Statements.ubsan_halts :=
  UF.ubsan_halts_of_walk ubsan_walk.

Definition plain_walk : PW.llvm_walk_at_frame :=
  PW.llvm_walk_all PL.LLVMFuzzerTestOneInput_walk_holds.

Definition libdiginet_fuzz_transport_plain_halts : Statements.plain_halts :=
  PF.plain_halts_of_walk plain_walk.

Definition libdiginet_fuzz_transport_ubsan_agrees : Statements.ubsan_agrees :=
  PA.ubsan_agrees_of_walks plain_walk ubsan_walk_cf.

