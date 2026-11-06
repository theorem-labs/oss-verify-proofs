(* LLVMFuzzerTestOneInput_agree.v ubsan_agrees_of_llvm with the plain slot premise from FrameClose.v
   slot_sr_all_of_build and the crash-free UBSan one from U/Prog/FrameCloseU.v slot_sr_cf_all_of_build;
   ubsan_agrees_holds puts in the walks of diginet_frame_build (diginet_frame_build.v and
   U/Prog/diginet_frame_build.v). *)
From OSSVerify.libdiginet.fuzz_frame Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog Require diginet_frame_build_c diginet_frame_build FrameClose
  LLVMFuzzerTestOneInput_agree.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require diginet_frame_build_c diginet_frame_build
  FrameCloseU.

Module PB := OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog.diginet_frame_build_c.
Module PW := OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog.diginet_frame_build.
Module PC := OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog.FrameClose.
Module AG := OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog.LLVMFuzzerTestOneInput_agree.
Module UB := OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog.diginet_frame_build_c.
Module UW := OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog.diginet_frame_build.
Module UC := OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog.FrameCloseU.

Theorem ubsan_agrees_of_builds :
  PB.diginet_frame_build_contract -> UB.diginet_frame_build_contract -> Statements.ubsan_agrees.
Proof.
  intros PBUILD UBUILD.
  exact (AG.ubsan_agrees_of_llvm (PC.slot_sr_all_of_build PBUILD) (UC.slot_sr_cf_all_of_build UBUILD)).
Qed.

Theorem ubsan_agrees_holds : Statements.ubsan_agrees.
Proof.
  exact (ubsan_agrees_of_builds (PC.frame_build_of_walks PW.diginet_frame_build_holds)
    (UC.frame_build_of_walks UW.diginet_frame_build_holds)).
Qed.
