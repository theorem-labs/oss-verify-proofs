From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog Require FrameClose FrameAgreeClose.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require FrameCloseU.

Definition libdiginet_fuzz_frame_plain_halts :=
  OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog.FrameClose.plain_halts_holds.
Definition libdiginet_fuzz_frame_ubsan_halts :=
  OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog.FrameCloseU.ubsan_halts_holds.
Definition libdiginet_fuzz_frame_ubsan_agrees :=
  OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog.FrameAgreeClose.ubsan_agrees_holds.
