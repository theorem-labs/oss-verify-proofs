(* Short-path names for Common/AllocRefusal.v's definitions. KReplay tables address constants by absolute path at a
   fixed character offset, so a reference to one of the allocation edition's helpers (formerly under
   LinuxProcessSemantics.LinuxProcessSem.Sys.Mm) is pointed here in place when AllocRefusal's own path is longer. *)
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require AllocRefusal.

Definition vm_gap_available := @AllocRefusal.vm_gap_available.
Definition vm_gap_available_iff := @AllocRefusal.vm_gap_available_iff.
