(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import RunConst.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AMalloc_iface AH_huf_iface AF_huf_dec_iface AF_huf_adisp AF_huf_ax1e AF_huf_ax2h.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_dec1xA () := "I59OSSVerify5KrLib5AsanW=AMalloc_iface<AMallocIface00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW;AF_huf_ax1e>dec_1x1_proofAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW;AF_huf_ax2h>dec_1x2_proofAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<AF_huf_adisp@huf_dec_1x_dispAC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW5ABase7alayout00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~".
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Theorem huf_dec_1x_closedA : forall (AI : AMallocIface) (rng_fs : alayout -> footprint -> Prop),
  huf_dec_stmtA AI rng_fs huf_dt_okA AHUF_DEC_1X.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_dec1xA ()) ["CANSEC1"] "h02AIh16rng_fsp;1p;3p;5g0000j13Tg0017j32Tg002<j30Tg003Aj51Tp,2rcR0#3g004Ig005Cp-0[[P0f1R1f0R2A2012A0012D1W1W0o"). Qed.
End CANSEC1.
