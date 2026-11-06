(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import RunConst.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AMalloc_iface AH_huf_iface AF_huf_dec_iface AF_huf_adisp AF_huf_w4sf AF_huf_dec4x2c.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_dec4xA () := "I59OSSVerify5KrLib5AsanW=AMalloc_iface<AMallocIface00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW;AF_huf_w4sf?dec_4x1_closedAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW>AF_huf_dec4x2c?dec_4x2_closedAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<AF_huf_adisp@huf_dec_4x_dispAC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW5ABase7alayout00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~".
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.

Theorem huf_dec_4x_closedA : forall (AI : AMallocIface) (rng_fs : alayout -> footprint -> Prop),
  huf_dec_stmtA AI rng_fs huf_dt_okA AHUF_DEC_4X.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_dec4xA ()) ["CANSEC1"] "h02AIh16rng_fsp;1p;3p;5g0000j13Tg0017j32Tg002=j30Tg003Fj51Tp,2rcR0#3g004Ng005Hp-0[[P0f1R1f0R2A2012A0012D1W1W0o"). Qed.

End CANSEC1.
