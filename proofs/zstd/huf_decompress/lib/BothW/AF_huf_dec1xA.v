(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import RunConst.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AMalloc_iface AH_huf_iface AF_huf_dec_iface AF_huf_adisp AF_huf_ax1e AF_huf_ax2h.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_dec1xA () := "I5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface<AMallocIface00C5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax1e>dec_1x1_proofAC5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_ax2h>dec_1x2_proofAC5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_adisp@huf_dec_1x_dispAI5ARocqVerifyHarness?AgentSubmission5BothW5ABase7alayout00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprint".
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Theorem huf_dec_1x_closedA : forall (AI : AMallocIface) (rng_fs : alayout -> footprint -> Prop),
  huf_dec_stmtA AI rng_fs huf_dt_okA AHUF_DEC_1X.
Proof.
  intros AI rng_fs. exact (huf_dec_1x_dispA AI rng_fs (dec_1x1_proofA AI rng_fs) (dec_1x2_proofA AI rng_fs)).
Qed.
End CANSEC1.
