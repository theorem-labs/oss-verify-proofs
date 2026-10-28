(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_fa_iface AF_huf_z4s_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s3_iface AF_huf_dec4x2 AF_huf_z4sf.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AF_huf_z4s1 AF_huf_z4s2 AF_huf_z4s31 AF_huf_z4s32b AF_huf_z4s33b AF_huf_z4s34b AF_huf_afa6 AF_huf_z4send.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

Theorem dec_4x2_closedA : forall (AI : AMallocIface) (rng_fs : alayout -> footprint -> Prop),
  dec4_int_stmtA AI rng_fs x2_tabA AHUF_DX2_4X.
Proof.
  intros AI rng_fs.
  exact (dec_4x2_proofA AI rng_fs
           (z4d_proofA AF_huf_z4s1.z4s1_top
              (AF_huf_z4s2.z4s2_proof AF_huf_z4s31.z4s31_proof AF_huf_z4s32b.z4s32_proof AF_huf_z4s33b.z4s33_proof
                 AF_huf_z4s34b.z4s34_proof AF_huf_z4send.z4end_proof))
           AF_huf_afa6.fast_args_proofA).
Qed.

End CANSEC1.
