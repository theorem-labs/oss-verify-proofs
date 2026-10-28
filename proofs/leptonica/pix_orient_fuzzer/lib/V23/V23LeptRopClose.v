From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRop2Arith.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptRopClip.
Import ListNotations.
Open Scope bv_scope.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptRop_iface V23LeptRop2Segs V23LeptRopGSpec.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptRopOp2W V23LeptRopOp3W V23LeptRopOp8W V23LeptRopOrW V23LeptRopLowC V23LeptRop2WC.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptRopPre V23LeptRopPre12 V23LeptRopGenPre V23LeptRop2W.

Section RopClose.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.

Theorem rasteropLow_wa2_clip_closed : rasteropLow_wa2_clip_contract.
Proof. exact (rasteropLow_wa2_clip_W rl_pre_W rl_empty_W). Qed.

Theorem rasteropLow_wa3_clip_closed : rasteropLow_wa3_clip_contract.
Proof. exact (rasteropLow_wa3_clip_W rl_pre_W rl_empty_W). Qed.

Theorem rasteropLow_wa8_clip_closed : rasteropLow_wa8_clip_contract.
Proof. exact (rasteropLow_wa8_clip_W rl_pre_W rl_empty_W). Qed.

Theorem rasteropLow_wa14_clip_closed : rasteropLow_wa14_clip_contract.
Proof. exact (rasteropLow_wa14_clip_W rl_pre_W rl_empty_W). Qed.

Theorem rasteropLow_wa_clip_closed : rasteropLow_wa_clip_contract.
Proof. exact (rasteropLow_wa_clip_W rl_pre_W rl_empty_W rl12_W). Qed.

Theorem rasteropLow_gen_clip_closed : rasteropLow_gen_clip_contract.
Proof. exact (rasteropLow_gen_clip_W rg_gen_pre_W rg_loops12_W). Qed.

End RopClose.
