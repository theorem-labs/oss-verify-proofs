(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import StartupTac RefMemcpyLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica.OL Require MaxIndex.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23Reloc O23RelocCode O23RelocSites O23RelocImg O23RelocOL.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23MaxIndex () := "C79OSSVerify5KrLib6Common9Leptonica2OL8MaxIndexAmaxindex_contractC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP=spec_maxindexC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP<sum_contractC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O238O23Reloc9o23_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23:O23RelocOL;o23_code_olC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23:O23RelocOL<o23_sites_olC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03".
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section VPORT.
Context {fx : FPState}.
Theorem maxindex_contract : SSP.sum_contract SEGS (SSP.spec_maxindex 0x723d0 144).
Proof.
ltac2:(KReplay.run1 (kr_t_O23MaxIndex ()) ["VPORT"] "h03RLTp;4p;1p;2p;3g0000j48Tg001Cj17Tg002Bj10Tg002gj11Tg003Lj12Tg003jj26Tg004jj24Tg005Gj23Tg006Wj35Tp,2fxR0g007fR1g008ag009`C8%71g00:`R2#0#0#1#0#0#0R3#1#1#0#1#1#0#1#0#1#0#0#2%12#0#1#1#0#0#0,61'4%03#2'3750f0b0o"). Qed.

End VPORT.
