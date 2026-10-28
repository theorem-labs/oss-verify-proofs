(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import MallocLayout RefStmts.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require RRef_calloc.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2MallocLayout V2Reloc V2RelocCode V2RelocSites V2RelocML.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2Ref_calloc () := "C6ARocqVerifyHarness?AgentSubmission6Common8Mallocng;RelocLayout<reloc_layoutC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng8RefStmts;calloc_stmtC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng;RRef_calloc>calloc_refinesC47Corelib4Init5Logic8eq_ind_rI6ARocqVerifyHarness?AgentSubmission6Common8Mallocng<MallocLayout<MallocLayout00C5ARocqVerifyHarness?AgentSubmission2V27V2Reloc8v2_relocC5ARocqVerifyHarness?AgentSubmission2V2;V2RelocCode7v2_codeC5ARocqVerifyHarness?AgentSubmission2V2<V2RelocSites8v2_sitesC5ARocqVerifyHarness?AgentSubmission2V2>V2MallocLayout4LU16C5ARocqVerifyHarness?AgentSubmission2V29V2RelocML9lv2_reloc".

Section Calloc.
Context {fx : FPState}.

Theorem calloc_refines : calloc_stmt.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Ref_calloc ()) ["Calloc"] "h01mp;1p;2p;4p;6g0000j13Tg001=j22Tg002Fj40Tg003Uj61Tg0043R0g005CR1#3p,2fxR2f0'2X00P2P1g006;g0076C0g0083g008nE1o"). Qed.
End Calloc.
