(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import MallocLayout RefStmts.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require RRef_malloc.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23MallocLayout V23Reloc V23RelocCode V23RelocSites V23RelocML.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_V23Ref_malloc () := "C6ARocqVerifyHarness?AgentSubmission6Common8Mallocng;RelocLayout<reloc_layoutC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng8RefStmts;malloc_stmtC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng;RRef_malloc>malloc_refinesC47Corelib4Init5Logic8eq_ind_rI6ARocqVerifyHarness?AgentSubmission6Common8Mallocng<MallocLayout<MallocLayout00C5ARocqVerifyHarness?AgentSubmission3V238V23Reloc9v23_relocC5ARocqVerifyHarness?AgentSubmission3V23<V23RelocCode8v23_codeC5ARocqVerifyHarness?AgentSubmission3V23=V23RelocSites9v23_sitesC5ARocqVerifyHarness?AgentSubmission3V23?V23MallocLayout4LU16C5ARocqVerifyHarness?AgentSubmission3V23:V23RelocML:lv23_reloc".

Section Malloc.
Context {fx : FPState}.

Theorem malloc_refines : malloc_stmt.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Ref_malloc ()) ["Malloc"] "h01mp;1p;2p;4p;6g0000j13Tg001=j22Tg002Fj40Tg003Uj61Tg0043R0g005CR1#3p,2fxR2f0'2X00P2P1g006>g007<C0g008<g0099E1o"). Qed.
End Malloc.
