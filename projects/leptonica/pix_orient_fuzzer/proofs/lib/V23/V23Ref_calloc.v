(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import MallocLayout RefStmts.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require RRef_calloc.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23MallocLayout V23Reloc V23RelocCode V23RelocSites V23RelocML.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_V23Ref_calloc () := "C69OSSVerify5KrLib6Common8Mallocng;RelocLayout<reloc_layoutC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng8RefStmts;calloc_stmtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng;RRef_calloc>calloc_refinesC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rI69OSSVerify5KrLib6Common8Mallocng<MallocLayout<MallocLayout00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V238V23Reloc9v23_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23RelocCode8v23_codeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23=V23RelocSites9v23_sitesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23?V23MallocLayout4LU16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23:V23RelocML:lv23_relocC1?~~~~~~~~~~~~~~~".

Section Calloc.
Context {fx : FPState}.

Theorem calloc_refines : calloc_stmt.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Ref_calloc ()) ["Calloc"] "h01mp;1p;2p;4p;6g0000j13Tg001=j22Tg002Fj40Tg003Uj61Tg0043R0g005CR1#3p,2fxR2f0'2X00P2P1g006>g007<C0g008<g0099E1o"). Qed.
End Calloc.
