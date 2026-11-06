(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import MallocLayout RefStmts.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require RRef_calloc.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23MallocLayout O23Reloc O23RelocCode O23RelocSites O23RelocML.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23Ref_calloc () := "C69OSSVerify5KrLib6Common8Mallocng;RelocLayout<reloc_layoutC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng8RefStmts;calloc_stmtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng;RRef_calloc>calloc_refinesC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rI69OSSVerify5KrLib6Common8Mallocng<MallocLayout<MallocLayout00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O238O23Reloc9o23_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23RelocCode8o23_codeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23=O23RelocSites9o23_sitesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23?O23MallocLayout4LS16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23:O23RelocML:lo23_relocC1?~~~~~~~~~~~~~~~".

Section Calloc.
Context {fx : FPState}.

Theorem calloc_refines : calloc_stmt.
Proof.
ltac2:(KReplay.run1 (kr_t_O23Ref_calloc ()) ["Calloc"] "h01mp;1p;2p;4p;6g0000j13Tg001=j22Tg002Fj40Tg003Uj61Tg0043R0g005CR1#3p,2fxR2f0'2X00P2P1g006>g007<C0g008<g0099E1o"). Qed.
End Calloc.
