(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import MallocLayout RefStmts.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require RRef_free.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2MallocLayout V2Reloc V2RelocCode V2RelocSites V2RelocML.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2Ref_free () := "C69OSSVerify5KrLib6Common8Mallocng;RelocLayout<reloc_layoutC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng8RefStmts9free_stmtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9RRef_free<free_refinesC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rI69OSSVerify5KrLib6Common8Mallocng<MallocLayout<MallocLayout00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V27V2Reloc8v2_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2RelocCode7v2_codeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2<V2RelocSites8v2_sitesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2>V2MallocLayout4LU16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V29V2RelocML9lv2_relocC1?~~~~~~~~~~~~~~~".

Section Free.
Context {fx : FPState}.

Theorem free_refines : free_stmt.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Ref_free ()) ["Free"] "h01mp;1p;2p;4p;6g0000j13Tg001=j22Tg002Dj40Tg003Oj61Tg003mR0g005=R1#3p,2fxR2f0'2X00P2P1g0065g0070C0g007mg008hE1o"). Qed.
End Free.
