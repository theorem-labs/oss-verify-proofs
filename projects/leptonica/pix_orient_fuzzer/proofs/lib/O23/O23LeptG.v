(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import AllocIface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptDefs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica.OL Require LeptBase.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23Reloc O23RelocOL O23LeptBase.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23LeptG () := "C79OSSVerify5KrLib6Common9Leptonica2OL8LeptBase3LLGC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01I69OSSVerify5KrLib6Common9Leptonica8LeptDefs:LeptLayout00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O238O23Reloc9o23_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23:O23RelocOL8o23_leptC1?~~~~~~~~~~~~~~~".

Lemma o23_LL : LL16 = @LeptBase.LLG o23_reloc o23_lept.
Proof.
ltac2:(KReplay.run1 (kr_t_O23LeptG ()) [] "p;2g0000j21Tg0015j20Tg001Og002Zg003U'1'0o"). Qed.

Definition o23_pinsG {AL : AllocLayout} {CL : CallocLayout} (PP : @O23Pins AL CL) : @LeptBase.PinsG o23_reloc AL CL :=
  @LeptBase.Build_PinsG o23_reloc AL CL (@p16_segs AL CL PP) (@p16_malloc AL CL PP) (@p16_free AL CL PP) (@p16_calloc AL CL PP) (@p16_tp AL CL PP).
