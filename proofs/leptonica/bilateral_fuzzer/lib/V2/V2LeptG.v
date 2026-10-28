(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import AllocIface.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptDefs.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica.VL Require LeptBase.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2Reloc V2RelocVL V2LeptBase.

Lemma v2_LL : LLU16 = @LeptBase.LLG v2_reloc v2_lept.
Proof. reflexivity. Qed.

Definition v2_pinsG {AL : AllocLayout} {CL : CallocLayout} (PP : @V2Pins AL CL) : @LeptBase.PinsG v2_reloc AL CL :=
  @LeptBase.Build_PinsG v2_reloc AL CL (@p16_segs AL CL PP) (@p16_malloc AL CL PP) (@p16_free AL CL PP) (@p16_calloc AL CL PP) (@p16_tp AL CL PP).
