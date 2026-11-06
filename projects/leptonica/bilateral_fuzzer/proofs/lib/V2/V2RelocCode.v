(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc RelocCode CanonCode.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2Reloc.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2RelocCode () := "K47Corelib4Init5Logic2eq01C69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc9RelocCode:code_checkC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib2V27V2Reloc8v2_relocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc9CanonCode:canon_codeC1?~~~~~~~~~~~~~~~".

Lemma v2_code_ok : code_check (@rl_segs v2_reloc) (@rl_delta v2_reloc) canon_code = true.
Proof.
ltac2:(KReplay.run1 (kr_t_V2RelocCode ()) [] "p;2p;1p;3g0000j24Tg000Jj13Tg001Ij10Tg002Ij31Tg003Oj32Tg003iR0g004IR1'4g004iR2#3%02g005a31=201do"). Qed.

Definition v2_code : RelocCode v2_reloc := {| rl_code_ok := v2_code_ok |}.
