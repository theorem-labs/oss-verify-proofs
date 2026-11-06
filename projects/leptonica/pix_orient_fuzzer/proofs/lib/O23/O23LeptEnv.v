(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require PFSpec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica.OL Require Import LeptStderr.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23Reloc.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23LeptEnv () := "K47Corelib4Init5Logic2eq01C79OSSVerify5KrLib6Common9Leptonica2OL:LeptStderr2LGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl6PFSpec6ls_ok1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib3O238O23Reloc9o23_relocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl6PFSpec6ls_ok2C1?~~~~~~~~~~~~~~~".

Lemma o23_lenv_ok1 : @PFSpec.ls_ok1 o23_reloc (@LG o23_reloc) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O23LeptEnv ()) [] "p;2p;1p;3g0000j23Tg000Jj12Tg001Pj20Tg002Nj31Tg002hR0g003HR1'3g003hR2%22'0=101do"). Qed.
Lemma o23_lenv_ok2 : @PFSpec.ls_ok2 o23_reloc (@LG o23_reloc) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O23LeptEnv ()) [] "p;2p;1p;3g0000j23Tg000Jj12Tg004cj20Tg002Nj31Tg002hR0g003HR1'3g003hR2%22'0=101do"). Qed.
Definition o23_lenv_ol : RelocLeptEnvOL o23_reloc := {| rl_lenv_ok1 := o23_lenv_ok1; rl_lenv_ok2 := o23_lenv_ok2 |}.
