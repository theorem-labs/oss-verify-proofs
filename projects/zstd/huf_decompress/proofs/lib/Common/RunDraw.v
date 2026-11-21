(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (2 recorded proofs replaced by written proofs (atop_range, sec_range)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require Export StackLayout.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Export RunConst.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RunDraw () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib3Lib8RunConst7ATOP_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst7ATOP_hiC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01I59OSSVerify5KrLib3Lib8RunConst9runConstT00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib3Lib8RunConst:SECRET_rngC1?~~~~~~~~~~~~~~~".
Open Scope Z_scope.

Lemma atop_range {rc : runConstT} : 0x7fff7f800000 <= ATOP <= 0x7FFFFF800000.
Proof. split; [apply ATOP_lo | apply ATOP_hi]. Qed.
Lemma sec_range {rc : runConstT} : 0 <= SECRET < 2^64.
Proof. apply SECRET_rng. Qed.

(* [comment removed for export] *)
Ltac atop_facts :=
  lazymatch goal with
  | _ : 0x7fff7f800000 <= @ATOP _ <= 0x7FFFFF800000 |- _ => idtac
  | |- context [@ATOP _] => pose proof atop_range
  | _ : context [@ATOP _] |- _ => pose proof atop_range
  | _ => idtac
  end.
Ltac sec_facts :=
  lazymatch goal with
  | _ : 0 <= @SECRET _ < 2^64 |- _ => idtac
  | _ => pose proof sec_range
  end.

(* [comment removed for export] *)
Ltac lia := atop_facts; Stdlib.micromega.Lia.lia.
Ltac nia := atop_facts; Stdlib.micromega.Lia.nia.
