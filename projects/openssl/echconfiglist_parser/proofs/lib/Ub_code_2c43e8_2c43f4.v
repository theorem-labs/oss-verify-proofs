(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_2c43e8 : bv 32 := 0x00050213.
Lemma F_2c43e8 : fetch_word Ubsan.M.loaded_segments (0x2c4424 : word) = Some W_2c43e8.
Proof. vm_refl. Qed.
Lemma D_2c43e8 : decode_any W_2c43e8 = Some (OpImm ALU_ADD 4 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c43ec : bv 32 := 0x00000513.
Lemma F_2c43ec : fetch_word Ubsan.M.loaded_segments (0x2c4428 : word) = Some W_2c43ec.
Proof. vm_refl. Qed.
Lemma D_2c43ec : decode_any W_2c43ec = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c43f0 : bv 32 := 0x00008067.
Lemma F_2c43f0 : fetch_word Ubsan.M.loaded_segments (0x2c442c : word) = Some W_2c43f0.
Proof. vm_refl. Qed.
Lemma D_2c43f0 : decode_any W_2c43f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
