(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_d0220 : bv 32 := 0xff010113.

Definition W_d0224 : bv 32 := 0x00113423.

Definition W_d0228 : bv 32 := 0x00050e63.

Definition W_d022c : bv 32 := 0x00050593.

Definition W_d0230 : bv 32 := 0x0001d517.

Definition W_d0234 : bv 32 := 0xe5453503.

Definition W_d0238 : bv 32 := 0x00800613.

Definition W_d023c : bv 32 := 0x3d5100ef.

Definition W_d0240 : bv 32 := 0x01c0006f.

Definition W_d025c : bv 32 := 0x0001d517.

Definition W_d0260 : bv 32 := 0xe2853503.

Definition W_d0264 : bv 32 := 0x000500a3.

Definition W_d0268 : bv 32 := 0x00053503.

Definition W_d026c : bv 32 := 0x00020593.

Definition W_d0270 : bv 32 := 0xfea5b823.

Definition W_d0274 : bv 32 := 0x00813083.

Definition W_d0278 : bv 32 := 0x01010113.

Definition W_d027c : bv 32 := 0x00008067.

Definition W_d0288 : bv 32 := 0xfffff5b7.
Lemma F_d0288 : fetch_word Plain.M.loaded_segments (0xd02bc : word) = Some W_d0288.
Proof. vm_refl. Qed.
Lemma D_d0288 : decode_any W_d0288 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_d028c : bv 32 := 0x0015859b.
Lemma F_d028c : fetch_word Plain.M.loaded_segments (0xd02c0 : word) = Some W_d028c.
Proof. vm_refl. Qed.
Lemma D_d028c : decode_any W_d028c = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0290 : bv 32 := 0x02b56663.
Lemma F_d0290 : fetch_word Plain.M.loaded_segments (0xd02c4 : word) = Some W_d0290.
Proof. vm_refl. Qed.
Lemma D_d0290 : decode_any W_d0290 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_d02bc : bv 32 := 0x00008067.
Lemma F_d02bc : fetch_word Plain.M.loaded_segments (0xd02f0 : word) = Some W_d02bc.
Proof. vm_refl. Qed.
Lemma D_d02bc : decode_any W_d02bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
