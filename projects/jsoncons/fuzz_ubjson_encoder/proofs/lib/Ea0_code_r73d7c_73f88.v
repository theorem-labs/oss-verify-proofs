(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_8e95c : bv 32 := 0xef010113.
Lemma F_8e95c : fetch_word Asan.M.loaded_segments (0x8e9ac : word) = Some W_8e95c.
Proof. vm_refl. Qed.
Lemma D_8e95c : decode_any W_8e95c = Some (OpImm ALU_ADD 2 2 3824, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e960 : bv 32 := 0x10113423.
Lemma F_8e960 : fetch_word Asan.M.loaded_segments (0x8e9b0 : word) = Some W_8e960.
Proof. vm_refl. Qed.
Lemma D_8e960 : decode_any W_8e960 = Some (Store SZ8 2 1 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e964 : bv 32 := 0x10813023.
Lemma F_8e964 : fetch_word Asan.M.loaded_segments (0x8e9b4 : word) = Some W_8e964.
Proof. vm_refl. Qed.
Lemma D_8e964 : decode_any W_8e964 = Some (Store SZ8 2 8 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e968 : bv 32 := 0x0e913c23.
Lemma F_8e968 : fetch_word Asan.M.loaded_segments (0x8e9b8 : word) = Some W_8e968.
Proof. vm_refl. Qed.
Lemma D_8e968 : decode_any W_8e968 = Some (Store SZ8 2 9 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e96c : bv 32 := 0x0f213823.
Lemma F_8e96c : fetch_word Asan.M.loaded_segments (0x8e9bc : word) = Some W_8e96c.
Proof. vm_refl. Qed.
Lemma D_8e96c : decode_any W_8e96c = Some (Store SZ8 2 18 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e970 : bv 32 := 0x0f313423.
Lemma F_8e970 : fetch_word Asan.M.loaded_segments (0x8e9c0 : word) = Some W_8e970.
Proof. vm_refl. Qed.
Lemma D_8e970 : decode_any W_8e970 = Some (Store SZ8 2 19 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e974 : bv 32 := 0x0f413023.
Lemma F_8e974 : fetch_word Asan.M.loaded_segments (0x8e9c4 : word) = Some W_8e974.
Proof. vm_refl. Qed.
Lemma D_8e974 : decode_any W_8e974 = Some (Store SZ8 2 20 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e978 : bv 32 := 0x0d513c23.
Lemma F_8e978 : fetch_word Asan.M.loaded_segments (0x8e9c8 : word) = Some W_8e978.
Proof. vm_refl. Qed.
Lemma D_8e978 : decode_any W_8e978 = Some (Store SZ8 2 21 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e97c : bv 32 := 0x00050913.
Lemma F_8e97c : fetch_word Asan.M.loaded_segments (0x8e9cc : word) = Some W_8e97c.
Proof. vm_refl. Qed.
Lemma D_8e97c : decode_any W_8e97c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e980 : bv 32 := 0xfff00513.
Lemma F_8e980 : fetch_word Asan.M.loaded_segments (0x8e9d0 : word) = Some W_8e980.
Proof. vm_refl. Qed.
Lemma D_8e980 : decode_any W_8e980 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e984 : bv 32 := 0x12090463.
Lemma F_8e984 : fetch_word Asan.M.loaded_segments (0x8e9d4 : word) = Some W_8e984.
Proof. vm_refl. Qed.
Lemma D_8e984 : decode_any W_8e984 = Some (Branch BC_EQ 18 0 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e988 : bv 32 := 0x00060413.
Lemma F_8e988 : fetch_word Asan.M.loaded_segments (0x8e9d8 : word) = Some W_8e988.
Proof. vm_refl. Qed.
Lemma D_8e988 : decode_any W_8e988 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e98c : bv 32 := 0x000aa617.
Lemma F_8e98c : fetch_word Asan.M.loaded_segments (0x8e9dc : word) = Some W_8e98c.
Proof. vm_refl. Qed.
Lemma D_8e98c : decode_any W_8e98c = Some (Auipc 12 170, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e990 : bv 32 := 0x7cc63603.
Lemma F_8e990 : fetch_word Asan.M.loaded_segments (0x8e9e0 : word) = Some W_8e990.
Proof. vm_refl. Qed.
Lemma D_8e990 : decode_any W_8e990 = Some (Load SZ8 true 12 12 1996, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e994 : bv 32 := 0x10464603.
Lemma F_8e994 : fetch_word Asan.M.loaded_segments (0x8e9e4 : word) = Some W_8e994.
Proof. vm_refl. Qed.
Lemma D_8e994 : decode_any W_8e994 = Some (Load SZ1 false 12 12 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e998 : bv 32 := 0x00167613.
Lemma F_8e998 : fetch_word Asan.M.loaded_segments (0x8e9e8 : word) = Some W_8e998.
Proof. vm_refl. Qed.
Lemma D_8e998 : decode_any W_8e998 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e99c : bv 32 := 0x10060863.
Lemma F_8e99c : fetch_word Asan.M.loaded_segments (0x8e9ec : word) = Some W_8e99c.
Proof. vm_refl. Qed.
Lemma D_8e99c : decode_any W_8e99c = Some (Branch BC_EQ 12 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eaac : bv 32 := 0x0005051b.
Lemma F_8eaac : fetch_word Asan.M.loaded_segments (0x8eafc : word) = Some W_8eaac.
Proof. vm_refl. Qed.
Lemma D_8eaac : decode_any W_8eaac = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eab0 : bv 32 := 0x10813083.
Lemma F_8eab0 : fetch_word Asan.M.loaded_segments (0x8eb00 : word) = Some W_8eab0.
Proof. vm_refl. Qed.
Lemma D_8eab0 : decode_any W_8eab0 = Some (Load SZ8 true 1 2 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eab4 : bv 32 := 0x10013403.
Lemma F_8eab4 : fetch_word Asan.M.loaded_segments (0x8eb04 : word) = Some W_8eab4.
Proof. vm_refl. Qed.
Lemma D_8eab4 : decode_any W_8eab4 = Some (Load SZ8 true 8 2 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eab8 : bv 32 := 0x0f813483.
Lemma F_8eab8 : fetch_word Asan.M.loaded_segments (0x8eb08 : word) = Some W_8eab8.
Proof. vm_refl. Qed.
Lemma D_8eab8 : decode_any W_8eab8 = Some (Load SZ8 true 9 2 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eabc : bv 32 := 0x0f013903.
Lemma F_8eabc : fetch_word Asan.M.loaded_segments (0x8eb0c : word) = Some W_8eabc.
Proof. vm_refl. Qed.
Lemma D_8eabc : decode_any W_8eabc = Some (Load SZ8 true 18 2 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eac0 : bv 32 := 0x0e813983.
Lemma F_8eac0 : fetch_word Asan.M.loaded_segments (0x8eb10 : word) = Some W_8eac0.
Proof. vm_refl. Qed.
Lemma D_8eac0 : decode_any W_8eac0 = Some (Load SZ8 true 19 2 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eac4 : bv 32 := 0x0e013a03.
Lemma F_8eac4 : fetch_word Asan.M.loaded_segments (0x8eb14 : word) = Some W_8eac4.
Proof. vm_refl. Qed.
Lemma D_8eac4 : decode_any W_8eac4 = Some (Load SZ8 true 20 2 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eac8 : bv 32 := 0x0d813a83.
Lemma F_8eac8 : fetch_word Asan.M.loaded_segments (0x8eb18 : word) = Some W_8eac8.
Proof. vm_refl. Qed.
Lemma D_8eac8 : decode_any W_8eac8 = Some (Load SZ8 true 21 2 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eacc : bv 32 := 0x11010113.
Lemma F_8eacc : fetch_word Asan.M.loaded_segments (0x8eb1c : word) = Some W_8eacc.
Proof. vm_refl. Qed.
Lemma D_8eacc : decode_any W_8eacc = Some (OpImm ALU_ADD 2 2 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ead0 : bv 32 := 0x00008067.
Lemma F_8ead0 : fetch_word Asan.M.loaded_segments (0x8eb20 : word) = Some W_8ead0.
Proof. vm_refl. Qed.
Lemma D_8ead0 : decode_any W_8ead0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
