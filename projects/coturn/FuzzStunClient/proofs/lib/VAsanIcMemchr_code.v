(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_44248 : bv 32 := 0x7c80106f.
Lemma F_44248 : fetch_word Asan.M.loaded_segments (0x44248 : word) = Some W_44248.
Proof. vm_refl. Qed.
Lemma D_44248 : decode_any W_44248 = Some (Jal 0 6088, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_45a10 : bv 32 := 0x81010113.
Lemma F_45a10 : fetch_word Asan.M.loaded_segments (0x45a10 : word) = Some W_45a10.
Proof. vm_refl. Qed.
Lemma D_45a10 : decode_any W_45a10 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a14 : bv 32 := 0x7e113423.
Lemma F_45a14 : fetch_word Asan.M.loaded_segments (0x45a14 : word) = Some W_45a14.
Proof. vm_refl. Qed.
Lemma D_45a14 : decode_any W_45a14 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a18 : bv 32 := 0x7e813023.
Lemma F_45a18 : fetch_word Asan.M.loaded_segments (0x45a18 : word) = Some W_45a18.
Proof. vm_refl. Qed.
Lemma D_45a18 : decode_any W_45a18 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a1c : bv 32 := 0x7c913c23.
Lemma F_45a1c : fetch_word Asan.M.loaded_segments (0x45a1c : word) = Some W_45a1c.
Proof. vm_refl. Qed.
Lemma D_45a1c : decode_any W_45a1c = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a20 : bv 32 := 0x7d213823.
Lemma F_45a20 : fetch_word Asan.M.loaded_segments (0x45a20 : word) = Some W_45a20.
Proof. vm_refl. Qed.
Lemma D_45a20 : decode_any W_45a20 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a24 : bv 32 := 0x7d313423.
Lemma F_45a24 : fetch_word Asan.M.loaded_segments (0x45a24 : word) = Some W_45a24.
Proof. vm_refl. Qed.
Lemma D_45a24 : decode_any W_45a24 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a28 : bv 32 := 0x7d413023.
Lemma F_45a28 : fetch_word Asan.M.loaded_segments (0x45a28 : word) = Some W_45a28.
Proof. vm_refl. Qed.
Lemma D_45a28 : decode_any W_45a28 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a2c : bv 32 := 0x7b513c23.
Lemma F_45a2c : fetch_word Asan.M.loaded_segments (0x45a2c : word) = Some W_45a2c.
Proof. vm_refl. Qed.
Lemma D_45a2c : decode_any W_45a2c = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a30 : bv 32 := 0x7f010413.
Lemma F_45a30 : fetch_word Asan.M.loaded_segments (0x45a30 : word) = Some W_45a30.
Proof. vm_refl. Qed.
Lemma D_45a30 : decode_any W_45a30 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a34 : bv 32 := 0xfa010113.
Lemma F_45a34 : fetch_word Asan.M.loaded_segments (0x45a34 : word) = Some W_45a34.
Proof. vm_refl. Qed.
Lemma D_45a34 : decode_any W_45a34 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a38 : bv 32 := 0x00060493.
Lemma F_45a38 : fetch_word Asan.M.loaded_segments (0x45a38 : word) = Some W_45a38.
Proof. vm_refl. Qed.
Lemma D_45a38 : decode_any W_45a38 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a3c : bv 32 := 0x00058993.
Lemma F_45a3c : fetch_word Asan.M.loaded_segments (0x45a3c : word) = Some W_45a3c.
Proof. vm_refl. Qed.
Lemma D_45a3c : decode_any W_45a3c = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a40 : bv 32 := 0x00050913.
Lemma F_45a40 : fetch_word Asan.M.loaded_segments (0x45a40 : word) = Some W_45a40.
Proof. vm_refl. Qed.
Lemma D_45a40 : decode_any W_45a40 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a44 : bv 32 := 0x4ec150ef.
Lemma F_45a44 : fetch_word Asan.M.loaded_segments (0x45a44 : word) = Some W_45a44.
Proof. vm_refl. Qed.
Lemma D_45a44 : decode_any W_45a44 = Some (Jal 1 87276, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a48 : bv 32 := 0x0a050663.
Lemma F_45a48 : fetch_word Asan.M.loaded_segments (0x45a48 : word) = Some W_45a48.
Proof. vm_refl. Qed.
Lemma D_45a48 : decode_any W_45a48 = Some (Branch BC_EQ 10 0 172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a4c : bv 32 := 0x3f4160ef.
Lemma F_45a4c : fetch_word Asan.M.loaded_segments (0x45a4c : word) = Some W_45a4c.
Proof. vm_refl. Qed.
Lemma D_45a4c : decode_any W_45a4c = Some (Jal 1 91124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a50 : bv 32 := 0x00067597.
Lemma F_45a50 : fetch_word Asan.M.loaded_segments (0x45a50 : word) = Some W_45a50.
Proof. vm_refl. Qed.
Lemma D_45a50 : decode_any W_45a50 = Some (Auipc 11 103, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a54 : bv 32 := 0x1605b683.
Lemma F_45a54 : fetch_word Asan.M.loaded_segments (0x45a54 : word) = Some W_45a54.
Proof. vm_refl. Qed.
Lemma D_45a54 : decode_any W_45a54 = Some (Load SZ8 true 13 11 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a58 : bv 32 := 0x00050a13.
Lemma F_45a58 : fetch_word Asan.M.loaded_segments (0x45a58 : word) = Some W_45a58.
Proof. vm_refl. Qed.
Lemma D_45a58 : decode_any W_45a58 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a5c : bv 32 := 0x00090513.
Lemma F_45a5c : fetch_word Asan.M.loaded_segments (0x45a5c : word) = Some W_45a5c.
Proof. vm_refl. Qed.
Lemma D_45a5c : decode_any W_45a5c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a60 : bv 32 := 0x00098593.
Lemma F_45a60 : fetch_word Asan.M.loaded_segments (0x45a60 : word) = Some W_45a60.
Proof. vm_refl. Qed.
Lemma D_45a60 : decode_any W_45a60 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a64 : bv 32 := 0x00048613.
Lemma F_45a64 : fetch_word Asan.M.loaded_segments (0x45a64 : word) = Some W_45a64.
Proof. vm_refl. Qed.
Lemma D_45a64 : decode_any W_45a64 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a68 : bv 32 := 0x000680e7.
Lemma F_45a68 : fetch_word Asan.M.loaded_segments (0x45a68 : word) = Some W_45a68.
Proof. vm_refl. Qed.
Lemma D_45a68 : decode_any W_45a68 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a6c : bv 32 := 0x060a0063.
Lemma F_45a6c : fetch_word Asan.M.loaded_segments (0x45a6c : word) = Some W_45a6c.
Proof. vm_refl. Qed.
Lemma D_45a6c : decode_any W_45a6c = Some (Branch BC_EQ 20 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a70 : bv 32 := 0x0a051c63.
Lemma F_45a70 : fetch_word Asan.M.loaded_segments (0x45a70 : word) = Some W_45a70.
Proof. vm_refl. Qed.
Lemma D_45a70 : decode_any W_45a70 = Some (Branch BC_NE 10 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a74 : bv 32 := 0xfff94593.
Lemma F_45a74 : fetch_word Asan.M.loaded_segments (0x45a74 : word) = Some W_45a74.
Proof. vm_refl. Qed.
Lemma D_45a74 : decode_any W_45a74 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a78 : bv 32 := 0x80040a13.
Lemma F_45a78 : fetch_word Asan.M.loaded_segments (0x45a78 : word) = Some W_45a78.
Proof. vm_refl. Qed.
Lemma D_45a78 : decode_any W_45a78 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a7c : bv 32 := 0xfb0a0a13.
Lemma F_45a7c : fetch_word Asan.M.loaded_segments (0x45a7c : word) = Some W_45a7c.
Proof. vm_refl. Qed.
Lemma D_45a7c : decode_any W_45a7c = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a80 : bv 32 := 0x0c95e063.
Lemma F_45a80 : fetch_word Asan.M.loaded_segments (0x45a80 : word) = Some W_45a80.
Proof. vm_refl. Qed.
Lemma D_45a80 : decode_any W_45a80 = Some (Branch BC_LTU 11 9 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a84 : bv 32 := 0xfbf48593.
Lemma F_45a84 : fetch_word Asan.M.loaded_segments (0x45a84 : word) = Some W_45a84.
Proof. vm_refl. Qed.
Lemma D_45a84 : decode_any W_45a84 = Some (OpImm ALU_ADD 11 9 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a88 : bv 32 := 0xfbf00613.
Lemma F_45a88 : fetch_word Asan.M.loaded_segments (0x45a88 : word) = Some W_45a88.
Proof. vm_refl. Qed.
Lemma D_45a88 : decode_any W_45a88 = Some (OpImm ALU_ADD 12 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a8c : bv 32 := 0x12b67663.
Lemma F_45a8c : fetch_word Asan.M.loaded_segments (0x45a8c : word) = Some W_45a8c.
Proof. vm_refl. Qed.
Lemma D_45a8c : decode_any W_45a8c = Some (Branch BC_GEU 12 11 300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a90 : bv 32 := 0x00065597.
Lemma F_45a90 : fetch_word Asan.M.loaded_segments (0x45a90 : word) = Some W_45a90.
Proof. vm_refl. Qed.
Lemma D_45a90 : decode_any W_45a90 = Some (Auipc 11 101, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a94 : bv 32 := 0x3f05b583.
Lemma F_45a94 : fetch_word Asan.M.loaded_segments (0x45a94 : word) = Some W_45a94.
Proof. vm_refl. Qed.
Lemma D_45a94 : decode_any W_45a94 = Some (Load SZ8 true 11 11 1008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a98 : bv 32 := 0x009906b3.
Lemma F_45a98 : fetch_word Asan.M.loaded_segments (0x45a98 : word) = Some W_45a98.
Proof. vm_refl. Qed.
Lemma D_45a98 : decode_any W_45a98 = Some (Op ALU_ADD 13 18 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45a9c : bv 32 := 0x0005b603.
Lemma F_45a9c : fetch_word Asan.M.loaded_segments (0x45a9c : word) = Some W_45a9c.
Proof. vm_refl. Qed.
Lemma D_45a9c : decode_any W_45a9c = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45aa0 : bv 32 := 0x00395593.
Lemma F_45aa0 : fetch_word Asan.M.loaded_segments (0x45aa0 : word) = Some W_45aa0.
Proof. vm_refl. Qed.
Lemma D_45aa0 : decode_any W_45aa0 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45aa4 : bv 32 := 0xfff68693.
Lemma F_45aa4 : fetch_word Asan.M.loaded_segments (0x45aa4 : word) = Some W_45aa4.
Proof. vm_refl. Qed.
Lemma D_45aa4 : decode_any W_45aa4 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45aa8 : bv 32 := 0x0036d713.
Lemma F_45aa8 : fetch_word Asan.M.loaded_segments (0x45aa8 : word) = Some W_45aa8.
Proof. vm_refl. Qed.
Lemma D_45aa8 : decode_any W_45aa8 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45aac : bv 32 := 0x00b605b3.
Lemma F_45aac : fetch_word Asan.M.loaded_segments (0x45aac : word) = Some W_45aac.
Proof. vm_refl. Qed.
Lemma D_45aac : decode_any W_45aac = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45ab0 : bv 32 := 0x00e60633.
Lemma F_45ab0 : fetch_word Asan.M.loaded_segments (0x45ab0 : word) = Some W_45ab0.
Proof. vm_refl. Qed.
Lemma D_45ab0 : decode_any W_45ab0 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45ab4 : bv 32 := 0xff85f713.
Lemma F_45ab4 : fetch_word Asan.M.loaded_segments (0x45ab4 : word) = Some W_45ab4.
Proof. vm_refl. Qed.
Lemma D_45ab4 : decode_any W_45ab4 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45ab8 : bv 32 := 0xff867793.
Lemma F_45ab8 : fetch_word Asan.M.loaded_segments (0x45ab8 : word) = Some W_45ab8.
Proof. vm_refl. Qed.
Lemma D_45ab8 : decode_any W_45ab8 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45abc : bv 32 := 0x00073703.
Lemma F_45abc : fetch_word Asan.M.loaded_segments (0x45abc : word) = Some W_45abc.
Proof. vm_refl. Qed.
Lemma D_45abc : decode_any W_45abc = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45ac0 : bv 32 := 0x0007b783.
Lemma F_45ac0 : fetch_word Asan.M.loaded_segments (0x45ac0 : word) = Some W_45ac0.
Proof. vm_refl. Qed.
Lemma D_45ac0 : decode_any W_45ac0 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45ac4 : bv 32 := 0x00e7e733.
Lemma F_45ac4 : fetch_word Asan.M.loaded_segments (0x45ac4 : word) = Some W_45ac4.
Proof. vm_refl. Qed.
Lemma D_45ac4 : decode_any W_45ac4 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45ac8 : bv 32 := 0x0e071c63.
Lemma F_45ac8 : fetch_word Asan.M.loaded_segments (0x45ac8 : word) = Some W_45ac8.
Proof. vm_refl. Qed.
Lemma D_45ac8 : decode_any W_45ac8 = Some (Branch BC_NE 14 0 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45acc : bv 32 := 0x06010113.
Lemma F_45acc : fetch_word Asan.M.loaded_segments (0x45acc : word) = Some W_45acc.
Proof. vm_refl. Qed.
Lemma D_45acc : decode_any W_45acc = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45ad0 : bv 32 := 0x7e813083.
Lemma F_45ad0 : fetch_word Asan.M.loaded_segments (0x45ad0 : word) = Some W_45ad0.
Proof. vm_refl. Qed.
Lemma D_45ad0 : decode_any W_45ad0 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45ad4 : bv 32 := 0x7e013403.
Lemma F_45ad4 : fetch_word Asan.M.loaded_segments (0x45ad4 : word) = Some W_45ad4.
Proof. vm_refl. Qed.
Lemma D_45ad4 : decode_any W_45ad4 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45ad8 : bv 32 := 0x7d813483.
Lemma F_45ad8 : fetch_word Asan.M.loaded_segments (0x45ad8 : word) = Some W_45ad8.
Proof. vm_refl. Qed.
Lemma D_45ad8 : decode_any W_45ad8 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45adc : bv 32 := 0x7d013903.
Lemma F_45adc : fetch_word Asan.M.loaded_segments (0x45adc : word) = Some W_45adc.
Proof. vm_refl. Qed.
Lemma D_45adc : decode_any W_45adc = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45ae0 : bv 32 := 0x7c813983.
Lemma F_45ae0 : fetch_word Asan.M.loaded_segments (0x45ae0 : word) = Some W_45ae0.
Proof. vm_refl. Qed.
Lemma D_45ae0 : decode_any W_45ae0 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45ae4 : bv 32 := 0x7c013a03.
Lemma F_45ae4 : fetch_word Asan.M.loaded_segments (0x45ae4 : word) = Some W_45ae4.
Proof. vm_refl. Qed.
Lemma D_45ae4 : decode_any W_45ae4 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45ae8 : bv 32 := 0x7b813a83.
Lemma F_45ae8 : fetch_word Asan.M.loaded_segments (0x45ae8 : word) = Some W_45ae8.
Proof. vm_refl. Qed.
Lemma D_45ae8 : decode_any W_45ae8 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45aec : bv 32 := 0x7f010113.
Lemma F_45aec : fetch_word Asan.M.loaded_segments (0x45aec : word) = Some W_45aec.
Proof. vm_refl. Qed.
Lemma D_45aec : decode_any W_45aec = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45af0 : bv 32 := 0x00008067.
Lemma F_45af0 : fetch_word Asan.M.loaded_segments (0x45af0 : word) = Some W_45af0.
Proof. vm_refl. Qed.
Lemma D_45af0 : decode_any W_45af0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45af4 : bv 32 := 0x00090513.
Lemma F_45af4 : fetch_word Asan.M.loaded_segments (0x45af4 : word) = Some W_45af4.
Proof. vm_refl. Qed.
Lemma D_45af4 : decode_any W_45af4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45af8 : bv 32 := 0x00098593.
Lemma F_45af8 : fetch_word Asan.M.loaded_segments (0x45af8 : word) = Some W_45af8.
Proof. vm_refl. Qed.
Lemma D_45af8 : decode_any W_45af8 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45afc : bv 32 := 0x00048613.
Lemma F_45afc : fetch_word Asan.M.loaded_segments (0x45afc : word) = Some W_45afc.
Proof. vm_refl. Qed.
Lemma D_45afc : decode_any W_45afc = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b00 : bv 32 := 0x06010113.
Lemma F_45b00 : fetch_word Asan.M.loaded_segments (0x45b00 : word) = Some W_45b00.
Proof. vm_refl. Qed.
Lemma D_45b00 : decode_any W_45b00 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b04 : bv 32 := 0x7e813083.
Lemma F_45b04 : fetch_word Asan.M.loaded_segments (0x45b04 : word) = Some W_45b04.
Proof. vm_refl. Qed.
Lemma D_45b04 : decode_any W_45b04 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b08 : bv 32 := 0x7e013403.
Lemma F_45b08 : fetch_word Asan.M.loaded_segments (0x45b08 : word) = Some W_45b08.
Proof. vm_refl. Qed.
Lemma D_45b08 : decode_any W_45b08 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b0c : bv 32 := 0x7d813483.
Lemma F_45b0c : fetch_word Asan.M.loaded_segments (0x45b0c : word) = Some W_45b0c.
Proof. vm_refl. Qed.
Lemma D_45b0c : decode_any W_45b0c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b10 : bv 32 := 0x7d013903.
Lemma F_45b10 : fetch_word Asan.M.loaded_segments (0x45b10 : word) = Some W_45b10.
Proof. vm_refl. Qed.
Lemma D_45b10 : decode_any W_45b10 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b14 : bv 32 := 0x7c813983.
Lemma F_45b14 : fetch_word Asan.M.loaded_segments (0x45b14 : word) = Some W_45b14.
Proof. vm_refl. Qed.
Lemma D_45b14 : decode_any W_45b14 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b18 : bv 32 := 0x7c013a03.
Lemma F_45b18 : fetch_word Asan.M.loaded_segments (0x45b18 : word) = Some W_45b18.
Proof. vm_refl. Qed.
Lemma D_45b18 : decode_any W_45b18 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b1c : bv 32 := 0x7b813a83.
Lemma F_45b1c : fetch_word Asan.M.loaded_segments (0x45b1c : word) = Some W_45b1c.
Proof. vm_refl. Qed.
Lemma D_45b1c : decode_any W_45b1c = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b20 : bv 32 := 0x7f010113.
Lemma F_45b20 : fetch_word Asan.M.loaded_segments (0x45b20 : word) = Some W_45b20.
Proof. vm_refl. Qed.
Lemma D_45b20 : decode_any W_45b20 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b24 : bv 32 := 0x5c42006f.
Lemma F_45b24 : fetch_word Asan.M.loaded_segments (0x45b24 : word) = Some W_45b24.
Proof. vm_refl. Qed.
Lemma D_45b24 : decode_any W_45b24 = Some (Jal 0 132548, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b28 : bv 32 := 0x412504b3.
Lemma F_45b28 : fetch_word Asan.M.loaded_segments (0x45b28 : word) = Some W_45b28.
Proof. vm_refl. Qed.
Lemma D_45b28 : decode_any W_45b28 = Some (Op ALU_SUB 9 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b2c : bv 32 := 0x00148493.
Lemma F_45b2c : fetch_word Asan.M.loaded_segments (0x45b2c : word) = Some W_45b2c.
Proof. vm_refl. Qed.
Lemma D_45b2c : decode_any W_45b2c = Some (OpImm ALU_ADD 9 9 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b30 : bv 32 := 0xfff94593.
Lemma F_45b30 : fetch_word Asan.M.loaded_segments (0x45b30 : word) = Some W_45b30.
Proof. vm_refl. Qed.
Lemma D_45b30 : decode_any W_45b30 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b34 : bv 32 := 0x80040a13.
Lemma F_45b34 : fetch_word Asan.M.loaded_segments (0x45b34 : word) = Some W_45b34.
Proof. vm_refl. Qed.
Lemma D_45b34 : decode_any W_45b34 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b38 : bv 32 := 0xfb0a0a13.
Lemma F_45b38 : fetch_word Asan.M.loaded_segments (0x45b38 : word) = Some W_45b38.
Proof. vm_refl. Qed.
Lemma D_45b38 : decode_any W_45b38 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b3c : bv 32 := 0xf495f4e3.
Lemma F_45b3c : fetch_word Asan.M.loaded_segments (0x45b3c : word) = Some W_45b3c.
Proof. vm_refl. Qed.
Lemma D_45b3c : decode_any W_45b3c = Some (Branch BC_GEU 11 9 8008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b40 : bv 32 := 0x80040593.
Lemma F_45b40 : fetch_word Asan.M.loaded_segments (0x45b40 : word) = Some W_45b40.
Proof. vm_refl. Qed.
Lemma D_45b40 : decode_any W_45b40 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b44 : bv 32 := 0xfc058593.
Lemma F_45b44 : fetch_word Asan.M.loaded_segments (0x45b44 : word) = Some W_45b44.
Proof. vm_refl. Qed.
Lemma D_45b44 : decode_any W_45b44 = Some (OpImm ALU_ADD 11 11 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b48 : bv 32 := 0x80040613.
Lemma F_45b48 : fetch_word Asan.M.loaded_segments (0x45b48 : word) = Some W_45b48.
Proof. vm_refl. Qed.
Lemma D_45b48 : decode_any W_45b48 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b4c : bv 32 := 0xfb060613.
Lemma F_45b4c : fetch_word Asan.M.loaded_segments (0x45b4c : word) = Some W_45b4c.
Proof. vm_refl. Qed.
Lemma D_45b4c : decode_any W_45b4c = Some (OpImm ALU_ADD 12 12 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b50 : bv 32 := 0x7ff60a93.
Lemma F_45b50 : fetch_word Asan.M.loaded_segments (0x45b50 : word) = Some W_45b50.
Proof. vm_refl. Qed.
Lemma D_45b50 : decode_any W_45b50 = Some (OpImm ALU_ADD 21 12 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b54 : bv 32 := 0x000ab4a3.
Lemma F_45b54 : fetch_word Asan.M.loaded_segments (0x45b54 : word) = Some W_45b54.
Proof. vm_refl. Qed.
Lemma D_45b54 : decode_any W_45b54 = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b58 : bv 32 := 0x00ba3023.
Lemma F_45b58 : fetch_word Asan.M.loaded_segments (0x45b58 : word) = Some W_45b58.
Proof. vm_refl. Qed.
Lemma D_45b58 : decode_any W_45b58 = Some (Store SZ8 20 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b5c : bv 32 := 0x000a3423.
Lemma F_45b5c : fetch_word Asan.M.loaded_segments (0x45b5c : word) = Some W_45b5c.
Proof. vm_refl. Qed.
Lemma D_45b5c : decode_any W_45b5c = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b60 : bv 32 := 0x00050993.
Lemma F_45b60 : fetch_word Asan.M.loaded_segments (0x45b60 : word) = Some W_45b60.
Proof. vm_refl. Qed.
Lemma D_45b60 : decode_any W_45b60 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b64 : bv 32 := 0x3252f0ef.
Lemma F_45b64 : fetch_word Asan.M.loaded_segments (0x45b64 : word) = Some W_45b64.
Proof. vm_refl. Qed.
Lemma D_45b64 : decode_any W_45b64 = Some (Jal 1 195364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b68 : bv 32 := 0x00050593.
Lemma F_45b68 : fetch_word Asan.M.loaded_segments (0x45b68 : word) = Some W_45b68.
Proof. vm_refl. Qed.
Lemma D_45b68 : decode_any W_45b68 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b6c : bv 32 := 0x00065517.
Lemma F_45b6c : fetch_word Asan.M.loaded_segments (0x45b6c : word) = Some W_45b6c.
Proof. vm_refl. Qed.
Lemma D_45b6c : decode_any W_45b6c = Some (Auipc 10 101, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b70 : bv 32 := 0x30453503.
Lemma F_45b70 : fetch_word Asan.M.loaded_segments (0x45b70 : word) = Some W_45b70.
Proof. vm_refl. Qed.
Lemma D_45b70 : decode_any W_45b70 = Some (Load SZ8 true 10 10 772, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b74 : bv 32 := 0x02154703.
Lemma F_45b74 : fetch_word Asan.M.loaded_segments (0x45b74 : word) = Some W_45b74.
Proof. vm_refl. Qed.
Lemma D_45b74 : decode_any W_45b74 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b78 : bv 32 := 0x008ab4a3.
Lemma F_45b78 : fetch_word Asan.M.loaded_segments (0x45b78 : word) = Some W_45b78.
Proof. vm_refl. Qed.
Lemma D_45b78 : decode_any W_45b78 = Some (Store SZ8 21 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b7c : bv 32 := 0x80040513.
Lemma F_45b7c : fetch_word Asan.M.loaded_segments (0x45b7c : word) = Some W_45b7c.
Proof. vm_refl. Qed.
Lemma D_45b7c : decode_any W_45b7c = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b80 : bv 32 := 0xfb050513.
Lemma F_45b80 : fetch_word Asan.M.loaded_segments (0x45b80 : word) = Some W_45b80.
Proof. vm_refl. Qed.
Lemma D_45b80 : decode_any W_45b80 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b84 : bv 32 := 0x0ff00793.
Lemma F_45b84 : fetch_word Asan.M.loaded_segments (0x45b84 : word) = Some W_45b84.
Proof. vm_refl. Qed.
Lemma D_45b84 : decode_any W_45b84 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b88 : bv 32 := 0x00040613.
Lemma F_45b88 : fetch_word Asan.M.loaded_segments (0x45b88 : word) = Some W_45b88.
Proof. vm_refl. Qed.
Lemma D_45b88 : decode_any W_45b88 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b8c : bv 32 := 0x00000693.
Lemma F_45b8c : fetch_word Asan.M.loaded_segments (0x45b8c : word) = Some W_45b8c.
Proof. vm_refl. Qed.
Lemma D_45b8c : decode_any W_45b8c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b90 : bv 32 := 0x048170ef.
Lemma F_45b90 : fetch_word Asan.M.loaded_segments (0x45b90 : word) = Some W_45b90.
Proof. vm_refl. Qed.
Lemma D_45b90 : decode_any W_45b90 = Some (Jal 1 94280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b94 : bv 32 := 0x80040613.
Lemma F_45b94 : fetch_word Asan.M.loaded_segments (0x45b94 : word) = Some W_45b94.
Proof. vm_refl. Qed.
Lemma D_45b94 : decode_any W_45b94 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b98 : bv 32 := 0xfb060613.
Lemma F_45b98 : fetch_word Asan.M.loaded_segments (0x45b98 : word) = Some W_45b98.
Proof. vm_refl. Qed.
Lemma D_45b98 : decode_any W_45b98 = Some (OpImm ALU_ADD 12 12 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45b9c : bv 32 := 0x00090513.
Lemma F_45b9c : fetch_word Asan.M.loaded_segments (0x45b9c : word) = Some W_45b9c.
Proof. vm_refl. Qed.
Lemma D_45b9c : decode_any W_45b9c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45ba0 : bv 32 := 0x00048593.
Lemma F_45ba0 : fetch_word Asan.M.loaded_segments (0x45ba0 : word) = Some W_45ba0.
Proof. vm_refl. Qed.
Lemma D_45ba0 : decode_any W_45ba0 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45ba4 : bv 32 := 0x5ed130ef.
Lemma F_45ba4 : fetch_word Asan.M.loaded_segments (0x45ba4 : word) = Some W_45ba4.
Proof. vm_refl. Qed.
Lemma D_45ba4 : decode_any W_45ba4 = Some (Jal 1 81388, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45ba8 : bv 32 := 0x00098513.
Lemma F_45ba8 : fetch_word Asan.M.loaded_segments (0x45ba8 : word) = Some W_45ba8.
Proof. vm_refl. Qed.
Lemma D_45ba8 : decode_any W_45ba8 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45bac : bv 32 := 0xfbf48593.
Lemma F_45bac : fetch_word Asan.M.loaded_segments (0x45bac : word) = Some W_45bac.
Proof. vm_refl. Qed.
Lemma D_45bac : decode_any W_45bac = Some (OpImm ALU_ADD 11 9 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45bb0 : bv 32 := 0xfbf00613.
Lemma F_45bb0 : fetch_word Asan.M.loaded_segments (0x45bb0 : word) = Some W_45bb0.
Proof. vm_refl. Qed.
Lemma D_45bb0 : decode_any W_45bb0 = Some (OpImm ALU_ADD 12 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45bb4 : bv 32 := 0xecb66ee3.
Lemma F_45bb4 : fetch_word Asan.M.loaded_segments (0x45bb4 : word) = Some W_45bb4.
Proof. vm_refl. Qed.
Lemma D_45bb4 : decode_any W_45bb4 = Some (Branch BC_LTU 12 11 7900, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45bb8 : bv 32 := 0x02049e63.
Lemma F_45bb8 : fetch_word Asan.M.loaded_segments (0x45bb8 : word) = Some W_45bb8.
Proof. vm_refl. Qed.
Lemma D_45bb8 : decode_any W_45bb8 = Some (Branch BC_NE 9 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45bbc : bv 32 := 0xf11ff06f.
Lemma F_45bbc : fetch_word Asan.M.loaded_segments (0x45bbc : word) = Some W_45bbc.
Proof. vm_refl. Qed.
Lemma D_45bbc : decode_any W_45bbc = Some (Jal 0 2096912, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45bc0 : bv 32 := 0x00060703.
Lemma F_45bc0 : fetch_word Asan.M.loaded_segments (0x45bc0 : word) = Some W_45bc0.
Proof. vm_refl. Qed.
Lemma D_45bc0 : decode_any W_45bc0 = Some (Load SZ1 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45bc4 : bv 32 := 0x0076f693.
Lemma F_45bc4 : fetch_word Asan.M.loaded_segments (0x45bc4 : word) = Some W_45bc4.
Proof. vm_refl. Qed.
Lemma D_45bc4 : decode_any W_45bc4 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45bc8 : bv 32 := 0x00e037b3.
Lemma F_45bc8 : fetch_word Asan.M.loaded_segments (0x45bc8 : word) = Some W_45bc8.
Proof. vm_refl. Qed.
Lemma D_45bc8 : decode_any W_45bc8 = Some (Op ALU_SLTU 15 0 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45bcc : bv 32 := 0x00e6a6b3.
Lemma F_45bcc : fetch_word Asan.M.loaded_segments (0x45bcc : word) = Some W_45bcc.
Proof. vm_refl. Qed.
Lemma D_45bcc : decode_any W_45bcc = Some (Op ALU_SLT 13 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45bd0 : bv 32 := 0x0016c693.
Lemma F_45bd0 : fetch_word Asan.M.loaded_segments (0x45bd0 : word) = Some W_45bd0.
Proof. vm_refl. Qed.
Lemma D_45bd0 : decode_any W_45bd0 = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45bd4 : bv 32 := 0x00d7f6b3.
Lemma F_45bd4 : fetch_word Asan.M.loaded_segments (0x45bd4 : word) = Some W_45bd4.
Proof. vm_refl. Qed.
Lemma D_45bd4 : decode_any W_45bd4 = Some (Op ALU_AND 13 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45bd8 : bv 32 := 0x00c5fa63.
Lemma F_45bd8 : fetch_word Asan.M.loaded_segments (0x45bd8 : word) = Some W_45bd8.
Proof. vm_refl. Qed.
Lemma D_45bd8 : decode_any W_45bd8 = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45bdc : bv 32 := 0x0005c703.
Lemma F_45bdc : fetch_word Asan.M.loaded_segments (0x45bdc : word) = Some W_45bdc.
Proof. vm_refl. Qed.
Lemma D_45bdc : decode_any W_45bdc = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45be0 : bv 32 := 0x00158593.
Lemma F_45be0 : fetch_word Asan.M.loaded_segments (0x45be0 : word) = Some W_45be0.
Proof. vm_refl. Qed.
Lemma D_45be0 : decode_any W_45be0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45be4 : bv 32 := 0x00d766b3.
Lemma F_45be4 : fetch_word Asan.M.loaded_segments (0x45be4 : word) = Some W_45be4.
Proof. vm_refl. Qed.
Lemma D_45be4 : decode_any W_45be4 = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45be8 : bv 32 := 0xfec59ae3.
Lemma F_45be8 : fetch_word Asan.M.loaded_segments (0x45be8 : word) = Some W_45be8.
Proof. vm_refl. Qed.
Lemma D_45be8 : decode_any W_45be8 = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45bec : bv 32 := 0x0ff6f593.
Lemma F_45bec : fetch_word Asan.M.loaded_segments (0x45bec : word) = Some W_45bec.
Proof. vm_refl. Qed.
Lemma D_45bec : decode_any W_45bec = Some (OpImm ALU_AND 11 13 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45bf0 : bv 32 := 0xec058ee3.
Lemma F_45bf0 : fetch_word Asan.M.loaded_segments (0x45bf0 : word) = Some W_45bf0.
Proof. vm_refl. Qed.
Lemma D_45bf0 : decode_any W_45bf0 = Some (Branch BC_EQ 11 0 7900, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45bf4 : bv 32 := 0x00050a93.
Lemma F_45bf4 : fetch_word Asan.M.loaded_segments (0x45bf4 : word) = Some W_45bf4.
Proof. vm_refl. Qed.
Lemma D_45bf4 : decode_any W_45bf4 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45bf8 : bv 32 := 0x00090513.
Lemma F_45bf8 : fetch_word Asan.M.loaded_segments (0x45bf8 : word) = Some W_45bf8.
Proof. vm_refl. Qed.
Lemma D_45bf8 : decode_any W_45bf8 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45bfc : bv 32 := 0x00048593.
Lemma F_45bfc : fetch_word Asan.M.loaded_segments (0x45bfc : word) = Some W_45bfc.
Proof. vm_refl. Qed.
Lemma D_45bfc : decode_any W_45bfc = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c00 : bv 32 := 0x5ad100ef.
Lemma F_45c00 : fetch_word Asan.M.loaded_segments (0x45c00 : word) = Some W_45c00.
Proof. vm_refl. Qed.
Lemma D_45c00 : decode_any W_45c00 = Some (Jal 1 69036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c04 : bv 32 := 0x00050913.
Lemma F_45c04 : fetch_word Asan.M.loaded_segments (0x45c04 : word) = Some W_45c04.
Proof. vm_refl. Qed.
Lemma D_45c04 : decode_any W_45c04 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c08 : bv 32 := 0x000a8513.
Lemma F_45c08 : fetch_word Asan.M.loaded_segments (0x45c08 : word) = Some W_45c08.
Proof. vm_refl. Qed.
Lemma D_45c08 : decode_any W_45c08 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c0c : bv 32 := 0xec0900e3.
Lemma F_45c0c : fetch_word Asan.M.loaded_segments (0x45c0c : word) = Some W_45c0c.
Proof. vm_refl. Qed.
Lemma D_45c0c : decode_any W_45c0c = Some (Branch BC_EQ 18 0 7872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c10 : bv 32 := 0xfffd5517.
Lemma F_45c10 : fetch_word Asan.M.loaded_segments (0x45c10 : word) = Some W_45c10.
Proof. vm_refl. Qed.
Lemma D_45c10 : decode_any W_45c10 = Some (Auipc 10 1048533, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c14 : bv 32 := 0x06350513.
Lemma F_45c14 : fetch_word Asan.M.loaded_segments (0x45c14 : word) = Some W_45c14.
Proof. vm_refl. Qed.
Lemma D_45c14 : decode_any W_45c14 = Some (OpImm ALU_ADD 10 10 99, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c18 : bv 32 := 0x76d170ef.
Lemma F_45c18 : fetch_word Asan.M.loaded_segments (0x45c18 : word) = Some W_45c18.
Proof. vm_refl. Qed.
Lemma D_45c18 : decode_any W_45c18 = Some (Jal 1 98156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c1c : bv 32 := 0x00050593.
Lemma F_45c1c : fetch_word Asan.M.loaded_segments (0x45c1c : word) = Some W_45c1c.
Proof. vm_refl. Qed.
Lemma D_45c1c : decode_any W_45c1c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c20 : bv 32 := 0x000a8513.
Lemma F_45c20 : fetch_word Asan.M.loaded_segments (0x45c20 : word) = Some W_45c20.
Proof. vm_refl. Qed.
Lemma D_45c20 : decode_any W_45c20 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c24 : bv 32 := 0xea0594e3.
Lemma F_45c24 : fetch_word Asan.M.loaded_segments (0x45c24 : word) = Some W_45c24.
Proof. vm_refl. Qed.
Lemma D_45c24 : decode_any W_45c24 = Some (Branch BC_NE 11 0 7848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c28 : bv 32 := 0x7c5170ef.
Lemma F_45c28 : fetch_word Asan.M.loaded_segments (0x45c28 : word) = Some W_45c28.
Proof. vm_refl. Qed.
Lemma D_45c28 : decode_any W_45c28 = Some (Jal 1 98244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c2c : bv 32 := 0x06050a63.
Lemma F_45c2c : fetch_word Asan.M.loaded_segments (0x45c2c : word) = Some W_45c2c.
Proof. vm_refl. Qed.
Lemma D_45c2c : decode_any W_45c2c = Some (Branch BC_EQ 10 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c30 : bv 32 := 0x80040513.
Lemma F_45c30 : fetch_word Asan.M.loaded_segments (0x45c30 : word) = Some W_45c30.
Proof. vm_refl. Qed.
Lemma D_45c30 : decode_any W_45c30 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c34 : bv 32 := 0xfc050513.
Lemma F_45c34 : fetch_word Asan.M.loaded_segments (0x45c34 : word) = Some W_45c34.
Proof. vm_refl. Qed.
Lemma D_45c34 : decode_any W_45c34 = Some (OpImm ALU_ADD 10 10 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c38 : bv 32 := 0x80040593.
Lemma F_45c38 : fetch_word Asan.M.loaded_segments (0x45c38 : word) = Some W_45c38.
Proof. vm_refl. Qed.
Lemma D_45c38 : decode_any W_45c38 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c3c : bv 32 := 0xfb058593.
Lemma F_45c3c : fetch_word Asan.M.loaded_segments (0x45c3c : word) = Some W_45c3c.
Proof. vm_refl. Qed.
Lemma D_45c3c : decode_any W_45c3c = Some (OpImm ALU_ADD 11 11 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c40 : bv 32 := 0x7ff58993.
Lemma F_45c40 : fetch_word Asan.M.loaded_segments (0x45c40 : word) = Some W_45c40.
Proof. vm_refl. Qed.
Lemma D_45c40 : decode_any W_45c40 = Some (OpImm ALU_ADD 19 11 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c44 : bv 32 := 0x0009b4a3.
Lemma F_45c44 : fetch_word Asan.M.loaded_segments (0x45c44 : word) = Some W_45c44.
Proof. vm_refl. Qed.
Lemma D_45c44 : decode_any W_45c44 = Some (Store SZ8 19 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c48 : bv 32 := 0x00aa3023.
Lemma F_45c48 : fetch_word Asan.M.loaded_segments (0x45c48 : word) = Some W_45c48.
Proof. vm_refl. Qed.
Lemma D_45c48 : decode_any W_45c48 = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c4c : bv 32 := 0x000a3423.
Lemma F_45c4c : fetch_word Asan.M.loaded_segments (0x45c4c : word) = Some W_45c4c.
Proof. vm_refl. Qed.
Lemma D_45c4c : decode_any W_45c4c = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c50 : bv 32 := 0x2392f0ef.
Lemma F_45c50 : fetch_word Asan.M.loaded_segments (0x45c50 : word) = Some W_45c50.
Proof. vm_refl. Qed.
Lemma D_45c50 : decode_any W_45c50 = Some (Jal 1 195128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c54 : bv 32 := 0x00050593.
Lemma F_45c54 : fetch_word Asan.M.loaded_segments (0x45c54 : word) = Some W_45c54.
Proof. vm_refl. Qed.
Lemma D_45c54 : decode_any W_45c54 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c58 : bv 32 := 0x00065517.
Lemma F_45c58 : fetch_word Asan.M.loaded_segments (0x45c58 : word) = Some W_45c58.
Proof. vm_refl. Qed.
Lemma D_45c58 : decode_any W_45c58 = Some (Auipc 10 101, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c5c : bv 32 := 0x21853503.
Lemma F_45c5c : fetch_word Asan.M.loaded_segments (0x45c5c : word) = Some W_45c5c.
Proof. vm_refl. Qed.
Lemma D_45c5c : decode_any W_45c5c = Some (Load SZ8 true 10 10 536, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c60 : bv 32 := 0x02154703.
Lemma F_45c60 : fetch_word Asan.M.loaded_segments (0x45c60 : word) = Some W_45c60.
Proof. vm_refl. Qed.
Lemma D_45c60 : decode_any W_45c60 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c64 : bv 32 := 0x0089b4a3.
Lemma F_45c64 : fetch_word Asan.M.loaded_segments (0x45c64 : word) = Some W_45c64.
Proof. vm_refl. Qed.
Lemma D_45c64 : decode_any W_45c64 = Some (Store SZ8 19 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c68 : bv 32 := 0x80040513.
Lemma F_45c68 : fetch_word Asan.M.loaded_segments (0x45c68 : word) = Some W_45c68.
Proof. vm_refl. Qed.
Lemma D_45c68 : decode_any W_45c68 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c6c : bv 32 := 0xfb050513.
Lemma F_45c6c : fetch_word Asan.M.loaded_segments (0x45c6c : word) = Some W_45c6c.
Proof. vm_refl. Qed.
Lemma D_45c6c : decode_any W_45c6c = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c70 : bv 32 := 0x0ff00793.
Lemma F_45c70 : fetch_word Asan.M.loaded_segments (0x45c70 : word) = Some W_45c70.
Proof. vm_refl. Qed.
Lemma D_45c70 : decode_any W_45c70 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c74 : bv 32 := 0x00040613.
Lemma F_45c74 : fetch_word Asan.M.loaded_segments (0x45c74 : word) = Some W_45c74.
Proof. vm_refl. Qed.
Lemma D_45c74 : decode_any W_45c74 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c78 : bv 32 := 0x00000693.
Lemma F_45c78 : fetch_word Asan.M.loaded_segments (0x45c78 : word) = Some W_45c78.
Proof. vm_refl. Qed.
Lemma D_45c78 : decode_any W_45c78 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c7c : bv 32 := 0x75d160ef.
Lemma F_45c7c : fetch_word Asan.M.loaded_segments (0x45c7c : word) = Some W_45c7c.
Proof. vm_refl. Qed.
Lemma D_45c7c : decode_any W_45c7c = Some (Jal 1 94044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c80 : bv 32 := 0x80040513.
Lemma F_45c80 : fetch_word Asan.M.loaded_segments (0x45c80 : word) = Some W_45c80.
Proof. vm_refl. Qed.
Lemma D_45c80 : decode_any W_45c80 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c84 : bv 32 := 0xfb050513.
Lemma F_45c84 : fetch_word Asan.M.loaded_segments (0x45c84 : word) = Some W_45c84.
Proof. vm_refl. Qed.
Lemma D_45c84 : decode_any W_45c84 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c88 : bv 32 := 0x26c180ef.
Lemma F_45c88 : fetch_word Asan.M.loaded_segments (0x45c88 : word) = Some W_45c88.
Proof. vm_refl. Qed.
Lemma D_45c88 : decode_any W_45c88 = Some (Jal 1 98924, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c8c : bv 32 := 0x00050593.
Lemma F_45c8c : fetch_word Asan.M.loaded_segments (0x45c8c : word) = Some W_45c8c.
Proof. vm_refl. Qed.
Lemma D_45c8c : decode_any W_45c8c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c90 : bv 32 := 0x00040993.
Lemma F_45c90 : fetch_word Asan.M.loaded_segments (0x45c90 : word) = Some W_45c90.
Proof. vm_refl. Qed.
Lemma D_45c90 : decode_any W_45c90 = Some (OpImm ALU_ADD 19 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c94 : bv 32 := 0x000a8513.
Lemma F_45c94 : fetch_word Asan.M.loaded_segments (0x45c94 : word) = Some W_45c94.
Proof. vm_refl. Qed.
Lemma D_45c94 : decode_any W_45c94 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c98 : bv 32 := 0xe2059ae3.
Lemma F_45c98 : fetch_word Asan.M.loaded_segments (0x45c98 : word) = Some W_45c98.
Proof. vm_refl. Qed.
Lemma D_45c98 : decode_any W_45c98 = Some (Branch BC_NE 11 0 7732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45c9c : bv 32 := 0x0080006f.
Lemma F_45c9c : fetch_word Asan.M.loaded_segments (0x45c9c : word) = Some W_45c9c.
Proof. vm_refl. Qed.
Lemma D_45c9c : decode_any W_45c9c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45ca0 : bv 32 := 0x00040993.
Lemma F_45ca0 : fetch_word Asan.M.loaded_segments (0x45ca0 : word) = Some W_45ca0.
Proof. vm_refl. Qed.
Lemma D_45ca0 : decode_any W_45ca0 = Some (OpImm ALU_ADD 19 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45ca4 : bv 32 := 0x1e52f0ef.
Lemma F_45ca4 : fetch_word Asan.M.loaded_segments (0x45ca4 : word) = Some W_45ca4.
Proof. vm_refl. Qed.
Lemma D_45ca4 : decode_any W_45ca4 = Some (Jal 1 195044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45ca8 : bv 32 := 0xfffca597.
Lemma F_45ca8 : fetch_word Asan.M.loaded_segments (0x45ca8 : word) = Some W_45ca8.
Proof. vm_refl. Qed.
Lemma D_45ca8 : decode_any W_45ca8 = Some (Auipc 11 1048522, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45cac : bv 32 := 0x7505b583.
Lemma F_45cac : fetch_word Asan.M.loaded_segments (0x45cac : word) = Some W_45cac.
Proof. vm_refl. Qed.
Lemma D_45cac : decode_any W_45cac = Some (Load SZ8 true 11 11 1872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45cb0 : bv 32 := 0x00ba3023.
Lemma F_45cb0 : fetch_word Asan.M.loaded_segments (0x45cb0 : word) = Some W_45cb0.
Proof. vm_refl. Qed.
Lemma D_45cb0 : decode_any W_45cb0 = Some (Store SZ8 20 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45cb4 : bv 32 := 0x80040613.
Lemma F_45cb4 : fetch_word Asan.M.loaded_segments (0x45cb4 : word) = Some W_45cb4.
Proof. vm_refl. Qed.
Lemma D_45cb4 : decode_any W_45cb4 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45cb8 : bv 32 := 0xfb060613.
Lemma F_45cb8 : fetch_word Asan.M.loaded_segments (0x45cb8 : word) = Some W_45cb8.
Proof. vm_refl. Qed.
Lemma D_45cb8 : decode_any W_45cb8 = Some (OpImm ALU_ADD 12 12 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45cbc : bv 32 := 0x00098593.
Lemma F_45cbc : fetch_word Asan.M.loaded_segments (0x45cbc : word) = Some W_45cbc.
Proof. vm_refl. Qed.
Lemma D_45cbc : decode_any W_45cbc = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45cc0 : bv 32 := 0x00090693.
Lemma F_45cc0 : fetch_word Asan.M.loaded_segments (0x45cc0 : word) = Some W_45cc0.
Proof. vm_refl. Qed.
Lemma D_45cc0 : decode_any W_45cc0 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45cc4 : bv 32 := 0x00000713.
Lemma F_45cc4 : fetch_word Asan.M.loaded_segments (0x45cc4 : word) = Some W_45cc4.
Proof. vm_refl. Qed.
Lemma D_45cc4 : decode_any W_45cc4 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45cc8 : bv 32 := 0x00048793.
Lemma F_45cc8 : fetch_word Asan.M.loaded_segments (0x45cc8 : word) = Some W_45cc8.
Proof. vm_refl. Qed.
Lemma D_45cc8 : decode_any W_45cc8 = Some (OpImm ALU_ADD 15 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45ccc : bv 32 := 0x00000813.
Lemma F_45ccc : fetch_word Asan.M.loaded_segments (0x45ccc : word) = Some W_45ccc.
Proof. vm_refl. Qed.
Lemma D_45ccc : decode_any W_45ccc = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45cd0 : bv 32 := 0x00000893.
Lemma F_45cd0 : fetch_word Asan.M.loaded_segments (0x45cd0 : word) = Some W_45cd0.
Proof. vm_refl. Qed.
Lemma D_45cd0 : decode_any W_45cd0 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45cd4 : bv 32 := 0x214140ef.
Lemma F_45cd4 : fetch_word Asan.M.loaded_segments (0x45cd4 : word) = Some W_45cd4.
Proof. vm_refl. Qed.
Lemma D_45cd4 : decode_any W_45cd4 = Some (Jal 1 82452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45cd8 : bv 32 := 0x000a8513.
Lemma F_45cd8 : fetch_word Asan.M.loaded_segments (0x45cd8 : word) = Some W_45cd8.
Proof. vm_refl. Qed.
Lemma D_45cd8 : decode_any W_45cd8 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45cdc : bv 32 := 0xdf1ff06f.
Lemma F_45cdc : fetch_word Asan.M.loaded_segments (0x45cdc : word) = Some W_45cdc.
Proof. vm_refl. Qed.
Lemma D_45cdc : decode_any W_45cdc = Some (Jal 0 2096624, 4%Z).
Proof. vm_refl. Qed.
