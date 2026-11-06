(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_17a4c : bv 32 := 0xffff9197.
Lemma F_17a4c : fetch_word Ubsan.M.loaded_segments (0x17a4c : word) = Some W_17a4c.
Proof. vm_refl. Qed.
Lemma D_17a4c : decode_any W_17a4c = Some (Auipc 3 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a50 : bv 32 := 0xdb418193.
Lemma F_17a50 : fetch_word Ubsan.M.loaded_segments (0x17a50 : word) = Some W_17a50.
Proof. vm_refl. Qed.
Lemma D_17a50 : decode_any W_17a50 = Some (OpImm ALU_ADD 3 3 3508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a54 : bv 32 := 0x00010513.
Lemma F_17a54 : fetch_word Ubsan.M.loaded_segments (0x17a54 : word) = Some W_17a54.
Proof. vm_refl. Qed.
Lemma D_17a54 : decode_any W_17a54 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a58 : bv 32 := 0xfffe8597.
Lemma F_17a58 : fetch_word Ubsan.M.loaded_segments (0x17a58 : word) = Some W_17a58.
Proof. vm_refl. Qed.
Lemma D_17a58 : decode_any W_17a58 = Some (Auipc 11 1048552, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a5c : bv 32 := 0x5a858593.
Lemma F_17a5c : fetch_word Ubsan.M.loaded_segments (0x17a5c : word) = Some W_17a5c.
Proof. vm_refl. Qed.
Lemma D_17a5c : decode_any W_17a5c = Some (OpImm ALU_ADD 11 11 1448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a60 : bv 32 := 0xff017113.
Lemma F_17a60 : fetch_word Ubsan.M.loaded_segments (0x17a60 : word) = Some W_17a60.
Proof. vm_refl. Qed.
Lemma D_17a60 : decode_any W_17a60 = Some (OpImm ALU_AND 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a64 : bv 32 := 0x0040006f.
Lemma F_17a64 : fetch_word Ubsan.M.loaded_segments (0x17a64 : word) = Some W_17a64.
Proof. vm_refl. Qed.
Lemma D_17a64 : decode_any W_17a64 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a68 : bv 32 := 0x00052583.
Lemma F_17a68 : fetch_word Ubsan.M.loaded_segments (0x17a68 : word) = Some W_17a68.
Proof. vm_refl. Qed.
Lemma D_17a68 : decode_any W_17a68 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a6c : bv 32 := 0x00019617.
Lemma F_17a6c : fetch_word Ubsan.M.loaded_segments (0x17a6c : word) = Some W_17a6c.
Proof. vm_refl. Qed.
Lemma D_17a6c : decode_any W_17a6c = Some (Auipc 12 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a70 : bv 32 := 0x00019697.
Lemma F_17a70 : fetch_word Ubsan.M.loaded_segments (0x17a70 : word) = Some W_17a70.
Proof. vm_refl. Qed.
Lemma D_17a70 : decode_any W_17a70 = Some (Auipc 13 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a74 : bv 32 := 0x00019717.
Lemma F_17a74 : fetch_word Ubsan.M.loaded_segments (0x17a74 : word) = Some W_17a74.
Proof. vm_refl. Qed.
Lemma D_17a74 : decode_any W_17a74 = Some (Auipc 14 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a78 : bv 32 := 0xccc63783.
Lemma F_17a78 : fetch_word Ubsan.M.loaded_segments (0x17a78 : word) = Some W_17a78.
Proof. vm_refl. Qed.
Lemma D_17a78 : decode_any W_17a78 = Some (Load SZ8 true 15 12 3276, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a7c : bv 32 := 0xcd06b683.
Lemma F_17a7c : fetch_word Ubsan.M.loaded_segments (0x17a7c : word) = Some W_17a7c.
Proof. vm_refl. Qed.
Lemma D_17a7c : decode_any W_17a7c = Some (Load SZ8 true 13 13 3280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a80 : bv 32 := 0xcd473703.
Lemma F_17a80 : fetch_word Ubsan.M.loaded_segments (0x17a80 : word) = Some W_17a80.
Proof. vm_refl. Qed.
Lemma D_17a80 : decode_any W_17a80 = Some (Load SZ8 true 14 14 3284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a84 : bv 32 := 0x00850613.
Lemma F_17a84 : fetch_word Ubsan.M.loaded_segments (0x17a84 : word) = Some W_17a84.
Proof. vm_refl. Qed.
Lemma D_17a84 : decode_any W_17a84 = Some (OpImm ALU_ADD 12 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a88 : bv 32 := 0x00078513.
Lemma F_17a88 : fetch_word Ubsan.M.loaded_segments (0x17a88 : word) = Some W_17a88.
Proof. vm_refl. Qed.
Lemma D_17a88 : decode_any W_17a88 = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a8c : bv 32 := 0x00000793.
Lemma F_17a8c : fetch_word Ubsan.M.loaded_segments (0x17a8c : word) = Some W_17a8c.
Proof. vm_refl. Qed.
Lemma D_17a8c : decode_any W_17a8c = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a90 : bv 32 := 0x4490a06f.
Lemma F_17a90 : fetch_word Ubsan.M.loaded_segments (0x17a90 : word) = Some W_17a90.
Proof. vm_refl. Qed.
Lemma D_17a90 : decode_any W_17a90 = Some (Jal 0 44104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a94 : bv 32 := 0xff010113.
Lemma F_17a94 : fetch_word Ubsan.M.loaded_segments (0x17a94 : word) = Some W_17a94.
Proof. vm_refl. Qed.
Lemma D_17a94 : decode_any W_17a94 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a98 : bv 32 := 0x00113423.
Lemma F_17a98 : fetch_word Ubsan.M.loaded_segments (0x17a98 : word) = Some W_17a98.
Proof. vm_refl. Qed.
Lemma D_17a98 : decode_any W_17a98 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a9c : bv 32 := 0x00813023.
Lemma F_17a9c : fetch_word Ubsan.M.loaded_segments (0x17a9c : word) = Some W_17a9c.
Proof. vm_refl. Qed.
Lemma D_17a9c : decode_any W_17a9c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17aa0 : bv 32 := 0x01010413.
Lemma F_17aa0 : fetch_word Ubsan.M.loaded_segments (0x17aa0 : word) = Some W_17aa0.
Proof. vm_refl. Qed.
Lemma D_17aa0 : decode_any W_17aa0 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17aa4 : bv 32 := 0x0001a517.
Lemma F_17aa4 : fetch_word Ubsan.M.loaded_segments (0x17aa4 : word) = Some W_17aa4.
Proof. vm_refl. Qed.
Lemma D_17aa4 : decode_any W_17aa4 = Some (Auipc 10 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17aa8 : bv 32 := 0x0ac50513.
Lemma F_17aa8 : fetch_word Ubsan.M.loaded_segments (0x17aa8 : word) = Some W_17aa8.
Proof. vm_refl. Qed.
Lemma D_17aa8 : decode_any W_17aa8 = Some (OpImm ALU_ADD 10 10 172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17aac : bv 32 := 0x00054503.
Lemma F_17aac : fetch_word Ubsan.M.loaded_segments (0x17aac : word) = Some W_17aac.
Proof. vm_refl. Qed.
Lemma D_17aac : decode_any W_17aac = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ab0 : bv 32 := 0x00157513.
Lemma F_17ab0 : fetch_word Ubsan.M.loaded_segments (0x17ab0 : word) = Some W_17ab0.
Proof. vm_refl. Qed.
Lemma D_17ab0 : decode_any W_17ab0 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ab4 : bv 32 := 0x00050663.
Lemma F_17ab4 : fetch_word Ubsan.M.loaded_segments (0x17ab4 : word) = Some W_17ab4.
Proof. vm_refl. Qed.
Lemma D_17ab4 : decode_any W_17ab4 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ac0 : bv 32 := 0x0001a517.
Lemma F_17ac0 : fetch_word Ubsan.M.loaded_segments (0x17ac0 : word) = Some W_17ac0.
Proof. vm_refl. Qed.
Lemma D_17ac0 : decode_any W_17ac0 = Some (Auipc 10 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ac4 : bv 32 := 0x09050593.
Lemma F_17ac4 : fetch_word Ubsan.M.loaded_segments (0x17ac4 : word) = Some W_17ac4.
Proof. vm_refl. Qed.
Lemma D_17ac4 : decode_any W_17ac4 = Some (OpImm ALU_ADD 11 10 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ac8 : bv 32 := 0x00100513.
Lemma F_17ac8 : fetch_word Ubsan.M.loaded_segments (0x17ac8 : word) = Some W_17ac8.
Proof. vm_refl. Qed.
Lemma D_17ac8 : decode_any W_17ac8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17acc : bv 32 := 0x00a58023.
Lemma F_17acc : fetch_word Ubsan.M.loaded_segments (0x17acc : word) = Some W_17acc.
Proof. vm_refl. Qed.
Lemma D_17acc : decode_any W_17acc = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ad0 : bv 32 := 0x00019517.
Lemma F_17ad0 : fetch_word Ubsan.M.loaded_segments (0x17ad0 : word) = Some W_17ad0.
Proof. vm_refl. Qed.
Lemma D_17ad0 : decode_any W_17ad0 = Some (Auipc 10 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ad4 : bv 32 := 0xc8053503.
Lemma F_17ad4 : fetch_word Ubsan.M.loaded_segments (0x17ad4 : word) = Some W_17ad4.
Proof. vm_refl. Qed.
Lemma D_17ad4 : decode_any W_17ad4 = Some (Load SZ8 true 10 10 3200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ad8 : bv 32 := 0x02050063.
Lemma F_17ad8 : fetch_word Ubsan.M.loaded_segments (0x17ad8 : word) = Some W_17ad8.
Proof. vm_refl. Qed.
Lemma D_17ad8 : decode_any W_17ad8 = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17af8 : bv 32 := 0x00813083.
Lemma F_17af8 : fetch_word Ubsan.M.loaded_segments (0x17af8 : word) = Some W_17af8.
Proof. vm_refl. Qed.
Lemma D_17af8 : decode_any W_17af8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17afc : bv 32 := 0x00013403.
Lemma F_17afc : fetch_word Ubsan.M.loaded_segments (0x17afc : word) = Some W_17afc.
Proof. vm_refl. Qed.
Lemma D_17afc : decode_any W_17afc = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b00 : bv 32 := 0x01010113.
Lemma F_17b00 : fetch_word Ubsan.M.loaded_segments (0x17b00 : word) = Some W_17b00.
Proof. vm_refl. Qed.
Lemma D_17b00 : decode_any W_17b00 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b04 : bv 32 := 0x00008067.
Lemma F_17b04 : fetch_word Ubsan.M.loaded_segments (0x17b04 : word) = Some W_17b04.
Proof. vm_refl. Qed.
Lemma D_17b04 : decode_any W_17b04 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b08 : bv 32 := 0xff010113.
Lemma F_17b08 : fetch_word Ubsan.M.loaded_segments (0x17b08 : word) = Some W_17b08.
Proof. vm_refl. Qed.
Lemma D_17b08 : decode_any W_17b08 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b0c : bv 32 := 0x00113423.
Lemma F_17b0c : fetch_word Ubsan.M.loaded_segments (0x17b0c : word) = Some W_17b0c.
Proof. vm_refl. Qed.
Lemma D_17b0c : decode_any W_17b0c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b10 : bv 32 := 0x00813023.
Lemma F_17b10 : fetch_word Ubsan.M.loaded_segments (0x17b10 : word) = Some W_17b10.
Proof. vm_refl. Qed.
Lemma D_17b10 : decode_any W_17b10 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b14 : bv 32 := 0x01010413.
Lemma F_17b14 : fetch_word Ubsan.M.loaded_segments (0x17b14 : word) = Some W_17b14.
Proof. vm_refl. Qed.
Lemma D_17b14 : decode_any W_17b14 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b18 : bv 32 := 0x0001a517.
Lemma F_17b18 : fetch_word Ubsan.M.loaded_segments (0x17b18 : word) = Some W_17b18.
Proof. vm_refl. Qed.
Lemma D_17b18 : decode_any W_17b18 = Some (Auipc 10 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b1c : bv 32 := 0x08050513.
Lemma F_17b1c : fetch_word Ubsan.M.loaded_segments (0x17b1c : word) = Some W_17b1c.
Proof. vm_refl. Qed.
Lemma D_17b1c : decode_any W_17b1c = Some (OpImm ALU_ADD 10 10 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b20 : bv 32 := 0x00054503.
Lemma F_17b20 : fetch_word Ubsan.M.loaded_segments (0x17b20 : word) = Some W_17b20.
Proof. vm_refl. Qed.
Lemma D_17b20 : decode_any W_17b20 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b24 : bv 32 := 0x00157513.
Lemma F_17b24 : fetch_word Ubsan.M.loaded_segments (0x17b24 : word) = Some W_17b24.
Proof. vm_refl. Qed.
Lemma D_17b24 : decode_any W_17b24 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b28 : bv 32 := 0x00050663.
Lemma F_17b28 : fetch_word Ubsan.M.loaded_segments (0x17b28 : word) = Some W_17b28.
Proof. vm_refl. Qed.
Lemma D_17b28 : decode_any W_17b28 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b34 : bv 32 := 0x0001a517.
Lemma F_17b34 : fetch_word Ubsan.M.loaded_segments (0x17b34 : word) = Some W_17b34.
Proof. vm_refl. Qed.
Lemma D_17b34 : decode_any W_17b34 = Some (Auipc 10 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b38 : bv 32 := 0x06450593.
Lemma F_17b38 : fetch_word Ubsan.M.loaded_segments (0x17b38 : word) = Some W_17b38.
Proof. vm_refl. Qed.
Lemma D_17b38 : decode_any W_17b38 = Some (OpImm ALU_ADD 11 10 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b3c : bv 32 := 0x00100513.
Lemma F_17b3c : fetch_word Ubsan.M.loaded_segments (0x17b3c : word) = Some W_17b3c.
Proof. vm_refl. Qed.
Lemma D_17b3c : decode_any W_17b3c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b40 : bv 32 := 0x00a58023.
Lemma F_17b40 : fetch_word Ubsan.M.loaded_segments (0x17b40 : word) = Some W_17b40.
Proof. vm_refl. Qed.
Lemma D_17b40 : decode_any W_17b40 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b44 : bv 32 := 0x00019517.
Lemma F_17b44 : fetch_word Ubsan.M.loaded_segments (0x17b44 : word) = Some W_17b44.
Proof. vm_refl. Qed.
Lemma D_17b44 : decode_any W_17b44 = Some (Auipc 10 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b48 : bv 32 := 0xc1453503.
Lemma F_17b48 : fetch_word Ubsan.M.loaded_segments (0x17b48 : word) = Some W_17b48.
Proof. vm_refl. Qed.
Lemma D_17b48 : decode_any W_17b48 = Some (Load SZ8 true 10 10 3092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b4c : bv 32 := 0x00050e63.
Lemma F_17b4c : fetch_word Ubsan.M.loaded_segments (0x17b4c : word) = Some W_17b4c.
Proof. vm_refl. Qed.
Lemma D_17b4c : decode_any W_17b4c = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b50 : bv 32 := 0x0040006f.
Lemma F_17b50 : fetch_word Ubsan.M.loaded_segments (0x17b50 : word) = Some W_17b50.
Proof. vm_refl. Qed.
Lemma D_17b50 : decode_any W_17b50 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b54 : bv 32 := 0x0001a517.
Lemma F_17b54 : fetch_word Ubsan.M.loaded_segments (0x17b54 : word) = Some W_17b54.
Proof. vm_refl. Qed.
Lemma D_17b54 : decode_any W_17b54 = Some (Auipc 10 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b58 : bv 32 := 0xca450513.
Lemma F_17b58 : fetch_word Ubsan.M.loaded_segments (0x17b58 : word) = Some W_17b58.
Proof. vm_refl. Qed.
Lemma D_17b58 : decode_any W_17b58 = Some (OpImm ALU_ADD 10 10 3236, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b5c : bv 32 := 0x00053503.
Lemma F_17b5c : fetch_word Ubsan.M.loaded_segments (0x17b5c : word) = Some W_17b5c.
Proof. vm_refl. Qed.
Lemma D_17b5c : decode_any W_17b5c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b60 : bv 32 := 0x0c00b0ef.
Lemma F_17b60 : fetch_word Ubsan.M.loaded_segments (0x17b60 : word) = Some W_17b60.
Proof. vm_refl. Qed.
Lemma D_17b60 : decode_any W_17b60 = Some (Jal 1 45248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b64 : bv 32 := 0x0040006f.
Lemma F_17b64 : fetch_word Ubsan.M.loaded_segments (0x17b64 : word) = Some W_17b64.
Proof. vm_refl. Qed.
Lemma D_17b64 : decode_any W_17b64 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b68 : bv 32 := 0x00019517.
Lemma F_17b68 : fetch_word Ubsan.M.loaded_segments (0x17b68 : word) = Some W_17b68.
Proof. vm_refl. Qed.
Lemma D_17b68 : decode_any W_17b68 = Some (Auipc 10 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b6c : bv 32 := 0xbf853503.
Lemma F_17b6c : fetch_word Ubsan.M.loaded_segments (0x17b6c : word) = Some W_17b6c.
Proof. vm_refl. Qed.
Lemma D_17b6c : decode_any W_17b6c = Some (Load SZ8 true 10 10 3064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b70 : bv 32 := 0x00050c63.
Lemma F_17b70 : fetch_word Ubsan.M.loaded_segments (0x17b70 : word) = Some W_17b70.
Proof. vm_refl. Qed.
Lemma D_17b70 : decode_any W_17b70 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b88 : bv 32 := 0x00813083.
Lemma F_17b88 : fetch_word Ubsan.M.loaded_segments (0x17b88 : word) = Some W_17b88.
Proof. vm_refl. Qed.
Lemma D_17b88 : decode_any W_17b88 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b8c : bv 32 := 0x00013403.
Lemma F_17b8c : fetch_word Ubsan.M.loaded_segments (0x17b8c : word) = Some W_17b8c.
Proof. vm_refl. Qed.
Lemma D_17b8c : decode_any W_17b8c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b90 : bv 32 := 0x01010113.
Lemma F_17b90 : fetch_word Ubsan.M.loaded_segments (0x17b90 : word) = Some W_17b90.
Proof. vm_refl. Qed.
Lemma D_17b90 : decode_any W_17b90 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b94 : bv 32 := 0x00008067.
Lemma F_17b94 : fetch_word Ubsan.M.loaded_segments (0x17b94 : word) = Some W_17b94.
Proof. vm_refl. Qed.
Lemma D_17b94 : decode_any W_17b94 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ee0 : bv 32 := 0x00090493.
Lemma F_17ee0 : fetch_word Ubsan.M.loaded_segments (0x17ee0 : word) = Some W_17ee0.
Proof. vm_refl. Qed.
Lemma D_17ee0 : decode_any W_17ee0 = Some (OpImm ALU_ADD 9 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ee4 : bv 32 := 0x0340006f.
Lemma F_17ee4 : fetch_word Ubsan.M.loaded_segments (0x17ee4 : word) = Some W_17ee4.
Proof. vm_refl. Qed.
Lemma D_17ee4 : decode_any W_17ee4 = Some (Jal 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f18 : bv 32 := 0x00000b13.
Lemma F_17f18 : fetch_word Ubsan.M.loaded_segments (0x17f18 : word) = Some W_17f18.
Proof. vm_refl. Qed.
Lemma D_17f18 : decode_any W_17f18 = Some (OpImm ALU_ADD 22 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f1c : bv 32 := 0xffe00b93.
Lemma F_17f1c : fetch_word Ubsan.M.loaded_segments (0x17f1c : word) = Some W_17f1c.
Proof. vm_refl. Qed.
Lemma D_17f1c : decode_any W_17f1c = Some (OpImm ALU_ADD 23 0 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f20 : bv 32 := 0x00100513.
Lemma F_17f20 : fetch_word Ubsan.M.loaded_segments (0x17f20 : word) = Some W_17f20.
Proof. vm_refl. Qed.
Lemma D_17f20 : decode_any W_17f20 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f24 : bv 32 := 0x00aa0223.
Lemma F_17f24 : fetch_word Ubsan.M.loaded_segments (0x17f24 : word) = Some W_17f24.
Proof. vm_refl. Qed.
Lemma D_17f24 : decode_any W_17f24 = Some (Store SZ1 20 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f28 : bv 32 := 0x00048513.
Lemma F_17f28 : fetch_word Ubsan.M.loaded_segments (0x17f28 : word) = Some W_17f28.
Proof. vm_refl. Qed.
Lemma D_17f28 : decode_any W_17f28 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f2c : bv 32 := 0x00040593.
Lemma F_17f2c : fetch_word Ubsan.M.loaded_segments (0x17f2c : word) = Some W_17f2c.
Proof. vm_refl. Qed.
Lemma D_17f2c : decode_any W_17f2c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f30 : bv 32 := 0x14c000ef.
Lemma F_17f30 : fetch_word Ubsan.M.loaded_segments (0x17f30 : word) = Some W_17f30.
Proof. vm_refl. Qed.
Lemma D_17f30 : decode_any W_17f30 = Some (Jal 1 332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f34 : bv 32 := 0x00050993.
Lemma F_17f34 : fetch_word Ubsan.M.loaded_segments (0x17f34 : word) = Some W_17f34.
Proof. vm_refl. Qed.
Lemma D_17f34 : decode_any W_17f34 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f38 : bv 32 := 0x000a0223.
Lemma F_17f38 : fetch_word Ubsan.M.loaded_segments (0x17f38 : word) = Some W_17f38.
Proof. vm_refl. Qed.
Lemma D_17f38 : decode_any W_17f38 = Some (Store SZ1 20 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f3c : bv 32 := 0x00050593.
Lemma F_17f3c : fetch_word Ubsan.M.loaded_segments (0x17f3c : word) = Some W_17f3c.
Proof. vm_refl. Qed.
Lemma D_17f3c : decode_any W_17f3c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f40 : bv 32 := 0x0b0000ef.
Lemma F_17f40 : fetch_word Ubsan.M.loaded_segments (0x17f40 : word) = Some W_17f40.
Proof. vm_refl. Qed.
Lemma D_17f40 : decode_any W_17f40 = Some (Jal 1 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f44 : bv 32 := 0xfff9899b.
Lemma F_17f44 : fetch_word Ubsan.M.loaded_segments (0x17f44 : word) = Some W_17f44.
Proof. vm_refl. Qed.
Lemma D_17f44 : decode_any W_17f44 = Some (OpImm32 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f48 : bv 32 := 0x0179f463.
Lemma F_17f48 : fetch_word Ubsan.M.loaded_segments (0x17f48 : word) = Some W_17f48.
Proof. vm_refl. Qed.
Lemma D_17f48 : decode_any W_17f48 = Some (Branch BC_GEU 19 23 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f50 : bv 32 := 0xfffa8a9b.
Lemma F_17f50 : fetch_word Ubsan.M.loaded_segments (0x17f50 : word) = Some W_17f50.
Proof. vm_refl. Qed.
Lemma D_17f50 : decode_any W_17f50 = Some (OpImm32 21 21 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f54 : bv 32 := 0xfc0a96e3.
Lemma F_17f54 : fetch_word Ubsan.M.loaded_segments (0x17f54 : word) = Some W_17f54.
Proof. vm_refl. Qed.
Lemma D_17f54 : decode_any W_17f54 = Some (Branch BC_NE 21 0 8140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17fc0 : bv 32 := 0x0002a517.
Lemma F_17fc0 : fetch_word Ubsan.M.loaded_segments (0x17fc0 : word) = Some W_17fc0.
Proof. vm_refl. Qed.
Lemma D_17fc0 : decode_any W_17fc0 = Some (Auipc 10 42, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17fc4 : bv 32 := 0xbe454503.
Lemma F_17fc4 : fetch_word Ubsan.M.loaded_segments (0x17fc4 : word) = Some W_17fc4.
Proof. vm_refl. Qed.
Lemma D_17fc4 : decode_any W_17fc4 = Some (Load SZ1 false 10 10 3044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17fc8 : bv 32 := 0x00051463.
Lemma F_17fc8 : fetch_word Ubsan.M.loaded_segments (0x17fc8 : word) = Some W_17fc8.
Proof. vm_refl. Qed.
Lemma D_17fc8 : decode_any W_17fc8 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17fcc : bv 32 := 0x00008067.
Lemma F_17fcc : fetch_word Ubsan.M.loaded_segments (0x17fcc : word) = Some W_17fcc.
Proof. vm_refl. Qed.
Lemma D_17fcc : decode_any W_17fcc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
