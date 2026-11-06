(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.simdjson.fuzz_utf8.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_b29ac : bv 32 := 0x0004b503.
Lemma F_b29ac : fetch_word Plain.M.loaded_segments (0xb2aa8 : word) = Some W_b29ac.
Proof. vm_refl. Qed.
Lemma D_b29ac : decode_any W_b29ac = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b29b0 : bv 32 := 0x00848493.
Lemma F_b29b0 : fetch_word Plain.M.loaded_segments (0xb2aac : word) = Some W_b29b0.
Proof. vm_refl. Qed.
Lemma D_b29b0 : decode_any W_b29b0 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b29b4 : bv 32 := 0xfe051ce3.
Lemma F_b29b4 : fetch_word Plain.M.loaded_segments (0xb2ab0 : word) = Some W_b29b4.
Proof. vm_refl. Qed.
Lemma D_b29b4 : decode_any W_b29b4 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b29b8 : bv 32 := 0x00051517.
Lemma F_b29b8 : fetch_word Plain.M.loaded_segments (0xb2ab4 : word) = Some W_b29b8.
Proof. vm_refl. Qed.
Lemma D_b29b8 : decode_any W_b29b8 = Some (Auipc 10 81, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b29bc : bv 32 := 0xda450913.
Lemma F_b29bc : fetch_word Plain.M.loaded_segments (0xb2ab8 : word) = Some W_b29bc.
Proof. vm_refl. Qed.
Lemma D_b29bc : decode_any W_b29bc = Some (OpImm ALU_ADD 18 10 3492, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b29c0 : bv 32 := 0x00993423.
Lemma F_b29c0 : fetch_word Plain.M.loaded_segments (0xb2abc : word) = Some W_b29c0.
Proof. vm_refl. Qed.
Lemma D_b29c0 : decode_any W_b29c0 = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b29c4 : bv 32 := 0x0004b583.
Lemma F_b29c4 : fetch_word Plain.M.loaded_segments (0xb2ac0 : word) = Some W_b29c4.
Proof. vm_refl. Qed.
Lemma D_b29c4 : decode_any W_b29c4 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b29c8 : bv 32 := 0x04058c63.
Lemma F_b29c8 : fetch_word Plain.M.loaded_segments (0xb2ac4 : word) = Some W_b29c8.
Proof. vm_refl. Qed.
Lemma D_b29c8 : decode_any W_b29c8 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b29cc : bv 32 := 0x01048493.
Lemma F_b29cc : fetch_word Plain.M.loaded_segments (0xb2ac8 : word) = Some W_b29cc.
Proof. vm_refl. Qed.
Lemma D_b29cc : decode_any W_b29cc = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b29d0 : bv 32 := 0x02500513.
Lemma F_b29d0 : fetch_word Plain.M.loaded_segments (0xb2acc : word) = Some W_b29d0.
Proof. vm_refl. Qed.
Lemma D_b29d0 : decode_any W_b29d0 = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b29d4 : bv 32 := 0x03010613.
Lemma F_b29d4 : fetch_word Plain.M.loaded_segments (0xb2ad0 : word) = Some W_b29d4.
Proof. vm_refl. Qed.
Lemma D_b29d4 : decode_any W_b29d4 = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b29d8 : bv 32 := 0x0100006f.
Lemma F_b29d8 : fetch_word Plain.M.loaded_segments (0xb2ad4 : word) = Some W_b29d8.
Proof. vm_refl. Qed.
Lemma D_b29d8 : decode_any W_b29d8 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b29dc : bv 32 := 0x0004b583.
Lemma F_b29dc : fetch_word Plain.M.loaded_segments (0xb2ad8 : word) = Some W_b29dc.
Proof. vm_refl. Qed.
Lemma D_b29dc : decode_any W_b29dc = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b29e0 : bv 32 := 0x01048493.
Lemma F_b29e0 : fetch_word Plain.M.loaded_segments (0xb2adc : word) = Some W_b29e0.
Proof. vm_refl. Qed.
Lemma D_b29e0 : decode_any W_b29e0 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b29e4 : bv 32 := 0x00058e63.
Lemma F_b29e4 : fetch_word Plain.M.loaded_segments (0xb2ae0 : word) = Some W_b29e4.
Proof. vm_refl. Qed.
Lemma D_b29e4 : decode_any W_b29e4 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b29e8 : bv 32 := 0xfeb56ae3.
Lemma F_b29e8 : fetch_word Plain.M.loaded_segments (0xb2ae4 : word) = Some W_b29e8.
Proof. vm_refl. Qed.
Lemma D_b29e8 : decode_any W_b29e8 = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b29ec : bv 32 := 0xff84b683.
Lemma F_b29ec : fetch_word Plain.M.loaded_segments (0xb2ae8 : word) = Some W_b29ec.
Proof. vm_refl. Qed.
Lemma D_b29ec : decode_any W_b29ec = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b29f0 : bv 32 := 0x00359593.
Lemma F_b29f0 : fetch_word Plain.M.loaded_segments (0xb2aec : word) = Some W_b29f0.
Proof. vm_refl. Qed.
Lemma D_b29f0 : decode_any W_b29f0 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b29f4 : bv 32 := 0x00b605b3.
Lemma F_b29f4 : fetch_word Plain.M.loaded_segments (0xb2af0 : word) = Some W_b29f4.
Proof. vm_refl. Qed.
Lemma D_b29f4 : decode_any W_b29f4 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b29f8 : bv 32 := 0x00d5b023.
Lemma F_b29f8 : fetch_word Plain.M.loaded_segments (0xb2af4 : word) = Some W_b29f8.
Proof. vm_refl. Qed.
Lemma D_b29f8 : decode_any W_b29f8 = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b29fc : bv 32 := 0xfe1ff06f.
Lemma F_b29fc : fetch_word Plain.M.loaded_segments (0xb2af8 : word) = Some W_b29fc.
Proof. vm_refl. Qed.
Lemma D_b29fc : decode_any W_b29fc = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a00 : bv 32 := 0x0b013583.
Lemma F_b2a00 : fetch_word Plain.M.loaded_segments (0xb2afc : word) = Some W_b2a00.
Proof. vm_refl. Qed.
Lemma D_b2a00 : decode_any W_b2a00 = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a04 : bv 32 := 0x13013503.
Lemma F_b2a04 : fetch_word Plain.M.loaded_segments (0xb2b00 : word) = Some W_b2a04.
Proof. vm_refl. Qed.
Lemma D_b2a04 : decode_any W_b2a04 = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a08 : bv 32 := 0x00051617.
Lemma F_b2a08 : fetch_word Plain.M.loaded_segments (0xb2b04 : word) = Some W_b2a08.
Proof. vm_refl. Qed.
Lemma D_b2a08 : decode_any W_b2a08 = Some (Auipc 12 81, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a0c : bv 32 := 0xdab63e23.
Lemma F_b2a0c : fetch_word Plain.M.loaded_segments (0xb2b08 : word) = Some W_b2a0c.
Proof. vm_refl. Qed.
Lemma D_b2a0c : decode_any W_b2a0c = Some (Store SZ8 12 11 3516, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a10 : bv 32 := 0x00050c63.
Lemma F_b2a10 : fetch_word Plain.M.loaded_segments (0xb2b0c : word) = Some W_b2a10.
Proof. vm_refl. Qed.
Lemma D_b2a10 : decode_any W_b2a10 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a14 : bv 32 := 0x00051597.
Lemma F_b2a14 : fetch_word Plain.M.loaded_segments (0xb2b10 : word) = Some W_b2a14.
Proof. vm_refl. Qed.
Lemma D_b2a14 : decode_any W_b2a14 = Some (Auipc 11 81, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a18 : bv 32 := 0xd2a5b823.
Lemma F_b2a18 : fetch_word Plain.M.loaded_segments (0xb2b14 : word) = Some W_b2a18.
Proof. vm_refl. Qed.
Lemma D_b2a18 : decode_any W_b2a18 = Some (Store SZ8 11 10 3376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a1c : bv 32 := 0x00c0006f.
Lemma F_b2a1c : fetch_word Plain.M.loaded_segments (0xb2b18 : word) = Some W_b2a1c.
Proof. vm_refl. Qed.
Lemma D_b2a1c : decode_any W_b2a1c = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a20 : bv 32 := 0x00051517.
Lemma F_b2a20 : fetch_word Plain.M.loaded_segments (0xb2b1c : word) = Some W_b2a20.
Proof. vm_refl. Qed.
Lemma D_b2a20 : decode_any W_b2a20 = Some (Auipc 10 81, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a24 : bv 32 := 0xda053223.
Lemma F_b2a24 : fetch_word Plain.M.loaded_segments (0xb2b20 : word) = Some W_b2a24.
Proof. vm_refl. Qed.
Lemma D_b2a24 : decode_any W_b2a24 = Some (Store SZ8 10 0 3492, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a28 : bv 32 := 0x06013503.
Lemma F_b2a28 : fetch_word Plain.M.loaded_segments (0xb2b24 : word) = Some W_b2a28.
Proof. vm_refl. Qed.
Lemma D_b2a28 : decode_any W_b2a28 = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a2c : bv 32 := 0x02a93823.
Lemma F_b2a2c : fetch_word Plain.M.loaded_segments (0xb2b28 : word) = Some W_b2a2c.
Proof. vm_refl. Qed.
Lemma D_b2a2c : decode_any W_b2a2c = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a30 : bv 32 := 0x00041463.
Lemma F_b2a30 : fetch_word Plain.M.loaded_segments (0xb2b2c : word) = Some W_b2a30.
Proof. vm_refl. Qed.
Lemma D_b2a30 : decode_any W_b2a30 = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a34 : bv 32 := 0x12813403.
Lemma F_b2a34 : fetch_word Plain.M.loaded_segments (0xb2b30 : word) = Some W_b2a34.
Proof. vm_refl. Qed.
Lemma D_b2a34 : decode_any W_b2a34 = Some (Load SZ8 true 8 2 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a38 : bv 32 := 0x00041663.
Lemma F_b2a38 : fetch_word Plain.M.loaded_segments (0xb2b34 : word) = Some W_b2a38.
Proof. vm_refl. Qed.
Lemma D_b2a38 : decode_any W_b2a38 = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a3c : bv 32 := 0xfff5e517.
Lemma F_b2a3c : fetch_word Plain.M.loaded_segments (0xb2b38 : word) = Some W_b2a3c.
Proof. vm_refl. Qed.
Lemma D_b2a3c : decode_any W_b2a3c = Some (Auipc 10 1048414, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a40 : bv 32 := 0x1a350413.
Lemma F_b2a40 : fetch_word Plain.M.loaded_segments (0xb2b3c : word) = Some W_b2a40.
Proof. vm_refl. Qed.
Lemma D_b2a40 : decode_any W_b2a40 = Some (OpImm ALU_ADD 8 10 419, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a44 : bv 32 := 0x0001d517.
Lemma F_b2a44 : fetch_word Plain.M.loaded_segments (0xb2b40 : word) = Some W_b2a44.
Proof. vm_refl. Qed.
Lemma D_b2a44 : decode_any W_b2a44 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a48 : bv 32 := 0x35853583.
Lemma F_b2a48 : fetch_word Plain.M.loaded_segments (0xb2b44 : word) = Some W_b2a48.
Proof. vm_refl. Qed.
Lemma D_b2a48 : decode_any W_b2a48 = Some (Load SZ8 true 11 10 856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a4c : bv 32 := 0x0001d517.
Lemma F_b2a4c : fetch_word Plain.M.loaded_segments (0xb2b48 : word) = Some W_b2a4c.
Proof. vm_refl. Qed.
Lemma D_b2a4c : decode_any W_b2a4c = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a50 : bv 32 := 0x35853503.
Lemma F_b2a50 : fetch_word Plain.M.loaded_segments (0xb2b4c : word) = Some W_b2a50.
Proof. vm_refl. Qed.
Lemma D_b2a50 : decode_any W_b2a50 = Some (Load SZ8 true 10 10 856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a54 : bv 32 := 0x0085b023.
Lemma F_b2a54 : fetch_word Plain.M.loaded_segments (0xb2b50 : word) = Some W_b2a54.
Proof. vm_refl. Qed.
Lemma D_b2a54 : decode_any W_b2a54 = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a58 : bv 32 := 0x00140593.
Lemma F_b2a58 : fetch_word Plain.M.loaded_segments (0xb2b54 : word) = Some W_b2a58.
Proof. vm_refl. Qed.
Lemma D_b2a58 : decode_any W_b2a58 = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a5c : bv 32 := 0x00853023.
Lemma F_b2a5c : fetch_word Plain.M.loaded_segments (0xb2b58 : word) = Some W_b2a5c.
Proof. vm_refl. Qed.
Lemma D_b2a5c : decode_any W_b2a5c = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a60 : bv 32 := 0x02f00613.
Lemma F_b2a60 : fetch_word Plain.M.loaded_segments (0xb2b5c : word) = Some W_b2a60.
Proof. vm_refl. Qed.
Lemma D_b2a60 : decode_any W_b2a60 = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a64 : bv 32 := 0x00c0006f.
Lemma F_b2a64 : fetch_word Plain.M.loaded_segments (0xb2b60 : word) = Some W_b2a64.
Proof. vm_refl. Qed.
Lemma D_b2a64 : decode_any W_b2a64 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a68 : bv 32 := 0x00b53023.
Lemma F_b2a68 : fetch_word Plain.M.loaded_segments (0xb2b64 : word) = Some W_b2a68.
Proof. vm_refl. Qed.
Lemma D_b2a68 : decode_any W_b2a68 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a6c : bv 32 := 0x00158593.
Lemma F_b2a6c : fetch_word Plain.M.loaded_segments (0xb2b68 : word) = Some W_b2a6c.
Proof. vm_refl. Qed.
Lemma D_b2a6c : decode_any W_b2a6c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a70 : bv 32 := 0xfff5c683.
Lemma F_b2a70 : fetch_word Plain.M.loaded_segments (0xb2b6c : word) = Some W_b2a70.
Proof. vm_refl. Qed.
Lemma D_b2a70 : decode_any W_b2a70 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a74 : bv 32 := 0xfec68ae3.
Lemma F_b2a74 : fetch_word Plain.M.loaded_segments (0xb2b70 : word) = Some W_b2a74.
Proof. vm_refl. Qed.
Lemma D_b2a74 : decode_any W_b2a74 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b2a78 : bv 32 := 0xfe069ae3.
Lemma F_b2a78 : fetch_word Plain.M.loaded_segments (0xb2b74 : word) = Some W_b2a78.
Proof. vm_refl. Qed.
Lemma D_b2a78 : decode_any W_b2a78 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
