(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_6afc8 : bv 32 := 0xf9010113.
Lemma F_6afc8 : fetch_word Plain.M.loaded_segments (0x6afc8 : word) = Some W_6afc8.
Proof. vm_refl. Qed.
Lemma D_6afc8 : decode_any W_6afc8 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6afcc : bv 32 := 0x06113423.
Lemma F_6afcc : fetch_word Plain.M.loaded_segments (0x6afcc : word) = Some W_6afcc.
Proof. vm_refl. Qed.
Lemma D_6afcc : decode_any W_6afcc = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6afd0 : bv 32 := 0x06813023.
Lemma F_6afd0 : fetch_word Plain.M.loaded_segments (0x6afd0 : word) = Some W_6afd0.
Proof. vm_refl. Qed.
Lemma D_6afd0 : decode_any W_6afd0 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6afd4 : bv 32 := 0x04913c23.
Lemma F_6afd4 : fetch_word Plain.M.loaded_segments (0x6afd4 : word) = Some W_6afd4.
Proof. vm_refl. Qed.
Lemma D_6afd4 : decode_any W_6afd4 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6afd8 : bv 32 := 0x05213823.
Lemma F_6afd8 : fetch_word Plain.M.loaded_segments (0x6afd8 : word) = Some W_6afd8.
Proof. vm_refl. Qed.
Lemma D_6afd8 : decode_any W_6afd8 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6afdc : bv 32 := 0x05313423.
Lemma F_6afdc : fetch_word Plain.M.loaded_segments (0x6afdc : word) = Some W_6afdc.
Proof. vm_refl. Qed.
Lemma D_6afdc : decode_any W_6afdc = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6afe0 : bv 32 := 0x05413023.
Lemma F_6afe0 : fetch_word Plain.M.loaded_segments (0x6afe0 : word) = Some W_6afe0.
Proof. vm_refl. Qed.
Lemma D_6afe0 : decode_any W_6afe0 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6afe4 : bv 32 := 0x03513c23.
Lemma F_6afe4 : fetch_word Plain.M.loaded_segments (0x6afe4 : word) = Some W_6afe4.
Proof. vm_refl. Qed.
Lemma D_6afe4 : decode_any W_6afe4 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6afe8 : bv 32 := 0x03613823.
Lemma F_6afe8 : fetch_word Plain.M.loaded_segments (0x6afe8 : word) = Some W_6afe8.
Proof. vm_refl. Qed.
Lemma D_6afe8 : decode_any W_6afe8 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6afec : bv 32 := 0x00060413.
Lemma F_6afec : fetch_word Plain.M.loaded_segments (0x6afec : word) = Some W_6afec.
Proof. vm_refl. Qed.
Lemma D_6afec : decode_any W_6afec = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aff0 : bv 32 := 0x00050493.
Lemma F_6aff0 : fetch_word Plain.M.loaded_segments (0x6aff0 : word) = Some W_6aff0.
Proof. vm_refl. Qed.
Lemma D_6aff0 : decode_any W_6aff0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aff4 : bv 32 := 0x00015517.
Lemma F_6aff4 : fetch_word Plain.M.loaded_segments (0x6aff4 : word) = Some W_6aff4.
Proof. vm_refl. Qed.
Lemma D_6aff4 : decode_any W_6aff4 = Some (Auipc 10 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aff8 : bv 32 := 0x81453a83.
Lemma F_6aff8 : fetch_word Plain.M.loaded_segments (0x6aff8 : word) = Some W_6aff8.
Proof. vm_refl. Qed.
Lemma D_6aff8 : decode_any W_6aff8 = Some (Load SZ8 true 21 10 2068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6affc : bv 32 := 0x000ab503.
Lemma F_6affc : fetch_word Plain.M.loaded_segments (0x6affc : word) = Some W_6affc.
Proof. vm_refl. Qed.
Lemma D_6affc : decode_any W_6affc = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b000 : bv 32 := 0x02a13423.
Lemma F_6b000 : fetch_word Plain.M.loaded_segments (0x6b000 : word) = Some W_6b000.
Proof. vm_refl. Qed.
Lemma D_6b000 : decode_any W_6b000 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b004 : bv 32 := 0x0284b503.
Lemma F_6b004 : fetch_word Plain.M.loaded_segments (0x6b004 : word) = Some W_6b004.
Proof. vm_refl. Qed.
Lemma D_6b004 : decode_any W_6b004 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b008 : bv 32 := 0x0384b603.
Lemma F_6b008 : fetch_word Plain.M.loaded_segments (0x6b008 : word) = Some W_6b008.
Proof. vm_refl. Qed.
Lemma D_6b008 : decode_any W_6b008 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b00c : bv 32 := 0x40c50b33.
Lemma F_6b00c : fetch_word Plain.M.loaded_segments (0x6b00c : word) = Some W_6b00c.
Proof. vm_refl. Qed.
Lemma D_6b00c : decode_any W_6b00c = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b010 : bv 32 := 0x00c546b3.
Lemma F_6b010 : fetch_word Plain.M.loaded_segments (0x6b010 : word) = Some W_6b010.
Proof. vm_refl. Qed.
Lemma D_6b010 : decode_any W_6b010 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b014 : bv 32 := 0x00c13423.
Lemma F_6b014 : fetch_word Plain.M.loaded_segments (0x6b014 : word) = Some W_6b014.
Proof. vm_refl. Qed.
Lemma D_6b014 : decode_any W_6b014 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b018 : bv 32 := 0x01613823.
Lemma F_6b018 : fetch_word Plain.M.loaded_segments (0x6b018 : word) = Some W_6b018.
Proof. vm_refl. Qed.
Lemma D_6b018 : decode_any W_6b018 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b01c : bv 32 := 0x00b13c23.
Lemma F_6b01c : fetch_word Plain.M.loaded_segments (0x6b01c : word) = Some W_6b01c.
Proof. vm_refl. Qed.
Lemma D_6b01c : decode_any W_6b01c = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b020 : bv 32 := 0x02813023.
Lemma F_6b020 : fetch_word Plain.M.loaded_segments (0x6b020 : word) = Some W_6b020.
Proof. vm_refl. Qed.
Lemma D_6b020 : decode_any W_6b020 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b024 : bv 32 := 0x008b0b33.
Lemma F_6b024 : fetch_word Plain.M.loaded_segments (0x6b024 : word) = Some W_6b024.
Proof. vm_refl. Qed.
Lemma D_6b024 : decode_any W_6b024 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b028 : bv 32 := 0x00d03933.
Lemma F_6b028 : fetch_word Plain.M.loaded_segments (0x6b028 : word) = Some W_6b028.
Proof. vm_refl. Qed.
Lemma D_6b028 : decode_any W_6b028 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b02c : bv 32 := 0x00c50663.
Lemma F_6b02c : fetch_word Plain.M.loaded_segments (0x6b02c : word) = Some W_6b02c.
Proof. vm_refl. Qed.
Lemma D_6b02c : decode_any W_6b02c = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b030 : bv 32 := 0x00810993.
Lemma F_6b030 : fetch_word Plain.M.loaded_segments (0x6b030 : word) = Some W_6b030.
Proof. vm_refl. Qed.
Lemma D_6b030 : decode_any W_6b030 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b034 : bv 32 := 0x0080006f.
Lemma F_6b034 : fetch_word Plain.M.loaded_segments (0x6b034 : word) = Some W_6b034.
Proof. vm_refl. Qed.
Lemma D_6b034 : decode_any W_6b034 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b038 : bv 32 := 0x01810993.
Lemma F_6b038 : fetch_word Plain.M.loaded_segments (0x6b038 : word) = Some W_6b038.
Proof. vm_refl. Qed.
Lemma D_6b038 : decode_any W_6b038 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b03c : bv 32 := 0x0784a503.
Lemma F_6b03c : fetch_word Plain.M.loaded_segments (0x6b03c : word) = Some W_6b03c.
Proof. vm_refl. Qed.
Lemma D_6b03c : decode_any W_6b03c = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b040 : bv 32 := 0x00190913.
Lemma F_6b040 : fetch_word Plain.M.loaded_segments (0x6b040 : word) = Some W_6b040.
Proof. vm_refl. Qed.
Lemma D_6b040 : decode_any W_6b040 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b044 : bv 32 := 0x04200893.
Lemma F_6b044 : fetch_word Plain.M.loaded_segments (0x6b044 : word) = Some W_6b044.
Proof. vm_refl. Qed.
Lemma D_6b044 : decode_any W_6b044 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b048 : bv 32 := 0x00098593.
Lemma F_6b048 : fetch_word Plain.M.loaded_segments (0x6b048 : word) = Some W_6b048.
Proof. vm_refl. Qed.
Lemma D_6b048 : decode_any W_6b048 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b04c : bv 32 := 0x00090613.
Lemma F_6b04c : fetch_word Plain.M.loaded_segments (0x6b04c : word) = Some W_6b04c.
Proof. vm_refl. Qed.
Lemma D_6b04c : decode_any W_6b04c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b050 : bv 32 := 0x00000073.
Lemma F_6b050 : fetch_word Plain.M.loaded_segments (0x6b050 : word) = Some W_6b050.
Proof. vm_refl. Qed.
Lemma D_6b050 : decode_any W_6b050 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_6b050 : is_ecall W_6b050 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b054 : bv 32 := 0xb7dfc0ef.
Lemma F_6b054 : fetch_word Plain.M.loaded_segments (0x6b054 : word) = Some W_6b054.
Proof. vm_refl. Qed.
Lemma D_6b054 : decode_any W_6b054 = Some (Jal 1 2083708, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b058 : bv 32 := 0x09651863.
Lemma F_6b058 : fetch_word Plain.M.loaded_segments (0x6b058 : word) = Some W_6b058.
Proof. vm_refl. Qed.
Lemma D_6b058 : decode_any W_6b058 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b05c : bv 32 := 0x0584b503.
Lemma F_6b05c : fetch_word Plain.M.loaded_segments (0x6b05c : word) = Some W_6b05c.
Proof. vm_refl. Qed.
Lemma D_6b05c : decode_any W_6b05c = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b060 : bv 32 := 0x0604b583.
Lemma F_6b060 : fetch_word Plain.M.loaded_segments (0x6b060 : word) = Some W_6b060.
Proof. vm_refl. Qed.
Lemma D_6b060 : decode_any W_6b060 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b064 : bv 32 := 0x00b505b3.
Lemma F_6b064 : fetch_word Plain.M.loaded_segments (0x6b064 : word) = Some W_6b064.
Proof. vm_refl. Qed.
Lemma D_6b064 : decode_any W_6b064 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b068 : bv 32 := 0x02b4b023.
Lemma F_6b068 : fetch_word Plain.M.loaded_segments (0x6b068 : word) = Some W_6b068.
Proof. vm_refl. Qed.
Lemma D_6b068 : decode_any W_6b068 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b06c : bv 32 := 0x02a4b423.
Lemma F_6b06c : fetch_word Plain.M.loaded_segments (0x6b06c : word) = Some W_6b06c.
Proof. vm_refl. Qed.
Lemma D_6b06c : decode_any W_6b06c = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b070 : bv 32 := 0x02a4bc23.
Lemma F_6b070 : fetch_word Plain.M.loaded_segments (0x6b070 : word) = Some W_6b070.
Proof. vm_refl. Qed.
Lemma D_6b070 : decode_any W_6b070 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b074 : bv 32 := 0x00040513.
Lemma F_6b074 : fetch_word Plain.M.loaded_segments (0x6b074 : word) = Some W_6b074.
Proof. vm_refl. Qed.
Lemma D_6b074 : decode_any W_6b074 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b078 : bv 32 := 0x000ab583.
Lemma F_6b078 : fetch_word Plain.M.loaded_segments (0x6b078 : word) = Some W_6b078.
Proof. vm_refl. Qed.
Lemma D_6b078 : decode_any W_6b078 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b07c : bv 32 := 0x02813603.
Lemma F_6b07c : fetch_word Plain.M.loaded_segments (0x6b07c : word) = Some W_6b07c.
Proof. vm_refl. Qed.
Lemma D_6b07c : decode_any W_6b07c = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b080 : bv 32 := 0x0cc59a63.
Lemma F_6b080 : fetch_word Plain.M.loaded_segments (0x6b080 : word) = Some W_6b080.
Proof. vm_refl. Qed.
Lemma D_6b080 : decode_any W_6b080 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b084 : bv 32 := 0x06813083.
Lemma F_6b084 : fetch_word Plain.M.loaded_segments (0x6b084 : word) = Some W_6b084.
Proof. vm_refl. Qed.
Lemma D_6b084 : decode_any W_6b084 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b088 : bv 32 := 0x06013403.
Lemma F_6b088 : fetch_word Plain.M.loaded_segments (0x6b088 : word) = Some W_6b088.
Proof. vm_refl. Qed.
Lemma D_6b088 : decode_any W_6b088 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b08c : bv 32 := 0x05813483.
Lemma F_6b08c : fetch_word Plain.M.loaded_segments (0x6b08c : word) = Some W_6b08c.
Proof. vm_refl. Qed.
Lemma D_6b08c : decode_any W_6b08c = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b090 : bv 32 := 0x05013903.
Lemma F_6b090 : fetch_word Plain.M.loaded_segments (0x6b090 : word) = Some W_6b090.
Proof. vm_refl. Qed.
Lemma D_6b090 : decode_any W_6b090 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b094 : bv 32 := 0x04813983.
Lemma F_6b094 : fetch_word Plain.M.loaded_segments (0x6b094 : word) = Some W_6b094.
Proof. vm_refl. Qed.
Lemma D_6b094 : decode_any W_6b094 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b098 : bv 32 := 0x04013a03.
Lemma F_6b098 : fetch_word Plain.M.loaded_segments (0x6b098 : word) = Some W_6b098.
Proof. vm_refl. Qed.
Lemma D_6b098 : decode_any W_6b098 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b09c : bv 32 := 0x03813a83.
Lemma F_6b09c : fetch_word Plain.M.loaded_segments (0x6b09c : word) = Some W_6b09c.
Proof. vm_refl. Qed.
Lemma D_6b09c : decode_any W_6b09c = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b0a0 : bv 32 := 0x03013b03.
Lemma F_6b0a0 : fetch_word Plain.M.loaded_segments (0x6b0a0 : word) = Some W_6b0a0.
Proof. vm_refl. Qed.
Lemma D_6b0a0 : decode_any W_6b0a0 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b0a4 : bv 32 := 0x07010113.
Lemma F_6b0a4 : fetch_word Plain.M.loaded_segments (0x6b0a4 : word) = Some W_6b0a4.
Proof. vm_refl. Qed.
Lemma D_6b0a4 : decode_any W_6b0a4 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b0a8 : bv 32 := 0x00008067.
Lemma F_6b0a8 : fetch_word Plain.M.loaded_segments (0x6b0a8 : word) = Some W_6b0a8.
Proof. vm_refl. Qed.
Lemma D_6b0a8 : decode_any W_6b0a8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b0ac : bv 32 := 0x00800713.
Lemma F_6b0ac : fetch_word Plain.M.loaded_segments (0x6b0ac : word) = Some W_6b0ac.
Proof. vm_refl. Qed.
Lemma D_6b0ac : decode_any W_6b0ac = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b0b0 : bv 32 := 0x000a0593.
Lemma F_6b0b0 : fetch_word Plain.M.loaded_segments (0x6b0b0 : word) = Some W_6b0b0.
Proof. vm_refl. Qed.
Lemma D_6b0b0 : decode_any W_6b0b0 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b0b4 : bv 32 := 0x00e98733.
Lemma F_6b0b4 : fetch_word Plain.M.loaded_segments (0x6b0b4 : word) = Some W_6b0b4.
Proof. vm_refl. Qed.
Lemma D_6b0b4 : decode_any W_6b0b4 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b0b8 : bv 32 := 0x00073783.
Lemma F_6b0b8 : fetch_word Plain.M.loaded_segments (0x6b0b8 : word) = Some W_6b0b8.
Proof. vm_refl. Qed.
Lemma D_6b0b8 : decode_any W_6b0b8 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b0bc : bv 32 := 0x40ab0b33.
Lemma F_6b0bc : fetch_word Plain.M.loaded_segments (0x6b0bc : word) = Some W_6b0bc.
Proof. vm_refl. Qed.
Lemma D_6b0bc : decode_any W_6b0bc = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b0c0 : bv 32 := 0x0784a503.
Lemma F_6b0c0 : fetch_word Plain.M.loaded_segments (0x6b0c0 : word) = Some W_6b0c0.
Proof. vm_refl. Qed.
Lemma D_6b0c0 : decode_any W_6b0c0 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b0c4 : bv 32 := 0x40c9093b.
Lemma F_6b0c4 : fetch_word Plain.M.loaded_segments (0x6b0c4 : word) = Some W_6b0c4.
Proof. vm_refl. Qed.
Lemma D_6b0c4 : decode_any W_6b0c4 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b0c8 : bv 32 := 0x40d787b3.
Lemma F_6b0c8 : fetch_word Plain.M.loaded_segments (0x6b0c8 : word) = Some W_6b0c8.
Proof. vm_refl. Qed.
Lemma D_6b0c8 : decode_any W_6b0c8 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b0cc : bv 32 := 0x00f73023.
Lemma F_6b0cc : fetch_word Plain.M.loaded_segments (0x6b0cc : word) = Some W_6b0cc.
Proof. vm_refl. Qed.
Lemma D_6b0cc : decode_any W_6b0cc = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b0d0 : bv 32 := 0x04200893.
Lemma F_6b0d0 : fetch_word Plain.M.loaded_segments (0x6b0d0 : word) = Some W_6b0d0.
Proof. vm_refl. Qed.
Lemma D_6b0d0 : decode_any W_6b0d0 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b0d4 : bv 32 := 0x00090613.
Lemma F_6b0d4 : fetch_word Plain.M.loaded_segments (0x6b0d4 : word) = Some W_6b0d4.
Proof. vm_refl. Qed.
Lemma D_6b0d4 : decode_any W_6b0d4 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b0d8 : bv 32 := 0x00000073.
Lemma F_6b0d8 : fetch_word Plain.M.loaded_segments (0x6b0d8 : word) = Some W_6b0d8.
Proof. vm_refl. Qed.
Lemma D_6b0d8 : decode_any W_6b0d8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_6b0d8 : is_ecall W_6b0d8 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b0dc : bv 32 := 0xaf5fc0ef.
Lemma F_6b0dc : fetch_word Plain.M.loaded_segments (0x6b0dc : word) = Some W_6b0dc.
Proof. vm_refl. Qed.
Lemma D_6b0dc : decode_any W_6b0dc = Some (Jal 1 2083572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b0e0 : bv 32 := 0x000a0993.
Lemma F_6b0e0 : fetch_word Plain.M.loaded_segments (0x6b0e0 : word) = Some W_6b0e0.
Proof. vm_refl. Qed.
Lemma D_6b0e0 : decode_any W_6b0e0 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b0e4 : bv 32 := 0xf7650ce3.
Lemma F_6b0e4 : fetch_word Plain.M.loaded_segments (0x6b0e4 : word) = Some W_6b0e4.
Proof. vm_refl. Qed.
Lemma D_6b0e4 : decode_any W_6b0e4 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b0e8 : bv 32 := 0x02054c63.
Lemma F_6b0e8 : fetch_word Plain.M.loaded_segments (0x6b0e8 : word) = Some W_6b0e8.
Proof. vm_refl. Qed.
Lemma D_6b0e8 : decode_any W_6b0e8 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b0ec : bv 32 := 0x0089b583.
Lemma F_6b0ec : fetch_word Plain.M.loaded_segments (0x6b0ec : word) = Some W_6b0ec.
Proof. vm_refl. Qed.
Lemma D_6b0ec : decode_any W_6b0ec = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b0f0 : bv 32 := 0x00a5b633.
Lemma F_6b0f0 : fetch_word Plain.M.loaded_segments (0x6b0f0 : word) = Some W_6b0f0.
Proof. vm_refl. Qed.
Lemma D_6b0f0 : decode_any W_6b0f0 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b0f4 : bv 32 := 0x00461a13.
Lemma F_6b0f4 : fetch_word Plain.M.loaded_segments (0x6b0f4 : word) = Some W_6b0f4.
Proof. vm_refl. Qed.
Lemma D_6b0f4 : decode_any W_6b0f4 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b0f8 : bv 32 := 0x01498a33.
Lemma F_6b0f8 : fetch_word Plain.M.loaded_segments (0x6b0f8 : word) = Some W_6b0f8.
Proof. vm_refl. Qed.
Lemma D_6b0f8 : decode_any W_6b0f8 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b0fc : bv 32 := 0x000a3703.
Lemma F_6b0fc : fetch_word Plain.M.loaded_segments (0x6b0fc : word) = Some W_6b0fc.
Proof. vm_refl. Qed.
Lemma D_6b0fc : decode_any W_6b0fc = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b100 : bv 32 := 0x40c006b3.
Lemma F_6b100 : fetch_word Plain.M.loaded_segments (0x6b100 : word) = Some W_6b100.
Proof. vm_refl. Qed.
Lemma D_6b100 : decode_any W_6b100 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b104 : bv 32 := 0x00b6f6b3.
Lemma F_6b104 : fetch_word Plain.M.loaded_segments (0x6b104 : word) = Some W_6b104.
Proof. vm_refl. Qed.
Lemma D_6b104 : decode_any W_6b104 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b108 : bv 32 := 0x40d506b3.
Lemma F_6b108 : fetch_word Plain.M.loaded_segments (0x6b108 : word) = Some W_6b108.
Proof. vm_refl. Qed.
Lemma D_6b108 : decode_any W_6b108 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b10c : bv 32 := 0x00d70733.
Lemma F_6b10c : fetch_word Plain.M.loaded_segments (0x6b10c : word) = Some W_6b10c.
Proof. vm_refl. Qed.
Lemma D_6b10c : decode_any W_6b10c = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b110 : bv 32 := 0x00ea3023.
Lemma F_6b110 : fetch_word Plain.M.loaded_segments (0x6b110 : word) = Some W_6b110.
Proof. vm_refl. Qed.
Lemma D_6b110 : decode_any W_6b110 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b114 : bv 32 := 0xf8a5fce3.
Lemma F_6b114 : fetch_word Plain.M.loaded_segments (0x6b114 : word) = Some W_6b114.
Proof. vm_refl. Qed.
Lemma D_6b114 : decode_any W_6b114 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b118 : bv 32 := 0x01800713.
Lemma F_6b118 : fetch_word Plain.M.loaded_segments (0x6b118 : word) = Some W_6b118.
Proof. vm_refl. Qed.
Lemma D_6b118 : decode_any W_6b118 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b11c : bv 32 := 0xf95ff06f.
Lemma F_6b11c : fetch_word Plain.M.loaded_segments (0x6b11c : word) = Some W_6b11c.
Proof. vm_refl. Qed.
Lemma D_6b11c : decode_any W_6b11c = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b120 : bv 32 := 0x00000513.
Lemma F_6b120 : fetch_word Plain.M.loaded_segments (0x6b120 : word) = Some W_6b120.
Proof. vm_refl. Qed.
Lemma D_6b120 : decode_any W_6b120 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b124 : bv 32 := 0x0004a583.
Lemma F_6b124 : fetch_word Plain.M.loaded_segments (0x6b124 : word) = Some W_6b124.
Proof. vm_refl. Qed.
Lemma D_6b124 : decode_any W_6b124 = Some (Load SZ4 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b128 : bv 32 := 0x0009091b.
Lemma F_6b128 : fetch_word Plain.M.loaded_segments (0x6b128 : word) = Some W_6b128.
Proof. vm_refl. Qed.
Lemma D_6b128 : decode_any W_6b128 = Some (OpImm32 18 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b12c : bv 32 := 0x00200613.
Lemma F_6b12c : fetch_word Plain.M.loaded_segments (0x6b12c : word) = Some W_6b12c.
Proof. vm_refl. Qed.
Lemma D_6b12c : decode_any W_6b12c = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b130 : bv 32 := 0x0205e593.
Lemma F_6b130 : fetch_word Plain.M.loaded_segments (0x6b130 : word) = Some W_6b130.
Proof. vm_refl. Qed.
Lemma D_6b130 : decode_any W_6b130 = Some (OpImm ALU_OR 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b134 : bv 32 := 0x00b4a023.
Lemma F_6b134 : fetch_word Plain.M.loaded_segments (0x6b134 : word) = Some W_6b134.
Proof. vm_refl. Qed.
Lemma D_6b134 : decode_any W_6b134 = Some (Store SZ4 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b138 : bv 32 := 0x0204b023.
Lemma F_6b138 : fetch_word Plain.M.loaded_segments (0x6b138 : word) = Some W_6b138.
Proof. vm_refl. Qed.
Lemma D_6b138 : decode_any W_6b138 = Some (Store SZ8 9 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b13c : bv 32 := 0x0204b423.
Lemma F_6b13c : fetch_word Plain.M.loaded_segments (0x6b13c : word) = Some W_6b13c.
Proof. vm_refl. Qed.
Lemma D_6b13c : decode_any W_6b13c = Some (Store SZ8 9 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b140 : bv 32 := 0x0204bc23.
Lemma F_6b140 : fetch_word Plain.M.loaded_segments (0x6b140 : word) = Some W_6b140.
Proof. vm_refl. Qed.
Lemma D_6b140 : decode_any W_6b140 = Some (Store SZ8 9 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b144 : bv 32 := 0xf2c90ae3.
Lemma F_6b144 : fetch_word Plain.M.loaded_segments (0x6b144 : word) = Some W_6b144.
Proof. vm_refl. Qed.
Lemma D_6b144 : decode_any W_6b144 = Some (Branch BC_EQ 18 12 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b148 : bv 32 := 0x0089b503.
Lemma F_6b148 : fetch_word Plain.M.loaded_segments (0x6b148 : word) = Some W_6b148.
Proof. vm_refl. Qed.
Lemma D_6b148 : decode_any W_6b148 = Some (Load SZ8 true 10 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b14c : bv 32 := 0x40a40533.
Lemma F_6b14c : fetch_word Plain.M.loaded_segments (0x6b14c : word) = Some W_6b14c.
Proof. vm_refl. Qed.
Lemma D_6b14c : decode_any W_6b14c = Some (Op ALU_SUB 10 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b150 : bv 32 := 0xf29ff06f.
Lemma F_6b150 : fetch_word Plain.M.loaded_segments (0x6b150 : word) = Some W_6b150.
Proof. vm_refl. Qed.
Lemma D_6b150 : decode_any W_6b150 = Some (Jal 0 2096936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b154 : bv 32 := 0xc10fc0ef.
Lemma F_6b154 : fetch_word Plain.M.loaded_segments (0x6b154 : word) = Some W_6b154.
Proof. vm_refl. Qed.
Lemma D_6b154 : decode_any W_6b154 = Some (Jal 1 2081808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b158 : bv 32 := 0x07852503.
Lemma F_6b158 : fetch_word Plain.M.loaded_segments (0x6b158 : word) = Some W_6b158.
Proof. vm_refl. Qed.
Lemma D_6b158 : decode_any W_6b158 = Some (Load SZ4 true 10 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b15c : bv 32 := 0x5c50d06f.
Lemma F_6b15c : fetch_word Plain.M.loaded_segments (0x6b15c : word) = Some W_6b15c.
Proof. vm_refl. Qed.
Lemma D_6b15c : decode_any W_6b15c = Some (Jal 0 56772, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b160 : bv 32 := 0xfe010113.
Lemma F_6b160 : fetch_word Plain.M.loaded_segments (0x6b160 : word) = Some W_6b160.
Proof. vm_refl. Qed.
Lemma D_6b160 : decode_any W_6b160 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b164 : bv 32 := 0x00113c23.
Lemma F_6b164 : fetch_word Plain.M.loaded_segments (0x6b164 : word) = Some W_6b164.
Proof. vm_refl. Qed.
Lemma D_6b164 : decode_any W_6b164 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b168 : bv 32 := 0x00813823.
Lemma F_6b168 : fetch_word Plain.M.loaded_segments (0x6b168 : word) = Some W_6b168.
Proof. vm_refl. Qed.
Lemma D_6b168 : decode_any W_6b168 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b16c : bv 32 := 0x00014697.
Lemma F_6b16c : fetch_word Plain.M.loaded_segments (0x6b16c : word) = Some W_6b16c.
Proof. vm_refl. Qed.
Lemma D_6b16c : decode_any W_6b16c = Some (Auipc 13 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b170 : bv 32 := 0x69c6b403.
Lemma F_6b170 : fetch_word Plain.M.loaded_segments (0x6b170 : word) = Some W_6b170.
Proof. vm_refl. Qed.
Lemma D_6b170 : decode_any W_6b170 = Some (Load SZ8 true 8 13 1692, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b174 : bv 32 := 0x00043683.
Lemma F_6b174 : fetch_word Plain.M.loaded_segments (0x6b174 : word) = Some W_6b174.
Proof. vm_refl. Qed.
Lemma D_6b174 : decode_any W_6b174 = Some (Load SZ8 true 13 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b178 : bv 32 := 0x00d13423.
Lemma F_6b178 : fetch_word Plain.M.loaded_segments (0x6b178 : word) = Some W_6b178.
Proof. vm_refl. Qed.
Lemma D_6b178 : decode_any W_6b178 = Some (Store SZ8 2 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b17c : bv 32 := 0x00054683.
Lemma F_6b17c : fetch_word Plain.M.loaded_segments (0x6b17c : word) = Some W_6b17c.
Proof. vm_refl. Qed.
Lemma D_6b17c : decode_any W_6b17c = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b180 : bv 32 := 0x00000717.
Lemma F_6b180 : fetch_word Plain.M.loaded_segments (0x6b180 : word) = Some W_6b180.
Proof. vm_refl. Qed.
Lemma D_6b180 : decode_any W_6b180 = Some (Auipc 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b184 : bv 32 := 0xe4870713.
Lemma F_6b184 : fetch_word Plain.M.loaded_segments (0x6b184 : word) = Some W_6b184.
Proof. vm_refl. Qed.
Lemma D_6b184 : decode_any W_6b184 = Some (OpImm ALU_ADD 14 14 3656, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b188 : bv 32 := 0x0406f693.
Lemma F_6b188 : fetch_word Plain.M.loaded_segments (0x6b188 : word) = Some W_6b188.
Proof. vm_refl. Qed.
Lemma D_6b188 : decode_any W_6b188 = Some (OpImm ALU_AND 13 13 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b18c : bv 32 := 0x04e53423.
Lemma F_6b18c : fetch_word Plain.M.loaded_segments (0x6b18c : word) = Some W_6b18c.
Proof. vm_refl. Qed.
Lemma D_6b18c : decode_any W_6b18c = Some (Store SZ8 10 14 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b190 : bv 32 := 0x04069663.
Lemma F_6b190 : fetch_word Plain.M.loaded_segments (0x6b190 : word) = Some W_6b190.
Proof. vm_refl. Qed.
Lemma D_6b190 : decode_any W_6b190 = Some (Branch BC_NE 13 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b194 : bv 32 := 0x07852683.
Lemma F_6b194 : fetch_word Plain.M.loaded_segments (0x6b194 : word) = Some W_6b194.
Proof. vm_refl. Qed.
Lemma D_6b194 : decode_any W_6b194 = Some (Load SZ4 true 13 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b198 : bv 32 := 0x00005737.
Lemma F_6b198 : fetch_word Plain.M.loaded_segments (0x6b198 : word) = Some W_6b198.
Proof. vm_refl. Qed.
Lemma D_6b198 : decode_any W_6b198 = Some (Lui 14 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b19c : bv 32 := 0x4137071b.
Lemma F_6b19c : fetch_word Plain.M.loaded_segments (0x6b19c : word) = Some W_6b19c.
Proof. vm_refl. Qed.
Lemma D_6b19c : decode_any W_6b19c = Some (OpImm32 14 14 1043, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1a0 : bv 32 := 0x01d00893.
Lemma F_6b1a0 : fetch_word Plain.M.loaded_segments (0x6b1a0 : word) = Some W_6b1a0.
Proof. vm_refl. Qed.
Lemma D_6b1a0 : decode_any W_6b1a0 = Some (OpImm ALU_ADD 17 0 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1a4 : bv 32 := 0x00060793.
Lemma F_6b1a4 : fetch_word Plain.M.loaded_segments (0x6b1a4 : word) = Some W_6b1a4.
Proof. vm_refl. Qed.
Lemma D_6b1a4 : decode_any W_6b1a4 = Some (OpImm ALU_ADD 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1a8 : bv 32 := 0x00010613.
Lemma F_6b1a8 : fetch_word Plain.M.loaded_segments (0x6b1a8 : word) = Some W_6b1a8.
Proof. vm_refl. Qed.
Lemma D_6b1a8 : decode_any W_6b1a8 = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1ac : bv 32 := 0x00050813.
Lemma F_6b1ac : fetch_word Plain.M.loaded_segments (0x6b1ac : word) = Some W_6b1ac.
Proof. vm_refl. Qed.
Lemma D_6b1ac : decode_any W_6b1ac = Some (OpImm ALU_ADD 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1b0 : bv 32 := 0x00068513.
Lemma F_6b1b0 : fetch_word Plain.M.loaded_segments (0x6b1b0 : word) = Some W_6b1b0.
Proof. vm_refl. Qed.
Lemma D_6b1b0 : decode_any W_6b1b0 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1b4 : bv 32 := 0x00058693.
Lemma F_6b1b4 : fetch_word Plain.M.loaded_segments (0x6b1b4 : word) = Some W_6b1b4.
Proof. vm_refl. Qed.
Lemma D_6b1b4 : decode_any W_6b1b4 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1b8 : bv 32 := 0x00070593.
Lemma F_6b1b8 : fetch_word Plain.M.loaded_segments (0x6b1b8 : word) = Some W_6b1b8.
Proof. vm_refl. Qed.
Lemma D_6b1b8 : decode_any W_6b1b8 = Some (OpImm ALU_ADD 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1bc : bv 32 := 0x00000073.
Lemma F_6b1bc : fetch_word Plain.M.loaded_segments (0x6b1bc : word) = Some W_6b1bc.
Proof. vm_refl. Qed.
Lemma D_6b1bc : decode_any W_6b1bc = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_6b1bc : is_ecall W_6b1bc = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b1c0 : bv 32 := 0x00068593.
Lemma F_6b1c0 : fetch_word Plain.M.loaded_segments (0x6b1c0 : word) = Some W_6b1c0.
Proof. vm_refl. Qed.
Lemma D_6b1c0 : decode_any W_6b1c0 = Some (OpImm ALU_ADD 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1c4 : bv 32 := 0x00078613.
Lemma F_6b1c4 : fetch_word Plain.M.loaded_segments (0x6b1c4 : word) = Some W_6b1c4.
Proof. vm_refl. Qed.
Lemma D_6b1c4 : decode_any W_6b1c4 = Some (OpImm ALU_ADD 12 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1c8 : bv 32 := 0x00050693.
Lemma F_6b1c8 : fetch_word Plain.M.loaded_segments (0x6b1c8 : word) = Some W_6b1c8.
Proof. vm_refl. Qed.
Lemma D_6b1c8 : decode_any W_6b1c8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1cc : bv 32 := 0x00080513.
Lemma F_6b1cc : fetch_word Plain.M.loaded_segments (0x6b1cc : word) = Some W_6b1cc.
Proof. vm_refl. Qed.
Lemma D_6b1cc : decode_any W_6b1cc = Some (OpImm ALU_ADD 10 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1d0 : bv 32 := 0x00068663.
Lemma F_6b1d0 : fetch_word Plain.M.loaded_segments (0x6b1d0 : word) = Some W_6b1d0.
Proof. vm_refl. Qed.
Lemma D_6b1d0 : decode_any W_6b1d0 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1d4 : bv 32 := 0xfff00693.
Lemma F_6b1d4 : fetch_word Plain.M.loaded_segments (0x6b1d4 : word) = Some W_6b1d4.
Proof. vm_refl. Qed.
Lemma D_6b1d4 : decode_any W_6b1d4 = Some (OpImm ALU_ADD 13 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1d8 : bv 32 := 0x08d52823.
Lemma F_6b1d8 : fetch_word Plain.M.loaded_segments (0x6b1d8 : word) = Some W_6b1d8.
Proof. vm_refl. Qed.
Lemma D_6b1d8 : decode_any W_6b1d8 = Some (Store SZ4 10 13 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1dc : bv 32 := 0xdedff0ef.
Lemma F_6b1dc : fetch_word Plain.M.loaded_segments (0x6b1dc : word) = Some W_6b1dc.
Proof. vm_refl. Qed.
Lemma D_6b1dc : decode_any W_6b1dc = Some (Jal 1 2096620, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1e0 : bv 32 := 0x00043583.
Lemma F_6b1e0 : fetch_word Plain.M.loaded_segments (0x6b1e0 : word) = Some W_6b1e0.
Proof. vm_refl. Qed.
Lemma D_6b1e0 : decode_any W_6b1e0 = Some (Load SZ8 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1e4 : bv 32 := 0x00813603.
Lemma F_6b1e4 : fetch_word Plain.M.loaded_segments (0x6b1e4 : word) = Some W_6b1e4.
Proof. vm_refl. Qed.
Lemma D_6b1e4 : decode_any W_6b1e4 = Some (Load SZ8 true 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1e8 : bv 32 := 0x00c59a63.
Lemma F_6b1e8 : fetch_word Plain.M.loaded_segments (0x6b1e8 : word) = Some W_6b1e8.
Proof. vm_refl. Qed.
Lemma D_6b1e8 : decode_any W_6b1e8 = Some (Branch BC_NE 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1ec : bv 32 := 0x01813083.
Lemma F_6b1ec : fetch_word Plain.M.loaded_segments (0x6b1ec : word) = Some W_6b1ec.
Proof. vm_refl. Qed.
Lemma D_6b1ec : decode_any W_6b1ec = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1f0 : bv 32 := 0x01013403.
Lemma F_6b1f0 : fetch_word Plain.M.loaded_segments (0x6b1f0 : word) = Some W_6b1f0.
Proof. vm_refl. Qed.
Lemma D_6b1f0 : decode_any W_6b1f0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1f4 : bv 32 := 0x02010113.
Lemma F_6b1f4 : fetch_word Plain.M.loaded_segments (0x6b1f4 : word) = Some W_6b1f4.
Proof. vm_refl. Qed.
Lemma D_6b1f4 : decode_any W_6b1f4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1f8 : bv 32 := 0x00008067.
Lemma F_6b1f8 : fetch_word Plain.M.loaded_segments (0x6b1f8 : word) = Some W_6b1f8.
Proof. vm_refl. Qed.
Lemma D_6b1f8 : decode_any W_6b1f8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1fc : bv 32 := 0xb68fc0ef.
Lemma F_6b1fc : fetch_word Plain.M.loaded_segments (0x6b1fc : word) = Some W_6b1fc.
Proof. vm_refl. Qed.
Lemma D_6b1fc : decode_any W_6b1fc = Some (Jal 1 2081640, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b200 : bv 32 := 0xfb010113.
Lemma F_6b200 : fetch_word Plain.M.loaded_segments (0x6b200 : word) = Some W_6b200.
Proof. vm_refl. Qed.
Lemma D_6b200 : decode_any W_6b200 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b204 : bv 32 := 0x00113c23.
Lemma F_6b204 : fetch_word Plain.M.loaded_segments (0x6b204 : word) = Some W_6b204.
Proof. vm_refl. Qed.
Lemma D_6b204 : decode_any W_6b204 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b208 : bv 32 := 0x00813823.
Lemma F_6b208 : fetch_word Plain.M.loaded_segments (0x6b208 : word) = Some W_6b208.
Proof. vm_refl. Qed.
Lemma D_6b208 : decode_any W_6b208 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b20c : bv 32 := 0x05113423.
Lemma F_6b20c : fetch_word Plain.M.loaded_segments (0x6b20c : word) = Some W_6b20c.
Proof. vm_refl. Qed.
Lemma D_6b20c : decode_any W_6b20c = Some (Store SZ8 2 17 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b210 : bv 32 := 0x00014897.
Lemma F_6b210 : fetch_word Plain.M.loaded_segments (0x6b210 : word) = Some W_6b210.
Proof. vm_refl. Qed.
Lemma D_6b210 : decode_any W_6b210 = Some (Auipc 17 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b214 : bv 32 := 0x5f88b403.
Lemma F_6b214 : fetch_word Plain.M.loaded_segments (0x6b214 : word) = Some W_6b214.
Proof. vm_refl. Qed.
Lemma D_6b214 : decode_any W_6b214 = Some (Load SZ8 true 8 17 1528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b218 : bv 32 := 0x02d13423.
Lemma F_6b218 : fetch_word Plain.M.loaded_segments (0x6b218 : word) = Some W_6b218.
Proof. vm_refl. Qed.
Lemma D_6b218 : decode_any W_6b218 = Some (Store SZ8 2 13 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b21c : bv 32 := 0x02e13823.
Lemma F_6b21c : fetch_word Plain.M.loaded_segments (0x6b21c : word) = Some W_6b21c.
Proof. vm_refl. Qed.
Lemma D_6b21c : decode_any W_6b21c = Some (Store SZ8 2 14 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b220 : bv 32 := 0x02f13c23.
Lemma F_6b220 : fetch_word Plain.M.loaded_segments (0x6b220 : word) = Some W_6b220.
Proof. vm_refl. Qed.
Lemma D_6b220 : decode_any W_6b220 = Some (Store SZ8 2 15 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b224 : bv 32 := 0x05013023.
Lemma F_6b224 : fetch_word Plain.M.loaded_segments (0x6b224 : word) = Some W_6b224.
Proof. vm_refl. Qed.
Lemma D_6b224 : decode_any W_6b224 = Some (Store SZ8 2 16 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b228 : bv 32 := 0x00043683.
Lemma F_6b228 : fetch_word Plain.M.loaded_segments (0x6b228 : word) = Some W_6b228.
Proof. vm_refl. Qed.
Lemma D_6b228 : decode_any W_6b228 = Some (Load SZ8 true 13 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b22c : bv 32 := 0x02810713.
Lemma F_6b22c : fetch_word Plain.M.loaded_segments (0x6b22c : word) = Some W_6b22c.
Proof. vm_refl. Qed.
Lemma D_6b22c : decode_any W_6b22c = Some (OpImm ALU_ADD 14 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b230 : bv 32 := 0x00d13423.
Lemma F_6b230 : fetch_word Plain.M.loaded_segments (0x6b230 : word) = Some W_6b230.
Proof. vm_refl. Qed.
Lemma D_6b230 : decode_any W_6b230 = Some (Store SZ8 2 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b234 : bv 32 := 0x00e13023.
Lemma F_6b234 : fetch_word Plain.M.loaded_segments (0x6b234 : word) = Some W_6b234.
Proof. vm_refl. Qed.
Lemma D_6b234 : decode_any W_6b234 = Some (Store SZ8 2 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b238 : bv 32 := 0x02810693.
Lemma F_6b238 : fetch_word Plain.M.loaded_segments (0x6b238 : word) = Some W_6b238.
Proof. vm_refl. Qed.
Lemma D_6b238 : decode_any W_6b238 = Some (OpImm ALU_ADD 13 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b23c : bv 32 := 0x405040ef.
Lemma F_6b23c : fetch_word Plain.M.loaded_segments (0x6b23c : word) = Some W_6b23c.
Proof. vm_refl. Qed.
Lemma D_6b23c : decode_any W_6b23c = Some (Jal 1 19460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b240 : bv 32 := 0x00043583.
Lemma F_6b240 : fetch_word Plain.M.loaded_segments (0x6b240 : word) = Some W_6b240.
Proof. vm_refl. Qed.
Lemma D_6b240 : decode_any W_6b240 = Some (Load SZ8 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b244 : bv 32 := 0x00813603.
Lemma F_6b244 : fetch_word Plain.M.loaded_segments (0x6b244 : word) = Some W_6b244.
Proof. vm_refl. Qed.
Lemma D_6b244 : decode_any W_6b244 = Some (Load SZ8 true 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b248 : bv 32 := 0x00c59a63.
Lemma F_6b248 : fetch_word Plain.M.loaded_segments (0x6b248 : word) = Some W_6b248.
Proof. vm_refl. Qed.
Lemma D_6b248 : decode_any W_6b248 = Some (Branch BC_NE 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b24c : bv 32 := 0x01813083.
Lemma F_6b24c : fetch_word Plain.M.loaded_segments (0x6b24c : word) = Some W_6b24c.
Proof. vm_refl. Qed.
Lemma D_6b24c : decode_any W_6b24c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b250 : bv 32 := 0x01013403.
Lemma F_6b250 : fetch_word Plain.M.loaded_segments (0x6b250 : word) = Some W_6b250.
Proof. vm_refl. Qed.
Lemma D_6b250 : decode_any W_6b250 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b254 : bv 32 := 0x05010113.
Lemma F_6b254 : fetch_word Plain.M.loaded_segments (0x6b254 : word) = Some W_6b254.
Proof. vm_refl. Qed.
Lemma D_6b254 : decode_any W_6b254 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b258 : bv 32 := 0x00008067.
Lemma F_6b258 : fetch_word Plain.M.loaded_segments (0x6b258 : word) = Some W_6b258.
Proof. vm_refl. Qed.
Lemma D_6b258 : decode_any W_6b258 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b25c : bv 32 := 0xb08fc0ef.
Lemma F_6b25c : fetch_word Plain.M.loaded_segments (0x6b25c : word) = Some W_6b25c.
Proof. vm_refl. Qed.
Lemma D_6b25c : decode_any W_6b25c = Some (Jal 1 2081544, 4%Z).
Proof. vm_refl. Qed.
