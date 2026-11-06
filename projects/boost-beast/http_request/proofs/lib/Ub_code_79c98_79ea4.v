(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_79c98 : bv 32 := 0x00757593.
Lemma F_79c98 : fetch_word Ubsan.M.loaded_segments (0x79c98 : word) = Some W_79c98.
Proof. vm_refl. Qed.
Lemma D_79c98 : decode_any W_79c98 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c9c : bv 32 := 0x00050613.
Lemma F_79c9c : fetch_word Ubsan.M.loaded_segments (0x79c9c : word) = Some W_79c9c.
Proof. vm_refl. Qed.
Lemma D_79c9c : decode_any W_79c9c = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ca0 : bv 32 := 0x02058a63.
Lemma F_79ca0 : fetch_word Ubsan.M.loaded_segments (0x79ca0 : word) = Some W_79ca0.
Proof. vm_refl. Qed.
Lemma D_79ca0 : decode_any W_79ca0 = Some (Branch BC_EQ 11 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ca4 : bv 32 := 0x00054583.
Lemma F_79ca4 : fetch_word Ubsan.M.loaded_segments (0x79ca4 : word) = Some W_79ca4.
Proof. vm_refl. Qed.
Lemma D_79ca4 : decode_any W_79ca4 = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ca8 : bv 32 := 0x06058c63.
Lemma F_79ca8 : fetch_word Ubsan.M.loaded_segments (0x79ca8 : word) = Some W_79ca8.
Proof. vm_refl. Qed.
Lemma D_79ca8 : decode_any W_79ca8 = Some (Branch BC_EQ 11 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79cac : bv 32 := 0x00150613.
Lemma F_79cac : fetch_word Ubsan.M.loaded_segments (0x79cac : word) = Some W_79cac.
Proof. vm_refl. Qed.
Lemma D_79cac : decode_any W_79cac = Some (OpImm ALU_ADD 12 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79cb0 : bv 32 := 0x00050593.
Lemma F_79cb0 : fetch_word Ubsan.M.loaded_segments (0x79cb0 : word) = Some W_79cb0.
Proof. vm_refl. Qed.
Lemma D_79cb0 : decode_any W_79cb0 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79cb4 : bv 32 := 0x00158693.
Lemma F_79cb4 : fetch_word Ubsan.M.loaded_segments (0x79cb4 : word) = Some W_79cb4.
Proof. vm_refl. Qed.
Lemma D_79cb4 : decode_any W_79cb4 = Some (OpImm ALU_ADD 13 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79cb8 : bv 32 := 0x0076f693.
Lemma F_79cb8 : fetch_word Ubsan.M.loaded_segments (0x79cb8 : word) = Some W_79cb8.
Proof. vm_refl. Qed.
Lemma D_79cb8 : decode_any W_79cb8 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79cbc : bv 32 := 0x00068c63.
Lemma F_79cbc : fetch_word Ubsan.M.loaded_segments (0x79cbc : word) = Some W_79cbc.
Proof. vm_refl. Qed.
Lemma D_79cbc : decode_any W_79cbc = Some (Branch BC_EQ 13 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79cc0 : bv 32 := 0x00064683.
Lemma F_79cc0 : fetch_word Ubsan.M.loaded_segments (0x79cc0 : word) = Some W_79cc0.
Proof. vm_refl. Qed.
Lemma D_79cc0 : decode_any W_79cc0 = Some (Load SZ1 false 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79cc4 : bv 32 := 0x00160613.
Lemma F_79cc4 : fetch_word Ubsan.M.loaded_segments (0x79cc4 : word) = Some W_79cc4.
Proof. vm_refl. Qed.
Lemma D_79cc4 : decode_any W_79cc4 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79cc8 : bv 32 := 0x00158593.
Lemma F_79cc8 : fetch_word Ubsan.M.loaded_segments (0x79cc8 : word) = Some W_79cc8.
Proof. vm_refl. Qed.
Lemma D_79cc8 : decode_any W_79cc8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ccc : bv 32 := 0xfe0694e3.
Lemma F_79ccc : fetch_word Ubsan.M.loaded_segments (0x79ccc : word) = Some W_79ccc.
Proof. vm_refl. Qed.
Lemma D_79ccc : decode_any W_79ccc = Some (Branch BC_NE 13 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79cd0 : bv 32 := 0x0480006f.
Lemma F_79cd0 : fetch_word Ubsan.M.loaded_segments (0x79cd0 : word) = Some W_79cd0.
Proof. vm_refl. Qed.
Lemma D_79cd0 : decode_any W_79cd0 = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79cd4 : bv 32 := 0xfff9b597.
Lemma F_79cd4 : fetch_word Ubsan.M.loaded_segments (0x79cd4 : word) = Some W_79cd4.
Proof. vm_refl. Qed.
Lemma D_79cd4 : decode_any W_79cd4 = Some (Auipc 11 1048475, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79cd8 : bv 32 := 0xfff9b717.
Lemma F_79cd8 : fetch_word Ubsan.M.loaded_segments (0x79cd8 : word) = Some W_79cd8.
Proof. vm_refl. Qed.
Lemma D_79cd8 : decode_any W_79cd8 = Some (Auipc 14 1048475, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79cdc : bv 32 := 0x1bc5b683.
Lemma F_79cdc : fetch_word Ubsan.M.loaded_segments (0x79cdc : word) = Some W_79cdc.
Proof. vm_refl. Qed.
Lemma D_79cdc : decode_any W_79cdc = Some (Load SZ8 true 13 11 444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ce0 : bv 32 := 0x1a073703.
Lemma F_79ce0 : fetch_word Ubsan.M.loaded_segments (0x79ce0 : word) = Some W_79ce0.
Proof. vm_refl. Qed.
Lemma D_79ce0 : decode_any W_79ce0 = Some (Load SZ8 true 14 14 416, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ce4 : bv 32 := 0xff760593.
Lemma F_79ce4 : fetch_word Ubsan.M.loaded_segments (0x79ce4 : word) = Some W_79ce4.
Proof. vm_refl. Qed.
Lemma D_79ce4 : decode_any W_79ce4 = Some (OpImm ALU_ADD 11 12 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ce8 : bv 32 := 0xff860613.
Lemma F_79ce8 : fetch_word Ubsan.M.loaded_segments (0x79ce8 : word) = Some W_79ce8.
Proof. vm_refl. Qed.
Lemma D_79ce8 : decode_any W_79ce8 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79cec : bv 32 := 0x00863783.
Lemma F_79cec : fetch_word Ubsan.M.loaded_segments (0x79cec : word) = Some W_79cec.
Proof. vm_refl. Qed.
Lemma D_79cec : decode_any W_79cec = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79cf0 : bv 32 := 0x00860613.
Lemma F_79cf0 : fetch_word Ubsan.M.loaded_segments (0x79cf0 : word) = Some W_79cf0.
Proof. vm_refl. Qed.
Lemma D_79cf0 : decode_any W_79cf0 = Some (OpImm ALU_ADD 12 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79cf4 : bv 32 := 0x40f68833.
Lemma F_79cf4 : fetch_word Ubsan.M.loaded_segments (0x79cf4 : word) = Some W_79cf4.
Proof. vm_refl. Qed.
Lemma D_79cf4 : decode_any W_79cf4 = Some (Op ALU_SUB 16 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79cf8 : bv 32 := 0x00f867b3.
Lemma F_79cf8 : fetch_word Ubsan.M.loaded_segments (0x79cf8 : word) = Some W_79cf8.
Proof. vm_refl. Qed.
Lemma D_79cf8 : decode_any W_79cf8 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79cfc : bv 32 := 0x00e7f7b3.
Lemma F_79cfc : fetch_word Ubsan.M.loaded_segments (0x79cfc : word) = Some W_79cfc.
Proof. vm_refl. Qed.
Lemma D_79cfc : decode_any W_79cfc = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d00 : bv 32 := 0x00858593.
Lemma F_79d00 : fetch_word Ubsan.M.loaded_segments (0x79d00 : word) = Some W_79d00.
Proof. vm_refl. Qed.
Lemma D_79d00 : decode_any W_79d00 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d04 : bv 32 := 0xfee784e3.
Lemma F_79d04 : fetch_word Ubsan.M.loaded_segments (0x79d04 : word) = Some W_79d04.
Proof. vm_refl. Qed.
Lemma D_79d04 : decode_any W_79d04 = Some (Branch BC_EQ 15 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d08 : bv 32 := 0x00064683.
Lemma F_79d08 : fetch_word Ubsan.M.loaded_segments (0x79d08 : word) = Some W_79d08.
Proof. vm_refl. Qed.
Lemma D_79d08 : decode_any W_79d08 = Some (Load SZ1 false 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d0c : bv 32 := 0x00160613.
Lemma F_79d0c : fetch_word Ubsan.M.loaded_segments (0x79d0c : word) = Some W_79d0c.
Proof. vm_refl. Qed.
Lemma D_79d0c : decode_any W_79d0c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d10 : bv 32 := 0x00158593.
Lemma F_79d10 : fetch_word Ubsan.M.loaded_segments (0x79d10 : word) = Some W_79d10.
Proof. vm_refl. Qed.
Lemma D_79d10 : decode_any W_79d10 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d14 : bv 32 := 0xfe069ae3.
Lemma F_79d14 : fetch_word Ubsan.M.loaded_segments (0x79d14 : word) = Some W_79d14.
Proof. vm_refl. Qed.
Lemma D_79d14 : decode_any W_79d14 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d18 : bv 32 := 0x40a58533.
Lemma F_79d18 : fetch_word Ubsan.M.loaded_segments (0x79d18 : word) = Some W_79d18.
Proof. vm_refl. Qed.
Lemma D_79d18 : decode_any W_79d18 = Some (Op ALU_SUB 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d1c : bv 32 := 0x00008067.
Lemma F_79d1c : fetch_word Ubsan.M.loaded_segments (0x79d1c : word) = Some W_79d1c.
Proof. vm_refl. Qed.
Lemma D_79d1c : decode_any W_79d1c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d20 : bv 32 := 0x40a50533.
Lemma F_79d20 : fetch_word Ubsan.M.loaded_segments (0x79d20 : word) = Some W_79d20.
Proof. vm_refl. Qed.
Lemma D_79d20 : decode_any W_79d20 = Some (Op ALU_SUB 10 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d24 : bv 32 := 0x00008067.
Lemma F_79d24 : fetch_word Ubsan.M.loaded_segments (0x79d24 : word) = Some W_79d24.
Proof. vm_refl. Qed.
Lemma D_79d24 : decode_any W_79d24 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d28 : bv 32 := 0xff010113.
Lemma F_79d28 : fetch_word Ubsan.M.loaded_segments (0x79d28 : word) = Some W_79d28.
Proof. vm_refl. Qed.
Lemma D_79d28 : decode_any W_79d28 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d2c : bv 32 := 0x00113423.
Lemma F_79d2c : fetch_word Ubsan.M.loaded_segments (0x79d2c : word) = Some W_79d2c.
Proof. vm_refl. Qed.
Lemma D_79d2c : decode_any W_79d2c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d30 : bv 32 := 0x00813023.
Lemma F_79d30 : fetch_word Ubsan.M.loaded_segments (0x79d30 : word) = Some W_79d30.
Proof. vm_refl. Qed.
Lemma D_79d30 : decode_any W_79d30 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d34 : bv 32 := 0x00050413.
Lemma F_79d34 : fetch_word Ubsan.M.loaded_segments (0x79d34 : word) = Some W_79d34.
Proof. vm_refl. Qed.
Lemma D_79d34 : decode_any W_79d34 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d38 : bv 32 := 0x018000ef.
Lemma F_79d38 : fetch_word Ubsan.M.loaded_segments (0x79d38 : word) = Some W_79d38.
Proof. vm_refl. Qed.
Lemma D_79d38 : decode_any W_79d38 = Some (Jal 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d3c : bv 32 := 0x00040513.
Lemma F_79d3c : fetch_word Ubsan.M.loaded_segments (0x79d3c : word) = Some W_79d3c.
Proof. vm_refl. Qed.
Lemma D_79d3c : decode_any W_79d3c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d40 : bv 32 := 0x00813083.
Lemma F_79d40 : fetch_word Ubsan.M.loaded_segments (0x79d40 : word) = Some W_79d40.
Proof. vm_refl. Qed.
Lemma D_79d40 : decode_any W_79d40 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d44 : bv 32 := 0x00013403.
Lemma F_79d44 : fetch_word Ubsan.M.loaded_segments (0x79d44 : word) = Some W_79d44.
Proof. vm_refl. Qed.
Lemma D_79d44 : decode_any W_79d44 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d48 : bv 32 := 0x01010113.
Lemma F_79d48 : fetch_word Ubsan.M.loaded_segments (0x79d48 : word) = Some W_79d48.
Proof. vm_refl. Qed.
Lemma D_79d48 : decode_any W_79d48 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d4c : bv 32 := 0x00008067.
Lemma F_79d4c : fetch_word Ubsan.M.loaded_segments (0x79d4c : word) = Some W_79d4c.
Proof. vm_refl. Qed.
Lemma D_79d4c : decode_any W_79d4c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d50 : bv 32 := 0xff010113.
Lemma F_79d50 : fetch_word Ubsan.M.loaded_segments (0x79d50 : word) = Some W_79d50.
Proof. vm_refl. Qed.
Lemma D_79d50 : decode_any W_79d50 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d54 : bv 32 := 0x00113423.
Lemma F_79d54 : fetch_word Ubsan.M.loaded_segments (0x79d54 : word) = Some W_79d54.
Proof. vm_refl. Qed.
Lemma D_79d54 : decode_any W_79d54 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d58 : bv 32 := 0x00813023.
Lemma F_79d58 : fetch_word Ubsan.M.loaded_segments (0x79d58 : word) = Some W_79d58.
Proof. vm_refl. Qed.
Lemma D_79d58 : decode_any W_79d58 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d5c : bv 32 := 0x00050413.
Lemma F_79d5c : fetch_word Ubsan.M.loaded_segments (0x79d5c : word) = Some W_79d5c.
Proof. vm_refl. Qed.
Lemma D_79d5c : decode_any W_79d5c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d60 : bv 32 := 0x00a5c6b3.
Lemma F_79d60 : fetch_word Ubsan.M.loaded_segments (0x79d60 : word) = Some W_79d60.
Proof. vm_refl. Qed.
Lemma D_79d60 : decode_any W_79d60 = Some (Op ALU_XOR 13 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d64 : bv 32 := 0x0076f693.
Lemma F_79d64 : fetch_word Ubsan.M.loaded_segments (0x79d64 : word) = Some W_79d64.
Proof. vm_refl. Qed.
Lemma D_79d64 : decode_any W_79d64 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d68 : bv 32 := 0x02068663.
Lemma F_79d68 : fetch_word Ubsan.M.loaded_segments (0x79d68 : word) = Some W_79d68.
Proof. vm_refl. Qed.
Lemma D_79d68 : decode_any W_79d68 = Some (Branch BC_EQ 13 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d6c : bv 32 := 0x0c060263.
Lemma F_79d6c : fetch_word Ubsan.M.loaded_segments (0x79d6c : word) = Some W_79d6c.
Proof. vm_refl. Qed.
Lemma D_79d6c : decode_any W_79d6c = Some (Branch BC_EQ 12 0 196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d70 : bv 32 := 0x00060693.
Lemma F_79d70 : fetch_word Ubsan.M.loaded_segments (0x79d70 : word) = Some W_79d70.
Proof. vm_refl. Qed.
Lemma D_79d70 : decode_any W_79d70 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d74 : bv 32 := 0x0005c603.
Lemma F_79d74 : fetch_word Ubsan.M.loaded_segments (0x79d74 : word) = Some W_79d74.
Proof. vm_refl. Qed.
Lemma D_79d74 : decode_any W_79d74 = Some (Load SZ1 false 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d78 : bv 32 := 0x00c40023.
Lemma F_79d78 : fetch_word Ubsan.M.loaded_segments (0x79d78 : word) = Some W_79d78.
Proof. vm_refl. Qed.
Lemma D_79d78 : decode_any W_79d78 = Some (Store SZ1 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d7c : bv 32 := 0x0a060c63.
Lemma F_79d7c : fetch_word Ubsan.M.loaded_segments (0x79d7c : word) = Some W_79d7c.
Proof. vm_refl. Qed.
Lemma D_79d7c : decode_any W_79d7c = Some (Branch BC_EQ 12 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d80 : bv 32 := 0xfff68693.
Lemma F_79d80 : fetch_word Ubsan.M.loaded_segments (0x79d80 : word) = Some W_79d80.
Proof. vm_refl. Qed.
Lemma D_79d80 : decode_any W_79d80 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d84 : bv 32 := 0x00158593.
Lemma F_79d84 : fetch_word Ubsan.M.loaded_segments (0x79d84 : word) = Some W_79d84.
Proof. vm_refl. Qed.
Lemma D_79d84 : decode_any W_79d84 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d88 : bv 32 := 0x00140413.
Lemma F_79d88 : fetch_word Ubsan.M.loaded_segments (0x79d88 : word) = Some W_79d88.
Proof. vm_refl. Qed.
Lemma D_79d88 : decode_any W_79d88 = Some (OpImm ALU_ADD 8 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d8c : bv 32 := 0xfe0694e3.
Lemma F_79d8c : fetch_word Ubsan.M.loaded_segments (0x79d8c : word) = Some W_79d8c.
Proof. vm_refl. Qed.
Lemma D_79d8c : decode_any W_79d8c = Some (Branch BC_NE 13 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d90 : bv 32 := 0x0a40006f.
Lemma F_79d90 : fetch_word Ubsan.M.loaded_segments (0x79d90 : word) = Some W_79d90.
Proof. vm_refl. Qed.
Lemma D_79d90 : decode_any W_79d90 = Some (Jal 0 164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d94 : bv 32 := 0x0075f693.
Lemma F_79d94 : fetch_word Ubsan.M.loaded_segments (0x79d94 : word) = Some W_79d94.
Proof. vm_refl. Qed.
Lemma D_79d94 : decode_any W_79d94 = Some (OpImm ALU_AND 13 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d98 : bv 32 := 0x00c03733.
Lemma F_79d98 : fetch_word Ubsan.M.loaded_segments (0x79d98 : word) = Some W_79d98.
Proof. vm_refl. Qed.
Lemma D_79d98 : decode_any W_79d98 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79d9c : bv 32 := 0x04068063.
Lemma F_79d9c : fetch_word Ubsan.M.loaded_segments (0x79d9c : word) = Some W_79d9c.
Proof. vm_refl. Qed.
Lemma D_79d9c : decode_any W_79d9c = Some (Branch BC_EQ 13 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79da0 : bv 32 := 0x02060e63.
Lemma F_79da0 : fetch_word Ubsan.M.loaded_segments (0x79da0 : word) = Some W_79da0.
Proof. vm_refl. Qed.
Lemma D_79da0 : decode_any W_79da0 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79da4 : bv 32 := 0x00158793.
Lemma F_79da4 : fetch_word Ubsan.M.loaded_segments (0x79da4 : word) = Some W_79da4.
Proof. vm_refl. Qed.
Lemma D_79da4 : decode_any W_79da4 = Some (OpImm ALU_ADD 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79da8 : bv 32 := 0x00100813.
Lemma F_79da8 : fetch_word Ubsan.M.loaded_segments (0x79da8 : word) = Some W_79da8.
Proof. vm_refl. Qed.
Lemma D_79da8 : decode_any W_79da8 = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79dac : bv 32 := 0x0005c703.
Lemma F_79dac : fetch_word Ubsan.M.loaded_segments (0x79dac : word) = Some W_79dac.
Proof. vm_refl. Qed.
Lemma D_79dac : decode_any W_79dac = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79db0 : bv 32 := 0x00060693.
Lemma F_79db0 : fetch_word Ubsan.M.loaded_segments (0x79db0 : word) = Some W_79db0.
Proof. vm_refl. Qed.
Lemma D_79db0 : decode_any W_79db0 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79db4 : bv 32 := 0x00e40023.
Lemma F_79db4 : fetch_word Ubsan.M.loaded_segments (0x79db4 : word) = Some W_79db4.
Proof. vm_refl. Qed.
Lemma D_79db4 : decode_any W_79db4 = Some (Store SZ1 8 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79db8 : bv 32 := 0x06070e63.
Lemma F_79db8 : fetch_word Ubsan.M.loaded_segments (0x79db8 : word) = Some W_79db8.
Proof. vm_refl. Qed.
Lemma D_79db8 : decode_any W_79db8 = Some (Branch BC_EQ 14 0 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79dbc : bv 32 := 0xfff68613.
Lemma F_79dbc : fetch_word Ubsan.M.loaded_segments (0x79dbc : word) = Some W_79dbc.
Proof. vm_refl. Qed.
Lemma D_79dbc : decode_any W_79dbc = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79dc0 : bv 32 := 0x00158593.
Lemma F_79dc0 : fetch_word Ubsan.M.loaded_segments (0x79dc0 : word) = Some W_79dc0.
Proof. vm_refl. Qed.
Lemma D_79dc0 : decode_any W_79dc0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79dc4 : bv 32 := 0x00140413.
Lemma F_79dc4 : fetch_word Ubsan.M.loaded_segments (0x79dc4 : word) = Some W_79dc4.
Proof. vm_refl. Qed.
Lemma D_79dc4 : decode_any W_79dc4 = Some (OpImm ALU_ADD 8 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79dc8 : bv 32 := 0x0077f893.
Lemma F_79dc8 : fetch_word Ubsan.M.loaded_segments (0x79dc8 : word) = Some W_79dc8.
Proof. vm_refl. Qed.
Lemma D_79dc8 : decode_any W_79dc8 = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79dcc : bv 32 := 0x00c03733.
Lemma F_79dcc : fetch_word Ubsan.M.loaded_segments (0x79dcc : word) = Some W_79dcc.
Proof. vm_refl. Qed.
Lemma D_79dcc : decode_any W_79dcc = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79dd0 : bv 32 := 0x00088663.
Lemma F_79dd0 : fetch_word Ubsan.M.loaded_segments (0x79dd0 : word) = Some W_79dd0.
Proof. vm_refl. Qed.
Lemma D_79dd0 : decode_any W_79dd0 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79dd4 : bv 32 := 0x00178793.
Lemma F_79dd4 : fetch_word Ubsan.M.loaded_segments (0x79dd4 : word) = Some W_79dd4.
Proof. vm_refl. Qed.
Lemma D_79dd4 : decode_any W_79dd4 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79dd8 : bv 32 := 0xfd069ae3.
Lemma F_79dd8 : fetch_word Ubsan.M.loaded_segments (0x79dd8 : word) = Some W_79dd8.
Proof. vm_refl. Qed.
Lemma D_79dd8 : decode_any W_79dd8 = Some (Branch BC_NE 13 16 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ddc : bv 32 := 0x04070a63.
Lemma F_79ddc : fetch_word Ubsan.M.loaded_segments (0x79ddc : word) = Some W_79ddc.
Proof. vm_refl. Qed.
Lemma D_79ddc : decode_any W_79ddc = Some (Branch BC_EQ 14 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79de0 : bv 32 := 0x0005c683.
Lemma F_79de0 : fetch_word Ubsan.M.loaded_segments (0x79de0 : word) = Some W_79de0.
Proof. vm_refl. Qed.
Lemma D_79de0 : decode_any W_79de0 = Some (Load SZ1 false 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79de4 : bv 32 := 0x06068a63.
Lemma F_79de4 : fetch_word Ubsan.M.loaded_segments (0x79de4 : word) = Some W_79de4.
Proof. vm_refl. Qed.
Lemma D_79de4 : decode_any W_79de4 = Some (Branch BC_EQ 13 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79de8 : bv 32 := 0x00800693.
Lemma F_79de8 : fetch_word Ubsan.M.loaded_segments (0x79de8 : word) = Some W_79de8.
Proof. vm_refl. Qed.
Lemma D_79de8 : decode_any W_79de8 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79dec : bv 32 := 0xf8d660e3.
Lemma F_79dec : fetch_word Ubsan.M.loaded_segments (0x79dec : word) = Some W_79dec.
Proof. vm_refl. Qed.
Lemma D_79dec : decode_any W_79dec = Some (Branch BC_LTU 12 13 8064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79df0 : bv 32 := 0xfff9b697.
Lemma F_79df0 : fetch_word Ubsan.M.loaded_segments (0x79df0 : word) = Some W_79df0.
Proof. vm_refl. Qed.
Lemma D_79df0 : decode_any W_79df0 = Some (Auipc 13 1048475, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79df4 : bv 32 := 0xfff9b717.
Lemma F_79df4 : fetch_word Ubsan.M.loaded_segments (0x79df4 : word) = Some W_79df4.
Proof. vm_refl. Qed.
Lemma D_79df4 : decode_any W_79df4 = Some (Auipc 14 1048475, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79df8 : bv 32 := 0x0a06b683.
Lemma F_79df8 : fetch_word Ubsan.M.loaded_segments (0x79df8 : word) = Some W_79df8.
Proof. vm_refl. Qed.
Lemma D_79df8 : decode_any W_79df8 = Some (Load SZ8 true 13 13 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79dfc : bv 32 := 0x08473703.
Lemma F_79dfc : fetch_word Ubsan.M.loaded_segments (0x79dfc : word) = Some W_79dfc.
Proof. vm_refl. Qed.
Lemma D_79dfc : decode_any W_79dfc = Some (Load SZ8 true 14 14 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e00 : bv 32 := 0x00700793.
Lemma F_79e00 : fetch_word Ubsan.M.loaded_segments (0x79e00 : word) = Some W_79e00.
Proof. vm_refl. Qed.
Lemma D_79e00 : decode_any W_79e00 = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e04 : bv 32 := 0x0005b803.
Lemma F_79e04 : fetch_word Ubsan.M.loaded_segments (0x79e04 : word) = Some W_79e04.
Proof. vm_refl. Qed.
Lemma D_79e04 : decode_any W_79e04 = Some (Load SZ8 true 16 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e08 : bv 32 := 0x410688b3.
Lemma F_79e08 : fetch_word Ubsan.M.loaded_segments (0x79e08 : word) = Some W_79e08.
Proof. vm_refl. Qed.
Lemma D_79e08 : decode_any W_79e08 = Some (Op ALU_SUB 17 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e0c : bv 32 := 0x0108e8b3.
Lemma F_79e0c : fetch_word Ubsan.M.loaded_segments (0x79e0c : word) = Some W_79e0c.
Proof. vm_refl. Qed.
Lemma D_79e0c : decode_any W_79e0c = Some (Op ALU_OR 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e10 : bv 32 := 0x00e8f8b3.
Lemma F_79e10 : fetch_word Ubsan.M.loaded_segments (0x79e10 : word) = Some W_79e10.
Proof. vm_refl. Qed.
Lemma D_79e10 : decode_any W_79e10 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e14 : bv 32 := 0xf4e89ee3.
Lemma F_79e14 : fetch_word Ubsan.M.loaded_segments (0x79e14 : word) = Some W_79e14.
Proof. vm_refl. Qed.
Lemma D_79e14 : decode_any W_79e14 = Some (Branch BC_NE 17 14 8028, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e18 : bv 32 := 0x01043023.
Lemma F_79e18 : fetch_word Ubsan.M.loaded_segments (0x79e18 : word) = Some W_79e18.
Proof. vm_refl. Qed.
Lemma D_79e18 : decode_any W_79e18 = Some (Store SZ8 8 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e1c : bv 32 := 0xff860613.
Lemma F_79e1c : fetch_word Ubsan.M.loaded_segments (0x79e1c : word) = Some W_79e1c.
Proof. vm_refl. Qed.
Lemma D_79e1c : decode_any W_79e1c = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e20 : bv 32 := 0x00858593.
Lemma F_79e20 : fetch_word Ubsan.M.loaded_segments (0x79e20 : word) = Some W_79e20.
Proof. vm_refl. Qed.
Lemma D_79e20 : decode_any W_79e20 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e24 : bv 32 := 0x00840413.
Lemma F_79e24 : fetch_word Ubsan.M.loaded_segments (0x79e24 : word) = Some W_79e24.
Proof. vm_refl. Qed.
Lemma D_79e24 : decode_any W_79e24 = Some (OpImm ALU_ADD 8 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e28 : bv 32 := 0xfcc7eee3.
Lemma F_79e28 : fetch_word Ubsan.M.loaded_segments (0x79e28 : word) = Some W_79e28.
Proof. vm_refl. Qed.
Lemma D_79e28 : decode_any W_79e28 = Some (Branch BC_LTU 15 12 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e2c : bv 32 := 0xf41ff06f.
Lemma F_79e2c : fetch_word Ubsan.M.loaded_segments (0x79e2c : word) = Some W_79e2c.
Proof. vm_refl. Qed.
Lemma D_79e2c : decode_any W_79e2c = Some (Jal 0 2096960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e30 : bv 32 := 0x00000693.
Lemma F_79e30 : fetch_word Ubsan.M.loaded_segments (0x79e30 : word) = Some W_79e30.
Proof. vm_refl. Qed.
Lemma D_79e30 : decode_any W_79e30 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e34 : bv 32 := 0x00040513.
Lemma F_79e34 : fetch_word Ubsan.M.loaded_segments (0x79e34 : word) = Some W_79e34.
Proof. vm_refl. Qed.
Lemma D_79e34 : decode_any W_79e34 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e38 : bv 32 := 0x00000593.
Lemma F_79e38 : fetch_word Ubsan.M.loaded_segments (0x79e38 : word) = Some W_79e38.
Proof. vm_refl. Qed.
Lemma D_79e38 : decode_any W_79e38 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e3c : bv 32 := 0x00068613.
Lemma F_79e3c : fetch_word Ubsan.M.loaded_segments (0x79e3c : word) = Some W_79e3c.
Proof. vm_refl. Qed.
Lemma D_79e3c : decode_any W_79e3c = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e40 : bv 32 := 0xc91ff0ef.
Lemma F_79e40 : fetch_word Ubsan.M.loaded_segments (0x79e40 : word) = Some W_79e40.
Proof. vm_refl. Qed.
Lemma D_79e40 : decode_any W_79e40 = Some (Jal 1 2096272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e44 : bv 32 := 0x00040513.
Lemma F_79e44 : fetch_word Ubsan.M.loaded_segments (0x79e44 : word) = Some W_79e44.
Proof. vm_refl. Qed.
Lemma D_79e44 : decode_any W_79e44 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e48 : bv 32 := 0x00813083.
Lemma F_79e48 : fetch_word Ubsan.M.loaded_segments (0x79e48 : word) = Some W_79e48.
Proof. vm_refl. Qed.
Lemma D_79e48 : decode_any W_79e48 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e4c : bv 32 := 0x00013403.
Lemma F_79e4c : fetch_word Ubsan.M.loaded_segments (0x79e4c : word) = Some W_79e4c.
Proof. vm_refl. Qed.
Lemma D_79e4c : decode_any W_79e4c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e50 : bv 32 := 0x01010113.
Lemma F_79e50 : fetch_word Ubsan.M.loaded_segments (0x79e50 : word) = Some W_79e50.
Proof. vm_refl. Qed.
Lemma D_79e50 : decode_any W_79e50 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e54 : bv 32 := 0x00008067.
Lemma F_79e54 : fetch_word Ubsan.M.loaded_segments (0x79e54 : word) = Some W_79e54.
Proof. vm_refl. Qed.
Lemma D_79e54 : decode_any W_79e54 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e58 : bv 32 := 0x00060693.
Lemma F_79e58 : fetch_word Ubsan.M.loaded_segments (0x79e58 : word) = Some W_79e58.
Proof. vm_refl. Qed.
Lemma D_79e58 : decode_any W_79e58 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e5c : bv 32 := 0xfd9ff06f.
Lemma F_79e5c : fetch_word Ubsan.M.loaded_segments (0x79e5c : word) = Some W_79e5c.
Proof. vm_refl. Qed.
Lemma D_79e5c : decode_any W_79e5c = Some (Jal 0 2097112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e60 : bv 32 := 0xfe010113.
Lemma F_79e60 : fetch_word Ubsan.M.loaded_segments (0x79e60 : word) = Some W_79e60.
Proof. vm_refl. Qed.
Lemma D_79e60 : decode_any W_79e60 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e64 : bv 32 := 0x00113c23.
Lemma F_79e64 : fetch_word Ubsan.M.loaded_segments (0x79e64 : word) = Some W_79e64.
Proof. vm_refl. Qed.
Lemma D_79e64 : decode_any W_79e64 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e68 : bv 32 := 0x00813823.
Lemma F_79e68 : fetch_word Ubsan.M.loaded_segments (0x79e68 : word) = Some W_79e68.
Proof. vm_refl. Qed.
Lemma D_79e68 : decode_any W_79e68 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e6c : bv 32 := 0x00913423.
Lemma F_79e6c : fetch_word Ubsan.M.loaded_segments (0x79e6c : word) = Some W_79e6c.
Proof. vm_refl. Qed.
Lemma D_79e6c : decode_any W_79e6c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e70 : bv 32 := 0x00058413.
Lemma F_79e70 : fetch_word Ubsan.M.loaded_segments (0x79e70 : word) = Some W_79e70.
Proof. vm_refl. Qed.
Lemma D_79e70 : decode_any W_79e70 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e74 : bv 32 := 0x00050493.
Lemma F_79e74 : fetch_word Ubsan.M.loaded_segments (0x79e74 : word) = Some W_79e74.
Proof. vm_refl. Qed.
Lemma D_79e74 : decode_any W_79e74 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e78 : bv 32 := 0x00000593.
Lemma F_79e78 : fetch_word Ubsan.M.loaded_segments (0x79e78 : word) = Some W_79e78.
Proof. vm_refl. Qed.
Lemma D_79e78 : decode_any W_79e78 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e7c : bv 32 := 0x00040613.
Lemma F_79e7c : fetch_word Ubsan.M.loaded_segments (0x79e7c : word) = Some W_79e7c.
Proof. vm_refl. Qed.
Lemma D_79e7c : decode_any W_79e7c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e80 : bv 32 := 0xdd4ff0ef.
Lemma F_79e80 : fetch_word Ubsan.M.loaded_segments (0x79e80 : word) = Some W_79e80.
Proof. vm_refl. Qed.
Lemma D_79e80 : decode_any W_79e80 = Some (Jal 1 2094548, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e84 : bv 32 := 0x00050463.
Lemma F_79e84 : fetch_word Ubsan.M.loaded_segments (0x79e84 : word) = Some W_79e84.
Proof. vm_refl. Qed.
Lemma D_79e84 : decode_any W_79e84 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e88 : bv 32 := 0x40950433.
Lemma F_79e88 : fetch_word Ubsan.M.loaded_segments (0x79e88 : word) = Some W_79e88.
Proof. vm_refl. Qed.
Lemma D_79e88 : decode_any W_79e88 = Some (Op ALU_SUB 8 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e8c : bv 32 := 0x00040513.
Lemma F_79e8c : fetch_word Ubsan.M.loaded_segments (0x79e8c : word) = Some W_79e8c.
Proof. vm_refl. Qed.
Lemma D_79e8c : decode_any W_79e8c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e90 : bv 32 := 0x01813083.
Lemma F_79e90 : fetch_word Ubsan.M.loaded_segments (0x79e90 : word) = Some W_79e90.
Proof. vm_refl. Qed.
Lemma D_79e90 : decode_any W_79e90 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e94 : bv 32 := 0x01013403.
Lemma F_79e94 : fetch_word Ubsan.M.loaded_segments (0x79e94 : word) = Some W_79e94.
Proof. vm_refl. Qed.
Lemma D_79e94 : decode_any W_79e94 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e98 : bv 32 := 0x00813483.
Lemma F_79e98 : fetch_word Ubsan.M.loaded_segments (0x79e98 : word) = Some W_79e98.
Proof. vm_refl. Qed.
Lemma D_79e98 : decode_any W_79e98 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79e9c : bv 32 := 0x02010113.
Lemma F_79e9c : fetch_word Ubsan.M.loaded_segments (0x79e9c : word) = Some W_79e9c.
Proof. vm_refl. Qed.
Lemma D_79e9c : decode_any W_79e9c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ea0 : bv 32 := 0x00008067.
Lemma F_79ea0 : fetch_word Ubsan.M.loaded_segments (0x79ea0 : word) = Some W_79ea0.
Proof. vm_refl. Qed.
Lemma D_79ea0 : decode_any W_79ea0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
