(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

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
Definition W_33e2c : bv 32 := 0x09648a63.
Lemma F_33e2c : fetch_word Asan.M.loaded_segments (0x33e2c : word) = Some W_33e2c.
Proof. vm_refl. Qed.
Lemma D_33e2c : decode_any W_33e2c = Some (Branch BC_EQ 9 22 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e30 : bv 32 := 0x1e0220ef.
Lemma F_33e30 : fetch_word Asan.M.loaded_segments (0x33e30 : word) = Some W_33e30.
Proof. vm_refl. Qed.
Lemma D_33e30 : decode_any W_33e30 = Some (Jal 1 139744, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e34 : bv 32 := 0x08050663.
Lemma F_33e34 : fetch_word Asan.M.loaded_segments (0x33e34 : word) = Some W_33e34.
Proof. vm_refl. Qed.
Lemma D_33e34 : decode_any W_33e34 = Some (Branch BC_EQ 10 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e38 : bv 32 := 0x00077517.
Lemma F_33e38 : fetch_word Asan.M.loaded_segments (0x33e38 : word) = Some W_33e38.
Proof. vm_refl. Qed.
Lemma D_33e38 : decode_any W_33e38 = Some (Auipc 10 119, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e3c : bv 32 := 0x04853503.
Lemma F_33e3c : fetch_word Asan.M.loaded_segments (0x33e3c : word) = Some W_33e3c.
Proof. vm_refl. Qed.
Lemma D_33e3c : decode_any W_33e3c = Some (Load SZ8 true 10 10 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e40 : bv 32 := 0x00053503.
Lemma F_33e40 : fetch_word Asan.M.loaded_segments (0x33e40 : word) = Some W_33e40.
Proof. vm_refl. Qed.
Lemma D_33e40 : decode_any W_33e40 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e44 : bv 32 := 0x016a0b33.
Lemma F_33e44 : fetch_word Asan.M.loaded_segments (0x33e44 : word) = Some W_33e44.
Proof. vm_refl. Qed.
Lemma D_33e44 : decode_any W_33e44 = Some (Op ALU_ADD 22 20 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e48 : bv 32 := 0xfff50593.
Lemma F_33e48 : fetch_word Asan.M.loaded_segments (0x33e48 : word) = Some W_33e48.
Proof. vm_refl. Qed.
Lemma D_33e48 : decode_any W_33e48 = Some (OpImm ALU_ADD 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e4c : bv 32 := 0x00b53633.
Lemma F_33e4c : fetch_word Asan.M.loaded_segments (0x33e4c : word) = Some W_33e4c.
Proof. vm_refl. Qed.
Lemma D_33e4c : decode_any W_33e4c = Some (Op ALU_SLTU 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e50 : bv 32 := 0xfff60613.
Lemma F_33e50 : fetch_word Asan.M.loaded_segments (0x33e50 : word) = Some W_33e50.
Proof. vm_refl. Qed.
Lemma D_33e50 : decode_any W_33e50 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e54 : bv 32 := 0x00b67633.
Lemma F_33e54 : fetch_word Asan.M.loaded_segments (0x33e54 : word) = Some W_33e54.
Proof. vm_refl. Qed.
Lemma D_33e54 : decode_any W_33e54 = Some (Op ALU_AND 12 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e58 : bv 32 := 0x05667263.
Lemma F_33e58 : fetch_word Asan.M.loaded_segments (0x33e58 : word) = Some W_33e58.
Proof. vm_refl. Qed.
Lemma D_33e58 : decode_any W_33e58 = Some (Branch BC_GEU 12 22 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e5c : bv 32 := 0x00077617.
Lemma F_33e5c : fetch_word Asan.M.loaded_segments (0x33e5c : word) = Some W_33e5c.
Proof. vm_refl. Qed.
Lemma D_33e5c : decode_any W_33e5c = Some (Auipc 12 119, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e60 : bv 32 := 0x02c63603.
Lemma F_33e60 : fetch_word Asan.M.loaded_segments (0x33e60 : word) = Some W_33e60.
Proof. vm_refl. Qed.
Lemma D_33e60 : decode_any W_33e60 = Some (Load SZ8 true 12 12 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e64 : bv 32 := 0x00077697.
Lemma F_33e64 : fetch_word Asan.M.loaded_segments (0x33e64 : word) = Some W_33e64.
Proof. vm_refl. Qed.
Lemma D_33e64 : decode_any W_33e64 = Some (Auipc 13 119, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e68 : bv 32 := 0x02c6b683.
Lemma F_33e68 : fetch_word Asan.M.loaded_segments (0x33e68 : word) = Some W_33e68.
Proof. vm_refl. Qed.
Lemma D_33e68 : decode_any W_33e68 = Some (Load SZ8 true 13 13 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e6c : bv 32 := 0x00063783.
Lemma F_33e6c : fetch_word Asan.M.loaded_segments (0x33e6c : word) = Some W_33e6c.
Proof. vm_refl. Qed.
Lemma D_33e6c : decode_any W_33e6c = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e70 : bv 32 := 0x0006b603.
Lemma F_33e70 : fetch_word Asan.M.loaded_segments (0x33e70 : word) = Some W_33e70.
Proof. vm_refl. Qed.
Lemma D_33e70 : decode_any W_33e70 = Some (Load SZ8 true 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e74 : bv 32 := 0xfff78713.
Lemma F_33e74 : fetch_word Asan.M.loaded_segments (0x33e74 : word) = Some W_33e74.
Proof. vm_refl. Qed.
Lemma D_33e74 : decode_any W_33e74 = Some (OpImm ALU_ADD 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e78 : bv 32 := 0x01677463.
Lemma F_33e78 : fetch_word Asan.M.loaded_segments (0x33e78 : word) = Some W_33e78.
Proof. vm_refl. Qed.
Lemma D_33e78 : decode_any W_33e78 = Some (Branch BC_GEU 14 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e7c : bv 32 := 0x03667063.
Lemma F_33e7c : fetch_word Asan.M.loaded_segments (0x33e7c : word) = Some W_33e7c.
Proof. vm_refl. Qed.
Lemma D_33e7c : decode_any W_33e7c = Some (Branch BC_GEU 12 22 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e80 : bv 32 := 0x00077697.
Lemma F_33e80 : fetch_word Asan.M.loaded_segments (0x33e80 : word) = Some W_33e80.
Proof. vm_refl. Qed.
Lemma D_33e80 : decode_any W_33e80 = Some (Auipc 13 119, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e84 : bv 32 := 0x0186b683.
Lemma F_33e84 : fetch_word Asan.M.loaded_segments (0x33e84 : word) = Some W_33e84.
Proof. vm_refl. Qed.
Lemma D_33e84 : decode_any W_33e84 = Some (Load SZ8 true 13 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e88 : bv 32 := 0x0006b883.
Lemma F_33e88 : fetch_word Asan.M.loaded_segments (0x33e88 : word) = Some W_33e88.
Proof. vm_refl. Qed.
Lemma D_33e88 : decode_any W_33e88 = Some (Load SZ8 true 17 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e8c : bv 32 := 0x0038d693.
Lemma F_33e8c : fetch_word Asan.M.loaded_segments (0x33e8c : word) = Some W_33e8c.
Proof. vm_refl. Qed.
Lemma D_33e8c : decode_any W_33e8c = Some (ShiftImm ALU_SRL 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e90 : bv 32 := 0x00a68833.
Lemma F_33e90 : fetch_word Asan.M.loaded_segments (0x33e90 : word) = Some W_33e90.
Proof. vm_refl. Qed.
Lemma D_33e90 : decode_any W_33e90 = Some (Op ALU_ADD 16 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e94 : bv 32 := 0x2568ea63.
Lemma F_33e94 : fetch_word Asan.M.loaded_segments (0x33e94 : word) = Some W_33e94.
Proof. vm_refl. Qed.
Lemma D_33e94 : decode_any W_33e94 = Some (Branch BC_LTU 17 22 596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e98 : bv 32 := 0x25687863.
Lemma F_33e98 : fetch_word Asan.M.loaded_segments (0x33e98 : word) = Some W_33e98.
Proof. vm_refl. Qed.
Lemma D_33e98 : decode_any W_33e98 = Some (Branch BC_GEU 16 22 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e9c : bv 32 := 0x00077597.
Lemma F_33e9c : fetch_word Asan.M.loaded_segments (0x33e9c : word) = Some W_33e9c.
Proof. vm_refl. Qed.
Lemma D_33e9c : decode_any W_33e9c = Some (Auipc 11 119, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ea0 : bv 32 := 0xfdc5b583.
Lemma F_33ea0 : fetch_word Asan.M.loaded_segments (0x33ea0 : word) = Some W_33ea0.
Proof. vm_refl. Qed.
Lemma D_33ea0 : decode_any W_33ea0 = Some (Load SZ8 true 11 11 4060, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ea4 : bv 32 := 0x0555c583.
Lemma F_33ea4 : fetch_word Asan.M.loaded_segments (0x33ea4 : word) = Some W_33ea4.
Proof. vm_refl. Qed.
Lemma D_33ea4 : decode_any W_33ea4 = Some (Load SZ1 false 11 11 85, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ea8 : bv 32 := 0x003b5613.
Lemma F_33ea8 : fetch_word Asan.M.loaded_segments (0x33ea8 : word) = Some W_33ea8.
Proof. vm_refl. Qed.
Lemma D_33ea8 : decode_any W_33ea8 = Some (ShiftImm ALU_SRL 12 22 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33eac : bv 32 := 0x00c50533.
Lemma F_33eac : fetch_word Asan.M.loaded_segments (0x33eac : word) = Some W_33eac.
Proof. vm_refl. Qed.
Lemma D_33eac : decode_any W_33eac = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33eb0 : bv 32 := 0x40b005bb.
Lemma F_33eb0 : fetch_word Asan.M.loaded_segments (0x33eb0 : word) = Some W_33eb0.
Proof. vm_refl. Qed.
Lemma D_33eb0 : decode_any W_33eb0 = Some (Op32 ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33eb4 : bv 32 := 0x00b4f5b3.
Lemma F_33eb4 : fetch_word Asan.M.loaded_segments (0x33eb4 : word) = Some W_33eb4.
Proof. vm_refl. Qed.
Lemma D_33eb4 : decode_any W_33eb4 = Some (Op ALU_AND 11 9 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33eb8 : bv 32 := 0x0075f593.
Lemma F_33eb8 : fetch_word Asan.M.loaded_segments (0x33eb8 : word) = Some W_33eb8.
Proof. vm_refl. Qed.
Lemma D_33eb8 : decode_any W_33eb8 = Some (OpImm ALU_AND 11 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ebc : bv 32 := 0x00b50023.
Lemma F_33ebc : fetch_word Asan.M.loaded_segments (0x33ebc : word) = Some W_33ebc.
Proof. vm_refl. Qed.
Lemma D_33ebc : decode_any W_33ebc = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ec0 : bv 32 := 0x14d290ef.
Lemma F_33ec0 : fetch_word Asan.M.loaded_segments (0x33ec0 : word) = Some W_33ec0.
Proof. vm_refl. Qed.
Lemma D_33ec0 : decode_any W_33ec0 = Some (Jal 1 170316, 4%Z).
Proof. vm_refl. Qed.
