(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.H Require GcFlushS15.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.grayquant_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_14c54 : bv 32 := 0xffffe517.
Lemma F_14c54 : fetch_word Plain.M.loaded_segments (0x14cac : word) = Some W_14c54.
Proof. vm_refl. Qed.
Lemma D_14c54 : decode_any W_14c54 = Some (Auipc 10 1048574, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14c58 : bv 32 := 0xc5450513.
Lemma F_14c58 : fetch_word Plain.M.loaded_segments (0x14cb0 : word) = Some W_14c58.
Proof. vm_refl. Qed.
Lemma D_14c58 : decode_any W_14c58 = Some (OpImm ALU_ADD 10 10 3156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14c5c : bv 32 := 0x00019597.
Lemma F_14c5c : fetch_word Plain.M.loaded_segments (0x14cb4 : word) = Some W_14c5c.
Proof. vm_refl. Qed.
Lemma D_14c5c : decode_any W_14c5c = Some (Auipc 11 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14c60 : bv 32 := 0xd5458593.
Lemma F_14c60 : fetch_word Plain.M.loaded_segments (0x14cb8 : word) = Some W_14c60.
Proof. vm_refl. Qed.
Lemma D_14c60 : decode_any W_14c60 = Some (OpImm ALU_ADD 11 11 3412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14c64 : bv 32 := 0x000000ef.
Lemma F_14c64 : fetch_word Plain.M.loaded_segments (0x14cbc : word) = Some W_14c64.
Proof. vm_refl. Qed.
Lemma D_14c64 : decode_any W_14c64 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14c68 : bv 32 := 0x0040006f.
Lemma F_14c68 : fetch_word Plain.M.loaded_segments (0x14cc0 : word) = Some W_14c68.
Proof. vm_refl. Qed.
Lemma D_14c68 : decode_any W_14c68 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14c6c : bv 32 := 0x00813083.
Lemma F_14c6c : fetch_word Plain.M.loaded_segments (0x14cc4 : word) = Some W_14c6c.
Proof. vm_refl. Qed.
Lemma D_14c6c : decode_any W_14c6c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14c70 : bv 32 := 0x00013403.
Lemma F_14c70 : fetch_word Plain.M.loaded_segments (0x14cc8 : word) = Some W_14c70.
Proof. vm_refl. Qed.
Lemma D_14c70 : decode_any W_14c70 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14c74 : bv 32 := 0x01010113.
Lemma F_14c74 : fetch_word Plain.M.loaded_segments (0x14ccc : word) = Some W_14c74.
Proof. vm_refl. Qed.
Lemma D_14c74 : decode_any W_14c74 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14c78 : bv 32 := 0x00008067.
Lemma F_14c78 : fetch_word Plain.M.loaded_segments (0x14cd0 : word) = Some W_14c78.
Proof. vm_refl. Qed.
Lemma D_14c78 : decode_any W_14c78 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14c7c : bv 32 := 0xff010113.
Lemma F_14c7c : fetch_word Plain.M.loaded_segments (0x14cd4 : word) = Some W_14c7c.
Proof. vm_refl. Qed.
Lemma D_14c7c : decode_any W_14c7c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14c80 : bv 32 := 0x00113423.
Lemma F_14c80 : fetch_word Plain.M.loaded_segments (0x14cd8 : word) = Some W_14c80.
Proof. vm_refl. Qed.
Lemma D_14c80 : decode_any W_14c80 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14c84 : bv 32 := 0x00813023.
Lemma F_14c84 : fetch_word Plain.M.loaded_segments (0x14cdc : word) = Some W_14c84.
Proof. vm_refl. Qed.
Lemma D_14c84 : decode_any W_14c84 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14c88 : bv 32 := 0x01010413.
Lemma F_14c88 : fetch_word Plain.M.loaded_segments (0x14ce0 : word) = Some W_14c88.
Proof. vm_refl. Qed.
Lemma D_14c88 : decode_any W_14c88 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14c8c : bv 32 := 0x00019517.
Lemma F_14c8c : fetch_word Plain.M.loaded_segments (0x14ce4 : word) = Some W_14c8c.
Proof. vm_refl. Qed.
Lemma D_14c8c : decode_any W_14c8c = Some (Auipc 10 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14c90 : bv 32 := 0xd6450513.
Lemma F_14c90 : fetch_word Plain.M.loaded_segments (0x14ce8 : word) = Some W_14c90.
Proof. vm_refl. Qed.
Lemma D_14c90 : decode_any W_14c90 = Some (OpImm ALU_ADD 10 10 3428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14c94 : bv 32 := 0x00054503.
Lemma F_14c94 : fetch_word Plain.M.loaded_segments (0x14cec : word) = Some W_14c94.
Proof. vm_refl. Qed.
Lemma D_14c94 : decode_any W_14c94 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14c98 : bv 32 := 0x00157513.
Lemma F_14c98 : fetch_word Plain.M.loaded_segments (0x14cf0 : word) = Some W_14c98.
Proof. vm_refl. Qed.
Lemma D_14c98 : decode_any W_14c98 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14c9c : bv 32 := 0x00050663.
Lemma F_14c9c : fetch_word Plain.M.loaded_segments (0x14cf4 : word) = Some W_14c9c.
Proof. vm_refl. Qed.
Lemma D_14c9c : decode_any W_14c9c = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ca0 : bv 32 := 0x0040006f.
Lemma F_14ca0 : fetch_word Plain.M.loaded_segments (0x14cf8 : word) = Some W_14ca0.
Proof. vm_refl. Qed.
Lemma D_14ca0 : decode_any W_14ca0 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ca4 : bv 32 := 0x0580006f.
Lemma F_14ca4 : fetch_word Plain.M.loaded_segments (0x14cfc : word) = Some W_14ca4.
Proof. vm_refl. Qed.
Lemma D_14ca4 : decode_any W_14ca4 = Some (Jal 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ca8 : bv 32 := 0x00019517.
Lemma F_14ca8 : fetch_word Plain.M.loaded_segments (0x14d00 : word) = Some W_14ca8.
Proof. vm_refl. Qed.
Lemma D_14ca8 : decode_any W_14ca8 = Some (Auipc 10 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cac : bv 32 := 0xd4850593.
Lemma F_14cac : fetch_word Plain.M.loaded_segments (0x14d04 : word) = Some W_14cac.
Proof. vm_refl. Qed.
Lemma D_14cac : decode_any W_14cac = Some (OpImm ALU_ADD 11 10 3400, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cb0 : bv 32 := 0x00100513.
Lemma F_14cb0 : fetch_word Plain.M.loaded_segments (0x14d08 : word) = Some W_14cb0.
Proof. vm_refl. Qed.
Lemma D_14cb0 : decode_any W_14cb0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cb4 : bv 32 := 0x00a58023.
Lemma F_14cb4 : fetch_word Plain.M.loaded_segments (0x14d0c : word) = Some W_14cb4.
Proof. vm_refl. Qed.
Lemma D_14cb4 : decode_any W_14cb4 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cb8 : bv 32 := 0x00018517.
Lemma F_14cb8 : fetch_word Plain.M.loaded_segments (0x14d10 : word) = Some W_14cb8.
Proof. vm_refl. Qed.
Lemma D_14cb8 : decode_any W_14cb8 = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cbc : bv 32 := 0xa4853503.
Lemma F_14cbc : fetch_word Plain.M.loaded_segments (0x14d14 : word) = Some W_14cbc.
Proof. vm_refl. Qed.
Lemma D_14cbc : decode_any W_14cbc = Some (Load SZ8 true 10 10 2632, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cc0 : bv 32 := 0x00050e63.
Lemma F_14cc0 : fetch_word Plain.M.loaded_segments (0x14d18 : word) = Some W_14cc0.
Proof. vm_refl. Qed.
Lemma D_14cc0 : decode_any W_14cc0 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cc4 : bv 32 := 0x0040006f.
Lemma F_14cc4 : fetch_word Plain.M.loaded_segments (0x14d1c : word) = Some W_14cc4.
Proof. vm_refl. Qed.
Lemma D_14cc4 : decode_any W_14cc4 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cc8 : bv 32 := 0x00019517.
Lemma F_14cc8 : fetch_word Plain.M.loaded_segments (0x14d20 : word) = Some W_14cc8.
Proof. vm_refl. Qed.
Lemma D_14cc8 : decode_any W_14cc8 = Some (Auipc 10 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ccc : bv 32 := 0xaa850513.
Lemma F_14ccc : fetch_word Plain.M.loaded_segments (0x14d24 : word) = Some W_14ccc.
Proof. vm_refl. Qed.
Lemma D_14ccc : decode_any W_14ccc = Some (OpImm ALU_ADD 10 10 2728, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cd0 : bv 32 := 0x00053503.
Lemma F_14cd0 : fetch_word Plain.M.loaded_segments (0x14d28 : word) = Some W_14cd0.
Proof. vm_refl. Qed.
Lemma D_14cd0 : decode_any W_14cd0 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cd4 : bv 32 := 0x6590b0ef.
Lemma F_14cd4 : fetch_word Plain.M.loaded_segments (0x14d2c : word) = Some W_14cd4.
Proof. vm_refl. Qed.
Lemma D_14cd4 : decode_any W_14cd4 = Some (Jal 1 48728, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cd8 : bv 32 := 0x0040006f.
Lemma F_14cd8 : fetch_word Plain.M.loaded_segments (0x14d30 : word) = Some W_14cd8.
Proof. vm_refl. Qed.
Lemma D_14cd8 : decode_any W_14cd8 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cdc : bv 32 := 0x00018517.
Lemma F_14cdc : fetch_word Plain.M.loaded_segments (0x14d34 : word) = Some W_14cdc.
Proof. vm_refl. Qed.
Lemma D_14cdc : decode_any W_14cdc = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ce0 : bv 32 := 0xa2c53503.
Lemma F_14ce0 : fetch_word Plain.M.loaded_segments (0x14d38 : word) = Some W_14ce0.
Proof. vm_refl. Qed.
Lemma D_14ce0 : decode_any W_14ce0 = Some (Load SZ8 true 10 10 2604, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ce4 : bv 32 := 0x00050c63.
Lemma F_14ce4 : fetch_word Plain.M.loaded_segments (0x14d3c : word) = Some W_14ce4.
Proof. vm_refl. Qed.
Lemma D_14ce4 : decode_any W_14ce4 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ce8 : bv 32 := 0x0040006f.
Lemma F_14ce8 : fetch_word Plain.M.loaded_segments (0x14d40 : word) = Some W_14ce8.
Proof. vm_refl. Qed.
Lemma D_14ce8 : decode_any W_14ce8 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cec : bv 32 := 0xffffe517.
Lemma F_14cec : fetch_word Plain.M.loaded_segments (0x14d44 : word) = Some W_14cec.
Proof. vm_refl. Qed.
Lemma D_14cec : decode_any W_14cec = Some (Auipc 10 1048574, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cf0 : bv 32 := 0xbbc50513.
Lemma F_14cf0 : fetch_word Plain.M.loaded_segments (0x14d48 : word) = Some W_14cf0.
Proof. vm_refl. Qed.
Lemma D_14cf0 : decode_any W_14cf0 = Some (OpImm ALU_ADD 10 10 3004, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cf4 : bv 32 := 0x000000ef.
Lemma F_14cf4 : fetch_word Plain.M.loaded_segments (0x14d4c : word) = Some W_14cf4.
Proof. vm_refl. Qed.
Lemma D_14cf4 : decode_any W_14cf4 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cf8 : bv 32 := 0x0040006f.
Lemma F_14cf8 : fetch_word Plain.M.loaded_segments (0x14d50 : word) = Some W_14cf8.
Proof. vm_refl. Qed.
Lemma D_14cf8 : decode_any W_14cf8 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cfc : bv 32 := 0x00813083.
Lemma F_14cfc : fetch_word Plain.M.loaded_segments (0x14d54 : word) = Some W_14cfc.
Proof. vm_refl. Qed.
Lemma D_14cfc : decode_any W_14cfc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d00 : bv 32 := 0x00013403.
Lemma F_14d00 : fetch_word Plain.M.loaded_segments (0x14d58 : word) = Some W_14d00.
Proof. vm_refl. Qed.
Lemma D_14d00 : decode_any W_14d00 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d04 : bv 32 := 0x01010113.
Lemma F_14d04 : fetch_word Plain.M.loaded_segments (0x14d5c : word) = Some W_14d04.
Proof. vm_refl. Qed.
Lemma D_14d04 : decode_any W_14d04 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d08 : bv 32 := 0x00008067.
Lemma F_14d08 : fetch_word Plain.M.loaded_segments (0x14d60 : word) = Some W_14d08.
Proof. vm_refl. Qed.
Lemma D_14d08 : decode_any W_14d08 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15134 : bv 32 := 0x00029517.
Lemma F_15134 : fetch_word Plain.M.loaded_segments (0x1518c : word) = Some W_15134.
Proof. vm_refl. Qed.
Lemma D_15134 : decode_any W_15134 = Some (Auipc 10 41, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15138 : bv 32 := 0x8c854503.
Lemma F_15138 : fetch_word Plain.M.loaded_segments (0x15190 : word) = Some W_15138.
Proof. vm_refl. Qed.
Lemma D_15138 : decode_any W_15138 = Some (Load SZ1 false 10 10 2248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1513c : bv 32 := 0x00051463.
Lemma F_1513c : fetch_word Plain.M.loaded_segments (0x15194 : word) = Some W_1513c.
Proof. vm_refl. Qed.
Lemma D_1513c : decode_any W_1513c = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15140 : bv 32 := 0x00008067.
Lemma F_15140 : fetch_word Plain.M.loaded_segments (0x15198 : word) = Some W_15140.
Proof. vm_refl. Qed.
Lemma D_15140 : decode_any W_15140 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15144 : bv 32 := 0xff010113.
Lemma F_15144 : fetch_word Plain.M.loaded_segments (0x1519c : word) = Some W_15144.
Proof. vm_refl. Qed.
Lemma D_15144 : decode_any W_15144 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15148 : bv 32 := 0x00113423.
Lemma F_15148 : fetch_word Plain.M.loaded_segments (0x151a0 : word) = Some W_15148.
Proof. vm_refl. Qed.
Lemma D_15148 : decode_any W_15148 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1514c : bv 32 := 0x00017517.
Lemma F_1514c : fetch_word Plain.M.loaded_segments (0x151a4 : word) = Some W_1514c.
Proof. vm_refl. Qed.
Lemma D_1514c : decode_any W_1514c = Some (Auipc 10 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15150 : bv 32 := 0x5d453503.
Lemma F_15150 : fetch_word Plain.M.loaded_segments (0x151a8 : word) = Some W_15150.
Proof. vm_refl. Qed.
Lemma D_15150 : decode_any W_15150 = Some (Load SZ8 true 10 10 1492, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15154 : bv 32 := 0x00053503.
Lemma F_15154 : fetch_word Plain.M.loaded_segments (0x151ac : word) = Some W_15154.
Proof. vm_refl. Qed.
Lemma D_15154 : decode_any W_15154 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15158 : bv 32 := 0x3490d0ef.
Lemma F_15158 : fetch_word Plain.M.loaded_segments (0x151b0 : word) = Some W_15158.
Proof. vm_refl. Qed.
Lemma D_15158 : decode_any W_15158 = Some (Jal 1 56136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1515c : bv 32 := 0x04d00513.
Lemma F_1515c : fetch_word Plain.M.loaded_segments (0x151b4 : word) = Some W_1515c.
Proof. vm_refl. Qed.
Lemma D_1515c : decode_any W_1515c = Some (OpImm ALU_ADD 10 0 77, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15160 : bv 32 := 0x4ac160ef.
Lemma F_15160 : fetch_word Plain.M.loaded_segments (0x151b8 : word) = Some W_15160.
Proof. vm_refl. Qed.
Lemma D_15160 : decode_any W_15160 = Some (Jal 1 91308, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20a70 : bv 32 := 0xfd010113.
Lemma F_20a70 : fetch_word Plain.M.loaded_segments (0x20abc : word) = Some W_20a70.
Proof. vm_refl. Qed.
Lemma D_20a70 : decode_any W_20a70 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20a74 : bv 32 := 0x02113423.
Lemma F_20a74 : fetch_word Plain.M.loaded_segments (0x20ac0 : word) = Some W_20a74.
Proof. vm_refl. Qed.
Lemma D_20a74 : decode_any W_20a74 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20a78 : bv 32 := 0x02813023.
Lemma F_20a78 : fetch_word Plain.M.loaded_segments (0x20ac4 : word) = Some W_20a78.
Proof. vm_refl. Qed.
Lemma D_20a78 : decode_any W_20a78 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20a7c : bv 32 := 0x00913c23.
Lemma F_20a7c : fetch_word Plain.M.loaded_segments (0x20ac8 : word) = Some W_20a7c.
Proof. vm_refl. Qed.
Lemma D_20a7c : decode_any W_20a7c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20a80 : bv 32 := 0x01213823.
Lemma F_20a80 : fetch_word Plain.M.loaded_segments (0x20acc : word) = Some W_20a80.
Proof. vm_refl. Qed.
Lemma D_20a80 : decode_any W_20a80 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20a84 : bv 32 := 0x01313423.
Lemma F_20a84 : fetch_word Plain.M.loaded_segments (0x20ad0 : word) = Some W_20a84.
Proof. vm_refl. Qed.
Lemma D_20a84 : decode_any W_20a84 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20a88 : bv 32 := 0x0003d517.
Lemma F_20a88 : fetch_word Plain.M.loaded_segments (0x20ad4 : word) = Some W_20a88.
Proof. vm_refl. Qed.
Lemma D_20a88 : decode_any W_20a88 = Some (Auipc 10 61, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20a8c : bv 32 := 0x0bc50913.
Lemma F_20a8c : fetch_word Plain.M.loaded_segments (0x20ad8 : word) = Some W_20a8c.
Proof. vm_refl. Qed.
Lemma D_20a8c : decode_any W_20a8c = Some (OpImm ALU_ADD 18 10 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20a90 : bv 32 := 0x00490413.
Lemma F_20a90 : fetch_word Plain.M.loaded_segments (0x20adc : word) = Some W_20a90.
Proof. vm_refl. Qed.
Lemma D_20a90 : decode_any W_20a90 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20a94 : bv 32 := 0x00040513.
Lemma F_20a94 : fetch_word Plain.M.loaded_segments (0x20ae0 : word) = Some W_20a94.
Proof. vm_refl. Qed.
Lemma D_20a94 : decode_any W_20a94 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20a98 : bv 32 := 0x0510a0ef.
Lemma F_20a98 : fetch_word Plain.M.loaded_segments (0x20ae4 : word) = Some W_20a98.
Proof. vm_refl. Qed.
Lemma D_20a98 : decode_any W_20a98 = Some (Jal 1 43088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20a9c : bv 32 := 0x01093503.
Lemma F_20a9c : fetch_word Plain.M.loaded_segments (0x20ae8 : word) = Some W_20a9c.
Proof. vm_refl. Qed.
Lemma D_20a9c : decode_any W_20a9c = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20aa0 : bv 32 := 0x06050863.
Lemma F_20aa0 : fetch_word Plain.M.loaded_segments (0x20aec : word) = Some W_20aa0.
Proof. vm_refl. Qed.
Lemma D_20aa0 : decode_any W_20aa0 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20aa4 : bv 32 := 0x00892583.
Lemma F_20aa4 : fetch_word Plain.M.loaded_segments (0x20af0 : word) = Some W_20aa4.
Proof. vm_refl. Qed.
Lemma D_20aa4 : decode_any W_20aa4 = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20aa8 : bv 32 := 0x0180006f.
Lemma F_20aa8 : fetch_word Plain.M.loaded_segments (0x20af4 : word) = Some W_20aa8.
Proof. vm_refl. Qed.
Lemma D_20aa8 : decode_any W_20aa8 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20aac : bv 32 := 0x00053503.
Lemma F_20aac : fetch_word Plain.M.loaded_segments (0x20af8 : word) = Some W_20aac.
Proof. vm_refl. Qed.
Lemma D_20aac : decode_any W_20aac = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ab0 : bv 32 := 0x02000593.
Lemma F_20ab0 : fetch_word Plain.M.loaded_segments (0x20afc : word) = Some W_20ab0.
Proof. vm_refl. Qed.
Lemma D_20ab0 : decode_any W_20ab0 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ab4 : bv 32 := 0x00b92423.
Lemma F_20ab4 : fetch_word Plain.M.loaded_segments (0x20b00 : word) = Some W_20ab4.
Proof. vm_refl. Qed.
Lemma D_20ab4 : decode_any W_20ab4 = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ab8 : bv 32 := 0x00a93823.
Lemma F_20ab8 : fetch_word Plain.M.loaded_segments (0x20b04 : word) = Some W_20ab8.
Proof. vm_refl. Qed.
Lemma D_20ab8 : decode_any W_20ab8 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20abc : bv 32 := 0x04050a63.
Lemma F_20abc : fetch_word Plain.M.loaded_segments (0x20b08 : word) = Some W_20abc.
Proof. vm_refl. Qed.
Lemma D_20abc : decode_any W_20abc = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ac0 : bv 32 := 0xfff5861b.
Lemma F_20ac0 : fetch_word Plain.M.loaded_segments (0x20b0c : word) = Some W_20ac0.
Proof. vm_refl. Qed.
Lemma D_20ac0 : decode_any W_20ac0 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ac4 : bv 32 := 0x00c92423.
Lemma F_20ac4 : fetch_word Plain.M.loaded_segments (0x20b10 : word) = Some W_20ac4.
Proof. vm_refl. Qed.
Lemma D_20ac4 : decode_any W_20ac4 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ac8 : bv 32 := 0xfeb052e3.
Lemma F_20ac8 : fetch_word Plain.M.loaded_segments (0x20b14 : word) = Some W_20ac8.
Proof. vm_refl. Qed.
Lemma D_20ac8 : decode_any W_20ac8 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20acc : bv 32 := 0x01093503.
Lemma F_20acc : fetch_word Plain.M.loaded_segments (0x20b18 : word) = Some W_20acc.
Proof. vm_refl. Qed.
Lemma D_20acc : decode_any W_20acc = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ad0 : bv 32 := 0x00361613.
Lemma F_20ad0 : fetch_word Plain.M.loaded_segments (0x20b1c : word) = Some W_20ad0.
Proof. vm_refl. Qed.
Lemma D_20ad0 : decode_any W_20ad0 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ad4 : bv 32 := 0x00c50533.
Lemma F_20ad4 : fetch_word Plain.M.loaded_segments (0x20b20 : word) = Some W_20ad4.
Proof. vm_refl. Qed.
Lemma D_20ad4 : decode_any W_20ad4 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ad8 : bv 32 := 0x00853983.
Lemma F_20ad8 : fetch_word Plain.M.loaded_segments (0x20b24 : word) = Some W_20ad8.
Proof. vm_refl. Qed.
Lemma D_20ad8 : decode_any W_20ad8 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20adc : bv 32 := 0x10853483.
Lemma F_20adc : fetch_word Plain.M.loaded_segments (0x20b28 : word) = Some W_20adc.
Proof. vm_refl. Qed.
Lemma D_20adc : decode_any W_20adc = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ae0 : bv 32 := 0x00040513.
Lemma F_20ae0 : fetch_word Plain.M.loaded_segments (0x20b2c : word) = Some W_20ae0.
Proof. vm_refl. Qed.
Lemma D_20ae0 : decode_any W_20ae0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ae4 : bv 32 := 0x28d0a0ef.
Lemma F_20ae4 : fetch_word Plain.M.loaded_segments (0x20b30 : word) = Some W_20ae4.
Proof. vm_refl. Qed.
Lemma D_20ae4 : decode_any W_20ae4 = Some (Jal 1 43660, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ae8 : bv 32 := 0x00048513.
Lemma F_20ae8 : fetch_word Plain.M.loaded_segments (0x20b34 : word) = Some W_20ae8.
Proof. vm_refl. Qed.
Lemma D_20ae8 : decode_any W_20ae8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20aec : bv 32 := 0x000980e7.
Lemma F_20aec : fetch_word Plain.M.loaded_segments (0x20b38 : word) = Some W_20aec.
Proof. vm_refl. Qed.
Lemma D_20aec : decode_any W_20aec = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20af0 : bv 32 := 0x00040513.
Lemma F_20af0 : fetch_word Plain.M.loaded_segments (0x20b3c : word) = Some W_20af0.
Proof. vm_refl. Qed.
Lemma D_20af0 : decode_any W_20af0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20af4 : bv 32 := 0x7f40a0ef.
Lemma F_20af4 : fetch_word Plain.M.loaded_segments (0x20b40 : word) = Some W_20af4.
Proof. vm_refl. Qed.
Lemma D_20af4 : decode_any W_20af4 = Some (Jal 1 42996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20af8 : bv 32 := 0x00892503.
Lemma F_20af8 : fetch_word Plain.M.loaded_segments (0x20b44 : word) = Some W_20af8.
Proof. vm_refl. Qed.
Lemma D_20af8 : decode_any W_20af8 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20afc : bv 32 := 0xfff5061b.
Lemma F_20afc : fetch_word Plain.M.loaded_segments (0x20b48 : word) = Some W_20afc.
Proof. vm_refl. Qed.
Lemma D_20afc : decode_any W_20afc = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b00 : bv 32 := 0x00c92423.
Lemma F_20b00 : fetch_word Plain.M.loaded_segments (0x20b4c : word) = Some W_20b00.
Proof. vm_refl. Qed.
Lemma D_20b00 : decode_any W_20b00 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b04 : bv 32 := 0xfca044e3.
Lemma F_20b04 : fetch_word Plain.M.loaded_segments (0x20b50 : word) = Some W_20b04.
Proof. vm_refl. Qed.
Lemma D_20b04 : decode_any W_20b04 = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b08 : bv 32 := 0x01093503.
Lemma F_20b08 : fetch_word Plain.M.loaded_segments (0x20b54 : word) = Some W_20b08.
Proof. vm_refl. Qed.
Lemma D_20b08 : decode_any W_20b08 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b0c : bv 32 := 0xfa1ff06f.
Lemma F_20b0c : fetch_word Plain.M.loaded_segments (0x20b58 : word) = Some W_20b0c.
Proof. vm_refl. Qed.
Lemma D_20b0c : decode_any W_20b0c = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b10 : bv 32 := 0x00100513.
Lemma F_20b10 : fetch_word Plain.M.loaded_segments (0x20b5c : word) = Some W_20b10.
Proof. vm_refl. Qed.
Lemma D_20b10 : decode_any W_20b10 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b14 : bv 32 := 0x00a90023.
Lemma F_20b14 : fetch_word Plain.M.loaded_segments (0x20b60 : word) = Some W_20b14.
Proof. vm_refl. Qed.
Lemma D_20b14 : decode_any W_20b14 = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b18 : bv 32 := 0x00040513.
Lemma F_20b18 : fetch_word Plain.M.loaded_segments (0x20b64 : word) = Some W_20b18.
Proof. vm_refl. Qed.
Lemma D_20b18 : decode_any W_20b18 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b1c : bv 32 := 0x02813083.
Lemma F_20b1c : fetch_word Plain.M.loaded_segments (0x20b68 : word) = Some W_20b1c.
Proof. vm_refl. Qed.
Lemma D_20b1c : decode_any W_20b1c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b20 : bv 32 := 0x02013403.
Lemma F_20b20 : fetch_word Plain.M.loaded_segments (0x20b6c : word) = Some W_20b20.
Proof. vm_refl. Qed.
Lemma D_20b20 : decode_any W_20b20 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b24 : bv 32 := 0x01813483.
Lemma F_20b24 : fetch_word Plain.M.loaded_segments (0x20b70 : word) = Some W_20b24.
Proof. vm_refl. Qed.
Lemma D_20b24 : decode_any W_20b24 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b28 : bv 32 := 0x01013903.
Lemma F_20b28 : fetch_word Plain.M.loaded_segments (0x20b74 : word) = Some W_20b28.
Proof. vm_refl. Qed.
Lemma D_20b28 : decode_any W_20b28 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b2c : bv 32 := 0x00813983.
Lemma F_20b2c : fetch_word Plain.M.loaded_segments (0x20b78 : word) = Some W_20b2c.
Proof. vm_refl. Qed.
Lemma D_20b2c : decode_any W_20b2c = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b30 : bv 32 := 0x03010113.
Lemma F_20b30 : fetch_word Plain.M.loaded_segments (0x20b7c : word) = Some W_20b30.
Proof. vm_refl. Qed.
Lemma D_20b30 : decode_any W_20b30 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b34 : bv 32 := 0x23d0a06f.
Lemma F_20b34 : fetch_word Plain.M.loaded_segments (0x20b80 : word) = Some W_20b34.
Proof. vm_refl. Qed.
Lemma D_20b34 : decode_any W_20b34 = Some (Jal 0 43580, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b38 : bv 32 := 0x00008067.
Lemma F_20b38 : fetch_word Plain.M.loaded_segments (0x20b84 : word) = Some W_20b38.
Proof. vm_refl. Qed.
Lemma D_20b38 : decode_any W_20b38 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b3c : bv 32 := 0xfd010113.
Lemma F_20b3c : fetch_word Plain.M.loaded_segments (0x20b88 : word) = Some W_20b3c.
Proof. vm_refl. Qed.
Lemma D_20b3c : decode_any W_20b3c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b40 : bv 32 := 0x02113423.
Lemma F_20b40 : fetch_word Plain.M.loaded_segments (0x20b8c : word) = Some W_20b40.
Proof. vm_refl. Qed.
Lemma D_20b40 : decode_any W_20b40 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b44 : bv 32 := 0x02813023.
Lemma F_20b44 : fetch_word Plain.M.loaded_segments (0x20b90 : word) = Some W_20b44.
Proof. vm_refl. Qed.
Lemma D_20b44 : decode_any W_20b44 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b48 : bv 32 := 0x00913c23.
Lemma F_20b48 : fetch_word Plain.M.loaded_segments (0x20b94 : word) = Some W_20b48.
Proof. vm_refl. Qed.
Lemma D_20b48 : decode_any W_20b48 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b4c : bv 32 := 0x01213823.
Lemma F_20b4c : fetch_word Plain.M.loaded_segments (0x20b98 : word) = Some W_20b4c.
Proof. vm_refl. Qed.
Lemma D_20b4c : decode_any W_20b4c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b50 : bv 32 := 0x01313423.
Lemma F_20b50 : fetch_word Plain.M.loaded_segments (0x20b9c : word) = Some W_20b50.
Proof. vm_refl. Qed.
Lemma D_20b50 : decode_any W_20b50 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b54 : bv 32 := 0x00050493.
Lemma F_20b54 : fetch_word Plain.M.loaded_segments (0x20ba0 : word) = Some W_20b54.
Proof. vm_refl. Qed.
Lemma D_20b54 : decode_any W_20b54 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b58 : bv 32 := 0x0003d517.
Lemma F_20b58 : fetch_word Plain.M.loaded_segments (0x20ba4 : word) = Some W_20b58.
Proof. vm_refl. Qed.
Lemma D_20b58 : decode_any W_20b58 = Some (Auipc 10 61, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b5c : bv 32 := 0xfec50993.
Lemma F_20b5c : fetch_word Plain.M.loaded_segments (0x20ba8 : word) = Some W_20b5c.
Proof. vm_refl. Qed.
Lemma D_20b5c : decode_any W_20b5c = Some (OpImm ALU_ADD 19 10 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b60 : bv 32 := 0x00498413.
Lemma F_20b60 : fetch_word Plain.M.loaded_segments (0x20bac : word) = Some W_20b60.
Proof. vm_refl. Qed.
Lemma D_20b60 : decode_any W_20b60 = Some (OpImm ALU_ADD 8 19 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b64 : bv 32 := 0x00040513.
Lemma F_20b64 : fetch_word Plain.M.loaded_segments (0x20bb0 : word) = Some W_20b64.
Proof. vm_refl. Qed.
Lemma D_20b64 : decode_any W_20b64 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b68 : bv 32 := 0x7800a0ef.
Lemma F_20b68 : fetch_word Plain.M.loaded_segments (0x20bb4 : word) = Some W_20b68.
Proof. vm_refl. Qed.
Lemma D_20b68 : decode_any W_20b68 = Some (Jal 1 42880, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b6c : bv 32 := 0x0009c503.
Lemma F_20b6c : fetch_word Plain.M.loaded_segments (0x20bb8 : word) = Some W_20b6c.
Proof. vm_refl. Qed.
Lemma D_20b6c : decode_any W_20b6c = Some (Load SZ1 false 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b70 : bv 32 := 0xfff00913.
Lemma F_20b70 : fetch_word Plain.M.loaded_segments (0x20bbc : word) = Some W_20b70.
Proof. vm_refl. Qed.
Lemma D_20b70 : decode_any W_20b70 = Some (OpImm ALU_ADD 18 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b74 : bv 32 := 0x06051263.
Lemma F_20b74 : fetch_word Plain.M.loaded_segments (0x20bc0 : word) = Some W_20b74.
Proof. vm_refl. Qed.
Lemma D_20b74 : decode_any W_20b74 = Some (Branch BC_NE 10 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b78 : bv 32 := 0x0109b503.
Lemma F_20b78 : fetch_word Plain.M.loaded_segments (0x20bc4 : word) = Some W_20b78.
Proof. vm_refl. Qed.
Lemma D_20b78 : decode_any W_20b78 = Some (Load SZ8 true 10 19 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b7c : bv 32 := 0x00051663.
Lemma F_20b7c : fetch_word Plain.M.loaded_segments (0x20bc8 : word) = Some W_20b7c.
Proof. vm_refl. Qed.
Lemma D_20b7c : decode_any W_20b7c = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b80 : bv 32 := 0x01898513.
Lemma F_20b80 : fetch_word Plain.M.loaded_segments (0x20bcc : word) = Some W_20b80.
Proof. vm_refl. Qed.
Lemma D_20b80 : decode_any W_20b80 = Some (OpImm ALU_ADD 10 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b84 : bv 32 := 0x00a9b823.
Lemma F_20b84 : fetch_word Plain.M.loaded_segments (0x20bd0 : word) = Some W_20b84.
Proof. vm_refl. Qed.
Lemma D_20b84 : decode_any W_20b84 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b88 : bv 32 := 0x0089a583.
Lemma F_20b88 : fetch_word Plain.M.loaded_segments (0x20bd4 : word) = Some W_20b88.
Proof. vm_refl. Qed.
Lemma D_20b88 : decode_any W_20b88 = Some (Load SZ4 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b8c : bv 32 := 0x02000613.
Lemma F_20b8c : fetch_word Plain.M.loaded_segments (0x20bd8 : word) = Some W_20b8c.
Proof. vm_refl. Qed.
Lemma D_20b8c : decode_any W_20b8c = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b90 : bv 32 := 0x02c59263.
Lemma F_20b90 : fetch_word Plain.M.loaded_segments (0x20bdc : word) = Some W_20b90.
Proof. vm_refl. Qed.
Lemma D_20b90 : decode_any W_20b90 = Some (Branch BC_NE 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b94 : bv 32 := 0x20800513.
Lemma F_20b94 : fetch_word Plain.M.loaded_segments (0x20be0 : word) = Some W_20b94.
Proof. vm_refl. Qed.
Lemma D_20b94 : decode_any W_20b94 = Some (OpImm ALU_ADD 10 0 520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b98 : bv 32 := 0x00100593.
Lemma F_20b98 : fetch_word Plain.M.loaded_segments (0x20be4 : word) = Some W_20b98.
Proof. vm_refl. Qed.
Lemma D_20b98 : decode_any W_20b98 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b9c : bv 32 := 0x3f4000ef.
Lemma F_20b9c : fetch_word Plain.M.loaded_segments (0x20be8 : word) = Some W_20b9c.
Proof. vm_refl. Qed.
Lemma D_20b9c : decode_any W_20b9c = Some (Jal 1 1012, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ba0 : bv 32 := 0x02050c63.
Lemma F_20ba0 : fetch_word Plain.M.loaded_segments (0x20bec : word) = Some W_20ba0.
Proof. vm_refl. Qed.
Lemma D_20ba0 : decode_any W_20ba0 = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ba4 : bv 32 := 0x00000593.
Lemma F_20ba4 : fetch_word Plain.M.loaded_segments (0x20bf0 : word) = Some W_20ba4.
Proof. vm_refl. Qed.
Lemma D_20ba4 : decode_any W_20ba4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ba8 : bv 32 := 0x0109b603.
Lemma F_20ba8 : fetch_word Plain.M.loaded_segments (0x20bf4 : word) = Some W_20ba8.
Proof. vm_refl. Qed.
Lemma D_20ba8 : decode_any W_20ba8 = Some (Load SZ8 true 12 19 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20bac : bv 32 := 0x00c53023.
Lemma F_20bac : fetch_word Plain.M.loaded_segments (0x20bf8 : word) = Some W_20bac.
Proof. vm_refl. Qed.
Lemma D_20bac : decode_any W_20bac = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20bb0 : bv 32 := 0x00a9b823.
Lemma F_20bb0 : fetch_word Plain.M.loaded_segments (0x20bfc : word) = Some W_20bb0.
Proof. vm_refl. Qed.
Lemma D_20bb0 : decode_any W_20bb0 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20bb4 : bv 32 := 0x00000913.
Lemma F_20bb4 : fetch_word Plain.M.loaded_segments (0x20c00 : word) = Some W_20bb4.
Proof. vm_refl. Qed.
Lemma D_20bb4 : decode_any W_20bb4 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20bb8 : bv 32 := 0x00359613.
Lemma F_20bb8 : fetch_word Plain.M.loaded_segments (0x20c04 : word) = Some W_20bb8.
Proof. vm_refl. Qed.
Lemma D_20bb8 : decode_any W_20bb8 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20bbc : bv 32 := 0x00c50533.
Lemma F_20bbc : fetch_word Plain.M.loaded_segments (0x20c08 : word) = Some W_20bbc.
Proof. vm_refl. Qed.
Lemma D_20bbc : decode_any W_20bbc = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20bc0 : bv 32 := 0x00000617.
Lemma F_20bc0 : fetch_word Plain.M.loaded_segments (0x20c0c : word) = Some W_20bc0.
Proof. vm_refl. Qed.
Lemma D_20bc0 : decode_any W_20bc0 = Some (Auipc 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20bc4 : bv 32 := 0x00158593.
Lemma F_20bc4 : fetch_word Plain.M.loaded_segments (0x20c10 : word) = Some W_20bc4.
Proof. vm_refl. Qed.
Lemma D_20bc4 : decode_any W_20bc4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20bc8 : bv 32 := 0x04060613.
Lemma F_20bc8 : fetch_word Plain.M.loaded_segments (0x20c14 : word) = Some W_20bc8.
Proof. vm_refl. Qed.
Lemma D_20bc8 : decode_any W_20bc8 = Some (OpImm ALU_ADD 12 12 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20bcc : bv 32 := 0x00c53423.
Lemma F_20bcc : fetch_word Plain.M.loaded_segments (0x20c18 : word) = Some W_20bcc.
Proof. vm_refl. Qed.
Lemma D_20bcc : decode_any W_20bcc = Some (Store SZ8 10 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20bd0 : bv 32 := 0x10953423.
Lemma F_20bd0 : fetch_word Plain.M.loaded_segments (0x20c1c : word) = Some W_20bd0.
Proof. vm_refl. Qed.
Lemma D_20bd0 : decode_any W_20bd0 = Some (Store SZ8 10 9 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20bd4 : bv 32 := 0x00b9a423.
Lemma F_20bd4 : fetch_word Plain.M.loaded_segments (0x20c20 : word) = Some W_20bd4.
Proof. vm_refl. Qed.
Lemma D_20bd4 : decode_any W_20bd4 = Some (Store SZ4 19 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20bd8 : bv 32 := 0x00040513.
Lemma F_20bd8 : fetch_word Plain.M.loaded_segments (0x20c24 : word) = Some W_20bd8.
Proof. vm_refl. Qed.
Lemma D_20bd8 : decode_any W_20bd8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20bdc : bv 32 := 0x1950a0ef.
Lemma F_20bdc : fetch_word Plain.M.loaded_segments (0x20c28 : word) = Some W_20bdc.
Proof. vm_refl. Qed.
Lemma D_20bdc : decode_any W_20bdc = Some (Jal 1 43412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20be0 : bv 32 := 0x00090513.
Lemma F_20be0 : fetch_word Plain.M.loaded_segments (0x20c2c : word) = Some W_20be0.
Proof. vm_refl. Qed.
Lemma D_20be0 : decode_any W_20be0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20be4 : bv 32 := 0x02813083.
Lemma F_20be4 : fetch_word Plain.M.loaded_segments (0x20c30 : word) = Some W_20be4.
Proof. vm_refl. Qed.
Lemma D_20be4 : decode_any W_20be4 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20be8 : bv 32 := 0x02013403.
Lemma F_20be8 : fetch_word Plain.M.loaded_segments (0x20c34 : word) = Some W_20be8.
Proof. vm_refl. Qed.
Lemma D_20be8 : decode_any W_20be8 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20bec : bv 32 := 0x01813483.
Lemma F_20bec : fetch_word Plain.M.loaded_segments (0x20c38 : word) = Some W_20bec.
Proof. vm_refl. Qed.
Lemma D_20bec : decode_any W_20bec = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20bf0 : bv 32 := 0x01013903.
Lemma F_20bf0 : fetch_word Plain.M.loaded_segments (0x20c3c : word) = Some W_20bf0.
Proof. vm_refl. Qed.
Lemma D_20bf0 : decode_any W_20bf0 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20bf4 : bv 32 := 0x00813983.
Lemma F_20bf4 : fetch_word Plain.M.loaded_segments (0x20c40 : word) = Some W_20bf4.
Proof. vm_refl. Qed.
Lemma D_20bf4 : decode_any W_20bf4 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20bf8 : bv 32 := 0x03010113.
Lemma F_20bf8 : fetch_word Plain.M.loaded_segments (0x20c44 : word) = Some W_20bf8.
Proof. vm_refl. Qed.
Lemma D_20bf8 : decode_any W_20bf8 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20bfc : bv 32 := 0x00008067.
Lemma F_20bfc : fetch_word Plain.M.loaded_segments (0x20c48 : word) = Some W_20bfc.
Proof. vm_refl. Qed.
Lemma D_20bfc : decode_any W_20bfc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c00 : bv 32 := 0x00050067.
Lemma F_20c00 : fetch_word Plain.M.loaded_segments (0x20c4c : word) = Some W_20c00.
Proof. vm_refl. Qed.
Lemma D_20c00 : decode_any W_20c00 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c04 : bv 32 := 0x00008067.
Lemma F_20c04 : fetch_word Plain.M.loaded_segments (0x20c50 : word) = Some W_20c04.
Proof. vm_refl. Qed.
Lemma D_20c04 : decode_any W_20c04 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c08 : bv 32 := 0xfe010113.
Lemma F_20c08 : fetch_word Plain.M.loaded_segments (0x20c54 : word) = Some W_20c08.
Proof. vm_refl. Qed.
Lemma D_20c08 : decode_any W_20c08 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c0c : bv 32 := 0x00113c23.
Lemma F_20c0c : fetch_word Plain.M.loaded_segments (0x20c58 : word) = Some W_20c0c.
Proof. vm_refl. Qed.
Lemma D_20c0c : decode_any W_20c0c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c10 : bv 32 := 0x00813823.
Lemma F_20c10 : fetch_word Plain.M.loaded_segments (0x20c5c : word) = Some W_20c10.
Proof. vm_refl. Qed.
Lemma D_20c10 : decode_any W_20c10 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c14 : bv 32 := 0x00913423.
Lemma F_20c14 : fetch_word Plain.M.loaded_segments (0x20c60 : word) = Some W_20c14.
Proof. vm_refl. Qed.
Lemma D_20c14 : decode_any W_20c14 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c18 : bv 32 := 0x0000c517.
Lemma F_20c18 : fetch_word Plain.M.loaded_segments (0x20c64 : word) = Some W_20c18.
Proof. vm_refl. Qed.
Lemma D_20c18 : decode_any W_20c18 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c1c : bv 32 := 0x0000c597.
Lemma F_20c1c : fetch_word Plain.M.loaded_segments (0x20c68 : word) = Some W_20c1c.
Proof. vm_refl. Qed.
Lemma D_20c1c : decode_any W_20c1c = Some (Auipc 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c20 : bv 32 := 0xb5453503.
Lemma F_20c20 : fetch_word Plain.M.loaded_segments (0x20c6c : word) = Some W_20c20.
Proof. vm_refl. Qed.
Lemma D_20c20 : decode_any W_20c20 = Some (Load SZ8 true 10 10 2900, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c24 : bv 32 := 0xb585b403.
Lemma F_20c24 : fetch_word Plain.M.loaded_segments (0x20c70 : word) = Some W_20c24.
Proof. vm_refl. Qed.
Lemma D_20c24 : decode_any W_20c24 = Some (Load SZ8 true 8 11 2904, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c28 : bv 32 := 0x00a47c63.
Lemma F_20c28 : fetch_word Plain.M.loaded_segments (0x20c74 : word) = Some W_20c28.
Proof. vm_refl. Qed.
Lemma D_20c28 : decode_any W_20c28 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c2c : bv 32 := 0xff853583.
Lemma F_20c2c : fetch_word Plain.M.loaded_segments (0x20c78 : word) = Some W_20c2c.
Proof. vm_refl. Qed.
Lemma D_20c2c : decode_any W_20c2c = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c30 : bv 32 := 0xff850493.
Lemma F_20c30 : fetch_word Plain.M.loaded_segments (0x20c7c : word) = Some W_20c30.
Proof. vm_refl. Qed.
Lemma D_20c30 : decode_any W_20c30 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c34 : bv 32 := 0x000580e7.
Lemma F_20c34 : fetch_word Plain.M.loaded_segments (0x20c80 : word) = Some W_20c34.
Proof. vm_refl. Qed.
Lemma D_20c34 : decode_any W_20c34 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c38 : bv 32 := 0x00048513.
Lemma F_20c38 : fetch_word Plain.M.loaded_segments (0x20c84 : word) = Some W_20c38.
Proof. vm_refl. Qed.
Lemma D_20c38 : decode_any W_20c38 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c3c : bv 32 := 0xfe9468e3.
Lemma F_20c3c : fetch_word Plain.M.loaded_segments (0x20c88 : word) = Some W_20c3c.
Proof. vm_refl. Qed.
Lemma D_20c3c : decode_any W_20c3c = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c40 : bv 32 := 0x01813083.
Lemma F_20c40 : fetch_word Plain.M.loaded_segments (0x20c8c : word) = Some W_20c40.
Proof. vm_refl. Qed.
Lemma D_20c40 : decode_any W_20c40 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c44 : bv 32 := 0x01013403.
Lemma F_20c44 : fetch_word Plain.M.loaded_segments (0x20c90 : word) = Some W_20c44.
Proof. vm_refl. Qed.
Lemma D_20c44 : decode_any W_20c44 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c48 : bv 32 := 0x00813483.
Lemma F_20c48 : fetch_word Plain.M.loaded_segments (0x20c94 : word) = Some W_20c48.
Proof. vm_refl. Qed.
Lemma D_20c48 : decode_any W_20c48 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c4c : bv 32 := 0x02010113.
Lemma F_20c4c : fetch_word Plain.M.loaded_segments (0x20c98 : word) = Some W_20c4c.
Proof. vm_refl. Qed.
Lemma D_20c4c : decode_any W_20c4c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c50 : bv 32 := 0xfb5ff06f.
Lemma F_20c50 : fetch_word Plain.M.loaded_segments (0x20c9c : word) = Some W_20c50.
Proof. vm_refl. Qed.
Lemma D_20c50 : decode_any W_20c50 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c54 : bv 32 := 0xff010113.
Lemma F_20c54 : fetch_word Plain.M.loaded_segments (0x20ca0 : word) = Some W_20c54.
Proof. vm_refl. Qed.
Lemma D_20c54 : decode_any W_20c54 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c58 : bv 32 := 0x00113423.
Lemma F_20c58 : fetch_word Plain.M.loaded_segments (0x20ca4 : word) = Some W_20c58.
Proof. vm_refl. Qed.
Lemma D_20c58 : decode_any W_20c58 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c5c : bv 32 := 0x00813023.
Lemma F_20c5c : fetch_word Plain.M.loaded_segments (0x20ca8 : word) = Some W_20c5c.
Proof. vm_refl. Qed.
Lemma D_20c5c : decode_any W_20c5c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c60 : bv 32 := 0x00000593.
Lemma F_20c60 : fetch_word Plain.M.loaded_segments (0x20cac : word) = Some W_20c60.
Proof. vm_refl. Qed.
Lemma D_20c60 : decode_any W_20c60 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c64 : bv 32 := 0x00020613.
Lemma F_20c64 : fetch_word Plain.M.loaded_segments (0x20cb0 : word) = Some W_20c64.
Proof. vm_refl. Qed.
Lemma D_20c64 : decode_any W_20c64 = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c68 : bv 32 := 0xf5862603.
Lemma F_20c68 : fetch_word Plain.M.loaded_segments (0x20cb4 : word) = Some W_20c68.
Proof. vm_refl. Qed.
Lemma D_20c68 : decode_any W_20c68 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c6c : bv 32 := 0x0003d697.
Lemma F_20c6c : fetch_word Plain.M.loaded_segments (0x20cb8 : word) = Some W_20c6c.
Proof. vm_refl. Qed.
Lemma D_20c6c : decode_any W_20c6c = Some (Auipc 13 61, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c70 : bv 32 := 0x0f868693.
Lemma F_20c70 : fetch_word Plain.M.loaded_segments (0x20cbc : word) = Some W_20c70.
Proof. vm_refl. Qed.
Lemma D_20c70 : decode_any W_20c70 = Some (OpImm ALU_ADD 13 13 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c74 : bv 32 := 0x1606a72f.
Lemma F_20c74 : fetch_word Plain.M.loaded_segments (0x20cc0 : word) = Some W_20c74.
Proof. vm_refl. Qed.
Lemma D_20c74 : decode_any W_20c74 = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c78 : bv 32 := 0x00b71663.
Lemma F_20c78 : fetch_word Plain.M.loaded_segments (0x20cc4 : word) = Some W_20c78.
Proof. vm_refl. Qed.
Lemma D_20c78 : decode_any W_20c78 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c7c : bv 32 := 0x1ec6a7af.
Lemma F_20c7c : fetch_word Plain.M.loaded_segments (0x20cc8 : word) = Some W_20c7c.
Proof. vm_refl. Qed.
Lemma D_20c7c : decode_any W_20c7c = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c80 : bv 32 := 0xfe079ae3.
Lemma F_20c80 : fetch_word Plain.M.loaded_segments (0x20ccc : word) = Some W_20c80.
Proof. vm_refl. Qed.
Lemma D_20c80 : decode_any W_20c80 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c84 : bv 32 := 0x0007059b.
Lemma F_20c84 : fetch_word Plain.M.loaded_segments (0x20cd0 : word) = Some W_20c84.
Proof. vm_refl. Qed.
Lemma D_20c84 : decode_any W_20c84 = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c88 : bv 32 := 0x02c58263.
Lemma F_20c88 : fetch_word Plain.M.loaded_segments (0x20cd4 : word) = Some W_20c88.
Proof. vm_refl. Qed.
Lemma D_20c88 : decode_any W_20c88 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c8c : bv 32 := 0x02058263.
Lemma F_20c8c : fetch_word Plain.M.loaded_segments (0x20cd8 : word) = Some W_20c8c.
Proof. vm_refl. Qed.
Lemma D_20c8c : decode_any W_20c8c = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c90 : bv 32 := 0x04900893.
Lemma F_20c90 : fetch_word Plain.M.loaded_segments (0x20cdc : word) = Some W_20c90.
Proof. vm_refl. Qed.
Lemma D_20c90 : decode_any W_20c90 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c94 : bv 32 := 0x00000593.
Lemma F_20c94 : fetch_word Plain.M.loaded_segments (0x20ce0 : word) = Some W_20c94.
Proof. vm_refl. Qed.
Lemma D_20c94 : decode_any W_20c94 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c98 : bv 32 := 0x00000613.
Lemma F_20c98 : fetch_word Plain.M.loaded_segments (0x20ce4 : word) = Some W_20c98.
Proof. vm_refl. Qed.
Lemma D_20c98 : decode_any W_20c98 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c9c : bv 32 := 0x00000693.
Lemma F_20c9c : fetch_word Plain.M.loaded_segments (0x20ce8 : word) = Some W_20c9c.
Proof. vm_refl. Qed.
Lemma D_20c9c : decode_any W_20c9c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ca0 : bv 32 := 0x00000513.
Lemma F_20ca0 : fetch_word Plain.M.loaded_segments (0x20cec : word) = Some W_20ca0.
Proof. vm_refl. Qed.
Lemma D_20ca0 : decode_any W_20ca0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ca4 : bv 32 := 0x00000073.
Lemma F_20ca4 : fetch_word Plain.M.loaded_segments (0x20cf0 : word) = Some W_20ca4.
Proof. vm_refl. Qed.
Lemma E_20ca4 : is_ecall W_20ca4 = true.
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ca8 : bv 32 := 0xff9ff06f.
Lemma F_20ca8 : fetch_word Plain.M.loaded_segments (0x20cf4 : word) = Some W_20ca8.
Proof. vm_refl. Qed.
Lemma D_20ca8 : decode_any W_20ca8 = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20cac : bv 32 := 0x00000023.
Lemma F_20cac : fetch_word Plain.M.loaded_segments (0x20cf8 : word) = Some W_20cac.
Proof. vm_refl. Qed.
Lemma D_20cac : decode_any W_20cac = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20cb0 : bv 32 := 0x00050413.
Lemma F_20cb0 : fetch_word Plain.M.loaded_segments (0x20cfc : word) = Some W_20cb0.
Proof. vm_refl. Qed.
Lemma D_20cb0 : decode_any W_20cb0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20cb4 : bv 32 := 0xdbdff0ef.
Lemma F_20cb4 : fetch_word Plain.M.loaded_segments (0x20d00 : word) = Some W_20cb4.
Proof. vm_refl. Qed.
Lemma D_20cb4 : decode_any W_20cb4 = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20cb8 : bv 32 := 0xf51ff0ef.
Lemma F_20cb8 : fetch_word Plain.M.loaded_segments (0x20d04 : word) = Some W_20cb8.
Proof. vm_refl. Qed.
Lemma D_20cb8 : decode_any W_20cb8 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20cbc : bv 32 := 0x280020ef.
Lemma F_20cbc : fetch_word Plain.M.loaded_segments (0x20d08 : word) = Some W_20cbc.
Proof. vm_refl. Qed.
Lemma D_20cbc : decode_any W_20cbc = Some (Jal 1 8832, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20cc0 : bv 32 := 0x00040513.
Lemma F_20cc0 : fetch_word Plain.M.loaded_segments (0x20d0c : word) = Some W_20cc0.
Proof. vm_refl. Qed.
Lemma D_20cc0 : decode_any W_20cc0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20cc4 : bv 32 := 0xd91ff0ef.
Lemma F_20cc4 : fetch_word Plain.M.loaded_segments (0x20d10 : word) = Some W_20cc4.
Proof. vm_refl. Qed.
Lemma D_20cc4 : decode_any W_20cc4 = Some (Jal 1 2096528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2e8 : bv 32 := 0x00033597.
Lemma F_2b2e8 : fetch_word Plain.M.loaded_segments (0x2b334 : word) = Some W_2b2e8.
Proof. vm_refl. Qed.
Lemma D_2b2e8 : decode_any W_2b2e8 = Some (Auipc 11 51, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2ec : bv 32 := 0xaa758683.
Lemma F_2b2ec : fetch_word Plain.M.loaded_segments (0x2b338 : word) = Some W_2b2ec.
Proof. vm_refl. Qed.
Lemma D_2b2ec : decode_any W_2b2ec = Some (Load SZ1 true 13 11 2727, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2f0 : bv 32 := 0x1e068863.
Lemma F_2b2f0 : fetch_word Plain.M.loaded_segments (0x2b33c : word) = Some W_2b2f0.
Proof. vm_refl. Qed.
Lemma D_2b2f0 : decode_any W_2b2f0 = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b4e0 : bv 32 := 0x00008067.
Lemma F_2b4e0 : fetch_word Plain.M.loaded_segments (0x2b52c : word) = Some W_2b4e0.
Proof. vm_refl. Qed.
Lemma D_2b4e0 : decode_any W_2b4e0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b570 : bv 32 := 0x00052583.
Lemma F_2b570 : fetch_word Plain.M.loaded_segments (0x2b5bc : word) = Some W_2b570.
Proof. vm_refl. Qed.
Lemma D_2b570 : decode_any W_2b570 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b574 : bv 32 := 0x0005c463.
Lemma F_2b574 : fetch_word Plain.M.loaded_segments (0x2b5c0 : word) = Some W_2b574.
Proof. vm_refl. Qed.
Lemma D_2b574 : decode_any W_2b574 = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b578 : bv 32 := 0x00008067.
Lemma F_2b578 : fetch_word Plain.M.loaded_segments (0x2b5c4 : word) = Some W_2b578.
Proof. vm_refl. Qed.
Lemma D_2b578 : decode_any W_2b578 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

