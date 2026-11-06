(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_61240 : bv 32 := 0xfff48693.
Lemma F_61240 : fetch_word AsanUbsan.M.loaded_segments (0x61240 : word) = Some W_61240.
Proof. vm_refl. Qed.
Lemma D_61240 : decode_any W_61240 = Some (OpImm ALU_ADD 13 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61244 : bv 32 := 0x00d4b733.
Lemma F_61244 : fetch_word AsanUbsan.M.loaded_segments (0x61244 : word) = Some W_61244.
Proof. vm_refl. Qed.
Lemma D_61244 : decode_any W_61244 = Some (Op ALU_SLTU 14 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61248 : bv 32 := 0xfff70713.
Lemma F_61248 : fetch_word AsanUbsan.M.loaded_segments (0x61248 : word) = Some W_61248.
Proof. vm_refl. Qed.
Lemma D_61248 : decode_any W_61248 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6124c : bv 32 := 0x00d77733.
Lemma F_6124c : fetch_word AsanUbsan.M.loaded_segments (0x6124c : word) = Some W_6124c.
Proof. vm_refl. Qed.
Lemma D_6124c : decode_any W_6124c = Some (Op ALU_AND 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61250 : bv 32 := 0x1ca77c63.
Lemma F_61250 : fetch_word AsanUbsan.M.loaded_segments (0x61250 : word) = Some W_61250.
Proof. vm_refl. Qed.
Lemma D_61250 : decode_any W_61250 = Some (Branch BC_GEU 14 10 472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61254 : bv 32 := 0x00075797.
Lemma F_61254 : fetch_word AsanUbsan.M.loaded_segments (0x61254 : word) = Some W_61254.
Proof. vm_refl. Qed.
Lemma D_61254 : decode_any W_61254 = Some (Auipc 15 117, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61258 : bv 32 := 0x27c7b783.
Lemma F_61258 : fetch_word AsanUbsan.M.loaded_segments (0x61258 : word) = Some W_61258.
Proof. vm_refl. Qed.
Lemma D_61258 : decode_any W_61258 = Some (Load SZ8 true 15 15 636, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6125c : bv 32 := 0x00075817.
Lemma F_6125c : fetch_word AsanUbsan.M.loaded_segments (0x6125c : word) = Some W_6125c.
Proof. vm_refl. Qed.
Lemma D_6125c : decode_any W_6125c = Some (Auipc 16 117, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61260 : bv 32 := 0x27c83803.
Lemma F_61260 : fetch_word AsanUbsan.M.loaded_segments (0x61260 : word) = Some W_61260.
Proof. vm_refl. Qed.
Lemma D_61260 : decode_any W_61260 = Some (Load SZ8 true 16 16 636, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61264 : bv 32 := 0x0007b883.
Lemma F_61264 : fetch_word AsanUbsan.M.loaded_segments (0x61264 : word) = Some W_61264.
Proof. vm_refl. Qed.
Lemma D_61264 : decode_any W_61264 = Some (Load SZ8 true 17 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61268 : bv 32 := 0x00083783.
Lemma F_61268 : fetch_word AsanUbsan.M.loaded_segments (0x61268 : word) = Some W_61268.
Proof. vm_refl. Qed.
Lemma D_61268 : decode_any W_61268 = Some (Load SZ8 true 15 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6126c : bv 32 := 0xfff88813.
Lemma F_6126c : fetch_word AsanUbsan.M.loaded_segments (0x6126c : word) = Some W_6126c.
Proof. vm_refl. Qed.
Lemma D_6126c : decode_any W_6126c = Some (OpImm ALU_ADD 16 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61270 : bv 32 := 0x00a87463.
Lemma F_61270 : fetch_word AsanUbsan.M.loaded_segments (0x61270 : word) = Some W_61270.
Proof. vm_refl. Qed.
Lemma D_61270 : decode_any W_61270 = Some (Branch BC_GEU 16 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61274 : bv 32 := 0x1aa7fa63.
Lemma F_61274 : fetch_word AsanUbsan.M.loaded_segments (0x61274 : word) = Some W_61274.
Proof. vm_refl. Qed.
Lemma D_61274 : decode_any W_61274 = Some (Branch BC_GEU 15 10 436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61278 : bv 32 := 0x00075297.
Lemma F_61278 : fetch_word AsanUbsan.M.loaded_segments (0x61278 : word) = Some W_61278.
Proof. vm_refl. Qed.
Lemma D_61278 : decode_any W_61278 = Some (Auipc 5 117, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6127c : bv 32 := 0x2682b283.
Lemma F_6127c : fetch_word AsanUbsan.M.loaded_segments (0x6127c : word) = Some W_6127c.
Proof. vm_refl. Qed.
Lemma D_6127c : decode_any W_6127c = Some (Load SZ8 true 5 5 616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61280 : bv 32 := 0x0002be03.
Lemma F_61280 : fetch_word AsanUbsan.M.loaded_segments (0x61280 : word) = Some W_61280.
Proof. vm_refl. Qed.
Lemma D_61280 : decode_any W_61280 = Some (Load SZ8 true 28 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61284 : bv 32 := 0x003e5313.
Lemma F_61284 : fetch_word AsanUbsan.M.loaded_segments (0x61284 : word) = Some W_61284.
Proof. vm_refl. Qed.
Lemma D_61284 : decode_any W_61284 = Some (ShiftImm ALU_SRL 6 28 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61288 : bv 32 := 0x009303b3.
Lemma F_61288 : fetch_word AsanUbsan.M.loaded_segments (0x61288 : word) = Some W_61288.
Proof. vm_refl. Qed.
Lemma D_61288 : decode_any W_61288 = Some (Op ALU_ADD 7 6 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6128c : bv 32 := 0x00ae6463.
Lemma F_6128c : fetch_word AsanUbsan.M.loaded_segments (0x6128c : word) = Some W_6128c.
Proof. vm_refl. Qed.
Lemma D_6128c : decode_any W_6128c = Some (Branch BC_LTU 28 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61290 : bv 32 := 0x0ca3e463.
Lemma F_61290 : fetch_word AsanUbsan.M.loaded_segments (0x61290 : word) = Some W_61290.
Proof. vm_refl. Qed.
Lemma D_61290 : decode_any W_61290 = Some (Branch BC_LTU 7 10 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61294 : bv 32 := 0x00075e17.
Lemma F_61294 : fetch_word AsanUbsan.M.loaded_segments (0x61294 : word) = Some W_61294.
Proof. vm_refl. Qed.
Lemma D_61294 : decode_any W_61294 = Some (Auipc 28 117, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61298 : bv 32 := 0x22ce3e03.
Lemma F_61298 : fetch_word AsanUbsan.M.loaded_segments (0x61298 : word) = Some W_61298.
Proof. vm_refl. Qed.
Lemma D_61298 : decode_any W_61298 = Some (Load SZ8 true 28 28 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6129c : bv 32 := 0x04ee4e03.
Lemma F_6129c : fetch_word AsanUbsan.M.loaded_segments (0x6129c : word) = Some W_6129c.
Proof. vm_refl. Qed.
Lemma D_6129c : decode_any W_6129c = Some (Load SZ1 false 28 28 78, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_612a0 : bv 32 := 0x3e0e1063.
Lemma F_612a0 : fetch_word AsanUbsan.M.loaded_segments (0x612a0 : word) = Some W_612a0.
Proof. vm_refl. Qed.
Lemma D_612a0 : decode_any W_612a0 = Some (Branch BC_NE 28 0 992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_612a4 : bv 32 := 0x04088e63.
Lemma F_612a4 : fetch_word AsanUbsan.M.loaded_segments (0x612a4 : word) = Some W_612a4.
Proof. vm_refl. Qed.
Lemma D_612a4 : decode_any W_612a4 = Some (Branch BC_EQ 17 0 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_612a8 : bv 32 := 0x0038d393.
Lemma F_612a8 : fetch_word AsanUbsan.M.loaded_segments (0x612a8 : word) = Some W_612a8.
Proof. vm_refl. Qed.
Lemma D_612a8 : decode_any W_612a8 = Some (ShiftImm ALU_SRL 7 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_612ac : bv 32 := 0x00d383b3.
Lemma F_612ac : fetch_word AsanUbsan.M.loaded_segments (0x612ac : word) = Some W_612ac.
Proof. vm_refl. Qed.
Lemma D_612ac : decode_any W_612ac = Some (Op ALU_ADD 7 7 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_612b0 : bv 32 := 0x06a3fe63.
Lemma F_612b0 : fetch_word AsanUbsan.M.loaded_segments (0x612b0 : word) = Some W_612b0.
Proof. vm_refl. Qed.
Lemma D_612b0 : decode_any W_612b0 = Some (Branch BC_GEU 7 10 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_612b4 : bv 32 := 0x00148393.
Lemma F_612b4 : fetch_word AsanUbsan.M.loaded_segments (0x612b4 : word) = Some W_612b4.
Proof. vm_refl. Qed.
Lemma D_612b4 : decode_any W_612b4 = Some (OpImm ALU_ADD 7 9 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_612b8 : bv 32 := 0x00a86863.
Lemma F_612b8 : fetch_word AsanUbsan.M.loaded_segments (0x612b8 : word) = Some W_612b8.
Proof. vm_refl. Qed.
Lemma D_612b8 : decode_any W_612b8 = Some (Branch BC_LTU 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_612bc : bv 32 := 0x0037de13.
Lemma F_612bc : fetch_word AsanUbsan.M.loaded_segments (0x612bc : word) = Some W_612bc.
Proof. vm_refl. Qed.
Lemma D_612bc : decode_any W_612bc = Some (ShiftImm ALU_SRL 28 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_612c0 : bv 32 := 0x007e0e33.
Lemma F_612c0 : fetch_word AsanUbsan.M.loaded_segments (0x612c0 : word) = Some W_612c0.
Proof. vm_refl. Qed.
Lemma D_612c0 : decode_any W_612c0 = Some (Op ALU_ADD 28 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_612c4 : bv 32 := 0x09c57a63.
Lemma F_612c4 : fetch_word AsanUbsan.M.loaded_segments (0x612c4 : word) = Some W_612c4.
Proof. vm_refl. Qed.
Lemma D_612c4 : decode_any W_612c4 = Some (Branch BC_GEU 10 28 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_612c8 : bv 32 := 0x00178e13.
Lemma F_612c8 : fetch_word AsanUbsan.M.loaded_segments (0x612c8 : word) = Some W_612c8.
Proof. vm_refl. Qed.
Lemma D_612c8 : decode_any W_612c8 = Some (OpImm ALU_ADD 28 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_612cc : bv 32 := 0x3bc56a63.
Lemma F_612cc : fetch_word AsanUbsan.M.loaded_segments (0x612cc : word) = Some W_612cc.
Proof. vm_refl. Qed.
Lemma D_612cc : decode_any W_612cc = Some (Branch BC_LTU 10 28 948, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_612d0 : bv 32 := 0x00730333.
Lemma F_612d0 : fetch_word AsanUbsan.M.loaded_segments (0x612d0 : word) = Some W_612d0.
Proof. vm_refl. Qed.
Lemma D_612d0 : decode_any W_612d0 = Some (Op ALU_ADD 6 6 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_612d4 : bv 32 := 0x00335313.
Lemma F_612d4 : fetch_word AsanUbsan.M.loaded_segments (0x612d4 : word) = Some W_612d4.
Proof. vm_refl. Qed.
Lemma D_612d4 : decode_any W_612d4 = Some (ShiftImm ALU_SRL 6 6 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_612d8 : bv 32 := 0x0480006f.
Lemma F_612d8 : fetch_word AsanUbsan.M.loaded_segments (0x612d8 : word) = Some W_612d8.
Proof. vm_refl. Qed.
Lemma D_612d8 : decode_any W_612d8 = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_612dc : bv 32 := 0x03813083.
Lemma F_612dc : fetch_word AsanUbsan.M.loaded_segments (0x612dc : word) = Some W_612dc.
Proof. vm_refl. Qed.
Lemma D_612dc : decode_any W_612dc = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_612e0 : bv 32 := 0x03013403.
Lemma F_612e0 : fetch_word AsanUbsan.M.loaded_segments (0x612e0 : word) = Some W_612e0.
Proof. vm_refl. Qed.
Lemma D_612e0 : decode_any W_612e0 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_612e4 : bv 32 := 0x02813483.
Lemma F_612e4 : fetch_word AsanUbsan.M.loaded_segments (0x612e4 : word) = Some W_612e4.
Proof. vm_refl. Qed.
Lemma D_612e4 : decode_any W_612e4 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_612e8 : bv 32 := 0x02013903.
Lemma F_612e8 : fetch_word AsanUbsan.M.loaded_segments (0x612e8 : word) = Some W_612e8.
Proof. vm_refl. Qed.
Lemma D_612e8 : decode_any W_612e8 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_612ec : bv 32 := 0x01813983.
Lemma F_612ec : fetch_word AsanUbsan.M.loaded_segments (0x612ec : word) = Some W_612ec.
Proof. vm_refl. Qed.
Lemma D_612ec : decode_any W_612ec = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_612f0 : bv 32 := 0x01013a03.
Lemma F_612f0 : fetch_word AsanUbsan.M.loaded_segments (0x612f0 : word) = Some W_612f0.
Proof. vm_refl. Qed.
Lemma D_612f0 : decode_any W_612f0 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_612f4 : bv 32 := 0x00813a83.
Lemma F_612f4 : fetch_word AsanUbsan.M.loaded_segments (0x612f4 : word) = Some W_612f4.
Proof. vm_refl. Qed.
Lemma D_612f4 : decode_any W_612f4 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_612f8 : bv 32 := 0x04010113.
Lemma F_612f8 : fetch_word AsanUbsan.M.loaded_segments (0x612f8 : word) = Some W_612f8.
Proof. vm_refl. Qed.
Lemma D_612f8 : decode_any W_612f8 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_612fc : bv 32 := 0x00008067.
Lemma F_612fc : fetch_word AsanUbsan.M.loaded_segments (0x612fc : word) = Some W_612fc.
Proof. vm_refl. Qed.
Lemma D_612fc : decode_any W_612fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61300 : bv 32 := 0x04048463.
Lemma F_61300 : fetch_word AsanUbsan.M.loaded_segments (0x61300 : word) = Some W_61300.
Proof. vm_refl. Qed.
Lemma D_61300 : decode_any W_61300 = Some (Branch BC_EQ 9 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61304 : bv 32 := 0x0036d313.
Lemma F_61304 : fetch_word AsanUbsan.M.loaded_segments (0x61304 : word) = Some W_61304.
Proof. vm_refl. Qed.
Lemma D_61304 : decode_any W_61304 = Some (ShiftImm ALU_SRL 6 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61308 : bv 32 := 0x00930333.
Lemma F_61308 : fetch_word AsanUbsan.M.loaded_segments (0x61308 : word) = Some W_61308.
Proof. vm_refl. Qed.
Lemma D_61308 : decode_any W_61308 = Some (Op ALU_ADD 6 6 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6130c : bv 32 := 0x00030663.
Lemma F_6130c : fetch_word AsanUbsan.M.loaded_segments (0x6130c : word) = Some W_6130c.
Proof. vm_refl. Qed.
Lemma D_6130c : decode_any W_6130c = Some (Branch BC_EQ 6 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61310 : bv 32 := 0x00130313.
Lemma F_61310 : fetch_word AsanUbsan.M.loaded_segments (0x61310 : word) = Some W_61310.
Proof. vm_refl. Qed.
Lemma D_61310 : decode_any W_61310 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61314 : bv 32 := 0x36656663.
Lemma F_61314 : fetch_word AsanUbsan.M.loaded_segments (0x61314 : word) = Some W_61314.
Proof. vm_refl. Qed.
Lemma D_61314 : decode_any W_61314 = Some (Branch BC_LTU 10 6 876, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61318 : bv 32 := 0x00138393.
Lemma F_61318 : fetch_word AsanUbsan.M.loaded_segments (0x61318 : word) = Some W_61318.
Proof. vm_refl. Qed.
Lemma D_61318 : decode_any W_61318 = Some (OpImm ALU_ADD 7 7 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6131c : bv 32 := 0x0033d313.
Lemma F_6131c : fetch_word AsanUbsan.M.loaded_segments (0x6131c : word) = Some W_6131c.
Proof. vm_refl. Qed.
Lemma D_6131c : decode_any W_6131c = Some (ShiftImm ALU_SRL 6 7 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61320 : bv 32 := 0x00d30333.
Lemma F_61320 : fetch_word AsanUbsan.M.loaded_segments (0x61320 : word) = Some W_61320.
Proof. vm_refl. Qed.
Lemma D_61320 : decode_any W_61320 = Some (Op ALU_ADD 6 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61324 : bv 32 := 0x02a37a63.
Lemma F_61324 : fetch_word AsanUbsan.M.loaded_segments (0x61324 : word) = Some W_61324.
Proof. vm_refl. Qed.
Lemma D_61324 : decode_any W_61324 = Some (Branch BC_GEU 6 10 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61328 : bv 32 := 0x3580006f.
Lemma F_61328 : fetch_word AsanUbsan.M.loaded_segments (0x61328 : word) = Some W_61328.
Proof. vm_refl. Qed.
Lemma D_61328 : decode_any W_61328 = Some (Jal 0 856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6132c : bv 32 := 0x02048663.
Lemma F_6132c : fetch_word AsanUbsan.M.loaded_segments (0x6132c : word) = Some W_6132c.
Proof. vm_refl. Qed.
Lemma D_6132c : decode_any W_6132c = Some (Branch BC_EQ 9 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61330 : bv 32 := 0x0036d313.
Lemma F_61330 : fetch_word AsanUbsan.M.loaded_segments (0x61330 : word) = Some W_61330.
Proof. vm_refl. Qed.
Lemma D_61330 : decode_any W_61330 = Some (ShiftImm ALU_SRL 6 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61334 : bv 32 := 0x00930333.
Lemma F_61334 : fetch_word AsanUbsan.M.loaded_segments (0x61334 : word) = Some W_61334.
Proof. vm_refl. Qed.
Lemma D_61334 : decode_any W_61334 = Some (Op ALU_ADD 6 6 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61338 : bv 32 := 0x02030063.
Lemma F_61338 : fetch_word AsanUbsan.M.loaded_segments (0x61338 : word) = Some W_61338.
Proof. vm_refl. Qed.
Lemma D_61338 : decode_any W_61338 = Some (Branch BC_EQ 6 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6133c : bv 32 := 0x00130313.
Lemma F_6133c : fetch_word AsanUbsan.M.loaded_segments (0x6133c : word) = Some W_6133c.
Proof. vm_refl. Qed.
Lemma D_6133c : decode_any W_6133c = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61340 : bv 32 := 0x00657c63.
Lemma F_61340 : fetch_word AsanUbsan.M.loaded_segments (0x61340 : word) = Some W_61340.
Proof. vm_refl. Qed.
Lemma D_61340 : decode_any W_61340 = Some (Branch BC_GEU 10 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61344 : bv 32 := 0x33c0006f.
Lemma F_61344 : fetch_word AsanUbsan.M.loaded_segments (0x61344 : word) = Some W_61344.
Proof. vm_refl. Qed.
Lemma D_61344 : decode_any W_61344 = Some (Jal 0 828, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61348 : bv 32 := 0x00130313.
Lemma F_61348 : fetch_word AsanUbsan.M.loaded_segments (0x61348 : word) = Some W_61348.
Proof. vm_refl. Qed.
Lemma D_61348 : decode_any W_61348 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6134c : bv 32 := 0x00335313.
Lemma F_6134c : fetch_word AsanUbsan.M.loaded_segments (0x6134c : word) = Some W_6134c.
Proof. vm_refl. Qed.
Lemma D_6134c : decode_any W_6134c = Some (ShiftImm ALU_SRL 6 6 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61350 : bv 32 := 0xfff30313.
Lemma F_61350 : fetch_word AsanUbsan.M.loaded_segments (0x61350 : word) = Some W_61350.
Proof. vm_refl. Qed.
Lemma D_61350 : decode_any W_61350 = Some (OpImm ALU_ADD 6 6 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61354 : bv 32 := 0x32a36663.
Lemma F_61354 : fetch_word AsanUbsan.M.loaded_segments (0x61354 : word) = Some W_61354.
Proof. vm_refl. Qed.
Lemma D_61354 : decode_any W_61354 = Some (Branch BC_LTU 6 10 812, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61358 : bv 32 := 0x0002b383.
Lemma F_61358 : fetch_word AsanUbsan.M.loaded_segments (0x61358 : word) = Some W_61358.
Proof. vm_refl. Qed.
Lemma D_61358 : decode_any W_61358 = Some (Load SZ8 true 7 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6135c : bv 32 := 0x0033d293.
Lemma F_6135c : fetch_word AsanUbsan.M.loaded_segments (0x6135c : word) = Some W_6135c.
Proof. vm_refl. Qed.
Lemma D_6135c : decode_any W_6135c = Some (ShiftImm ALU_SRL 5 7 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61360 : bv 32 := 0x00928333.
Lemma F_61360 : fetch_word AsanUbsan.M.loaded_segments (0x61360 : word) = Some W_61360.
Proof. vm_refl. Qed.
Lemma D_61360 : decode_any W_61360 = Some (Op ALU_ADD 6 5 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61364 : bv 32 := 0x00a3e463.
Lemma F_61364 : fetch_word AsanUbsan.M.loaded_segments (0x61364 : word) = Some W_61364.
Proof. vm_refl. Qed.
Lemma D_61364 : decode_any W_61364 = Some (Branch BC_LTU 7 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61368 : bv 32 := 0x0ca36063.
Lemma F_61368 : fetch_word AsanUbsan.M.loaded_segments (0x61368 : word) = Some W_61368.
Proof. vm_refl. Qed.
Lemma D_61368 : decode_any W_61368 = Some (Branch BC_LTU 6 10 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6136c : bv 32 := 0x00075397.
Lemma F_6136c : fetch_word AsanUbsan.M.loaded_segments (0x6136c : word) = Some W_6136c.
Proof. vm_refl. Qed.
Lemma D_6136c : decode_any W_6136c = Some (Auipc 7 117, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61370 : bv 32 := 0x1543b383.
Lemma F_61370 : fetch_word AsanUbsan.M.loaded_segments (0x61370 : word) = Some W_61370.
Proof. vm_refl. Qed.
Lemma D_61370 : decode_any W_61370 = Some (Load SZ8 true 7 7 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61374 : bv 32 := 0x04e3c383.
Lemma F_61374 : fetch_word AsanUbsan.M.loaded_segments (0x61374 : word) = Some W_61374.
Proof. vm_refl. Qed.
Lemma D_61374 : decode_any W_61374 = Some (Load SZ1 false 7 7 78, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61378 : bv 32 := 0x08039063.
Lemma F_61378 : fetch_word AsanUbsan.M.loaded_segments (0x61378 : word) = Some W_61378.
Proof. vm_refl. Qed.
Lemma D_61378 : decode_any W_61378 = Some (Branch BC_NE 7 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6137c : bv 32 := 0x02088c63.
Lemma F_6137c : fetch_word AsanUbsan.M.loaded_segments (0x6137c : word) = Some W_6137c.
Proof. vm_refl. Qed.
Lemma D_6137c : decode_any W_6137c = Some (Branch BC_EQ 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61380 : bv 32 := 0x0038d893.
Lemma F_61380 : fetch_word AsanUbsan.M.loaded_segments (0x61380 : word) = Some W_61380.
Proof. vm_refl. Qed.
Lemma D_61380 : decode_any W_61380 = Some (ShiftImm ALU_SRL 17 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61384 : bv 32 := 0x00d888b3.
Lemma F_61384 : fetch_word AsanUbsan.M.loaded_segments (0x61384 : word) = Some W_61384.
Proof. vm_refl. Qed.
Lemma D_61384 : decode_any W_61384 = Some (Op ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61388 : bv 32 := 0x04a8fc63.
Lemma F_61388 : fetch_word AsanUbsan.M.loaded_segments (0x61388 : word) = Some W_61388.
Proof. vm_refl. Qed.
Lemma D_61388 : decode_any W_61388 = Some (Branch BC_GEU 17 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6138c : bv 32 := 0x00148893.
Lemma F_6138c : fetch_word AsanUbsan.M.loaded_segments (0x6138c : word) = Some W_6138c.
Proof. vm_refl. Qed.
Lemma D_6138c : decode_any W_6138c = Some (OpImm ALU_ADD 17 9 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61390 : bv 32 := 0x00a86863.
Lemma F_61390 : fetch_word AsanUbsan.M.loaded_segments (0x61390 : word) = Some W_61390.
Proof. vm_refl. Qed.
Lemma D_61390 : decode_any W_61390 = Some (Branch BC_LTU 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61394 : bv 32 := 0x0037d813.
Lemma F_61394 : fetch_word AsanUbsan.M.loaded_segments (0x61394 : word) = Some W_61394.
Proof. vm_refl. Qed.
Lemma D_61394 : decode_any W_61394 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61398 : bv 32 := 0x01180833.
Lemma F_61398 : fetch_word AsanUbsan.M.loaded_segments (0x61398 : word) = Some W_61398.
Proof. vm_refl. Qed.
Lemma D_61398 : decode_any W_61398 = Some (Op ALU_ADD 16 16 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6139c : bv 32 := 0x09057663.
Lemma F_6139c : fetch_word AsanUbsan.M.loaded_segments (0x6139c : word) = Some W_6139c.
Proof. vm_refl. Qed.
Lemma D_6139c : decode_any W_6139c = Some (Branch BC_GEU 10 16 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613a0 : bv 32 := 0x00178793.
Lemma F_613a0 : fetch_word AsanUbsan.M.loaded_segments (0x613a0 : word) = Some W_613a0.
Proof. vm_refl. Qed.
Lemma D_613a0 : decode_any W_613a0 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613a4 : bv 32 := 0x04f56a63.
Lemma F_613a4 : fetch_word AsanUbsan.M.loaded_segments (0x613a4 : word) = Some W_613a4.
Proof. vm_refl. Qed.
Lemma D_613a4 : decode_any W_613a4 = Some (Branch BC_LTU 10 15 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613a8 : bv 32 := 0x011288b3.
Lemma F_613a8 : fetch_word AsanUbsan.M.loaded_segments (0x613a8 : word) = Some W_613a8.
Proof. vm_refl. Qed.
Lemma D_613a8 : decode_any W_613a8 = Some (Op ALU_ADD 17 5 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613ac : bv 32 := 0x0038d793.
Lemma F_613ac : fetch_word AsanUbsan.M.loaded_segments (0x613ac : word) = Some W_613ac.
Proof. vm_refl. Qed.
Lemma D_613ac : decode_any W_613ac = Some (ShiftImm ALU_SRL 15 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613b0 : bv 32 := 0x0240006f.
Lemma F_613b0 : fetch_word AsanUbsan.M.loaded_segments (0x613b0 : word) = Some W_613b0.
Proof. vm_refl. Qed.
Lemma D_613b0 : decode_any W_613b0 = Some (Jal 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613b4 : bv 32 := 0x06048263.
Lemma F_613b4 : fetch_word AsanUbsan.M.loaded_segments (0x613b4 : word) = Some W_613b4.
Proof. vm_refl. Qed.
Lemma D_613b4 : decode_any W_613b4 = Some (Branch BC_EQ 9 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613b8 : bv 32 := 0x0036d793.
Lemma F_613b8 : fetch_word AsanUbsan.M.loaded_segments (0x613b8 : word) = Some W_613b8.
Proof. vm_refl. Qed.
Lemma D_613b8 : decode_any W_613b8 = Some (ShiftImm ALU_SRL 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613bc : bv 32 := 0x009787b3.
Lemma F_613bc : fetch_word AsanUbsan.M.loaded_segments (0x613bc : word) = Some W_613bc.
Proof. vm_refl. Qed.
Lemma D_613bc : decode_any W_613bc = Some (Op ALU_ADD 15 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613c0 : bv 32 := 0x00078663.
Lemma F_613c0 : fetch_word AsanUbsan.M.loaded_segments (0x613c0 : word) = Some W_613c0.
Proof. vm_refl. Qed.
Lemma D_613c0 : decode_any W_613c0 = Some (Branch BC_EQ 15 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613c4 : bv 32 := 0x00178793.
Lemma F_613c4 : fetch_word AsanUbsan.M.loaded_segments (0x613c4 : word) = Some W_613c4.
Proof. vm_refl. Qed.
Lemma D_613c4 : decode_any W_613c4 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613c8 : bv 32 := 0x02f56863.
Lemma F_613c8 : fetch_word AsanUbsan.M.loaded_segments (0x613c8 : word) = Some W_613c8.
Proof. vm_refl. Qed.
Lemma D_613c8 : decode_any W_613c8 = Some (Branch BC_LTU 10 15 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613cc : bv 32 := 0x00130313.
Lemma F_613cc : fetch_word AsanUbsan.M.loaded_segments (0x613cc : word) = Some W_613cc.
Proof. vm_refl. Qed.
Lemma D_613cc : decode_any W_613cc = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613d0 : bv 32 := 0x00335793.
Lemma F_613d0 : fetch_word AsanUbsan.M.loaded_segments (0x613d0 : word) = Some W_613d0.
Proof. vm_refl. Qed.
Lemma D_613d0 : decode_any W_613d0 = Some (ShiftImm ALU_SRL 15 6 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613d4 : bv 32 := 0x00d787b3.
Lemma F_613d4 : fetch_word AsanUbsan.M.loaded_segments (0x613d4 : word) = Some W_613d4.
Proof. vm_refl. Qed.
Lemma D_613d4 : decode_any W_613d4 = Some (Op ALU_ADD 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613d8 : bv 32 := 0x04a7f863.
Lemma F_613d8 : fetch_word AsanUbsan.M.loaded_segments (0x613d8 : word) = Some W_613d8.
Proof. vm_refl. Qed.
Lemma D_613d8 : decode_any W_613d8 = Some (Branch BC_GEU 15 10 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613dc : bv 32 := 0x01c0006f.
Lemma F_613dc : fetch_word AsanUbsan.M.loaded_segments (0x613dc : word) = Some W_613dc.
Proof. vm_refl. Qed.
Lemma D_613dc : decode_any W_613dc = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613e0 : bv 32 := 0x04048463.
Lemma F_613e0 : fetch_word AsanUbsan.M.loaded_segments (0x613e0 : word) = Some W_613e0.
Proof. vm_refl. Qed.
Lemma D_613e0 : decode_any W_613e0 = Some (Branch BC_EQ 9 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613e4 : bv 32 := 0x0036d793.
Lemma F_613e4 : fetch_word AsanUbsan.M.loaded_segments (0x613e4 : word) = Some W_613e4.
Proof. vm_refl. Qed.
Lemma D_613e4 : decode_any W_613e4 = Some (ShiftImm ALU_SRL 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613e8 : bv 32 := 0x009787b3.
Lemma F_613e8 : fetch_word AsanUbsan.M.loaded_segments (0x613e8 : word) = Some W_613e8.
Proof. vm_refl. Qed.
Lemma D_613e8 : decode_any W_613e8 = Some (Op ALU_ADD 15 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613ec : bv 32 := 0x02078e63.
Lemma F_613ec : fetch_word AsanUbsan.M.loaded_segments (0x613ec : word) = Some W_613ec.
Proof. vm_refl. Qed.
Lemma D_613ec : decode_any W_613ec = Some (Branch BC_EQ 15 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613f0 : bv 32 := 0x00178793.
Lemma F_613f0 : fetch_word AsanUbsan.M.loaded_segments (0x613f0 : word) = Some W_613f0.
Proof. vm_refl. Qed.
Lemma D_613f0 : decode_any W_613f0 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613f4 : bv 32 := 0x02f57a63.
Lemma F_613f4 : fetch_word AsanUbsan.M.loaded_segments (0x613f4 : word) = Some W_613f4.
Proof. vm_refl. Qed.
Lemma D_613f4 : decode_any W_613f4 = Some (Branch BC_GEU 10 15 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613f8 : bv 32 := 0xfffc0517.
Lemma F_613f8 : fetch_word AsanUbsan.M.loaded_segments (0x613f8 : word) = Some W_613f8.
Proof. vm_refl. Qed.
Lemma D_613f8 : decode_any W_613f8 = Some (Auipc 10 1048512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613fc : bv 32 := 0xfffb7597.
Lemma F_613fc : fetch_word AsanUbsan.M.loaded_segments (0x613fc : word) = Some W_613fc.
Proof. vm_refl. Qed.
Lemma D_613fc : decode_any W_613fc = Some (Auipc 11 1048503, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61400 : bv 32 := 0x8b850513.
Lemma F_61400 : fetch_word AsanUbsan.M.loaded_segments (0x61400 : word) = Some W_61400.
Proof. vm_refl. Qed.
Lemma D_61400 : decode_any W_61400 = Some (OpImm ALU_ADD 10 10 2232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61404 : bv 32 := 0x11158613.
Lemma F_61404 : fetch_word AsanUbsan.M.loaded_segments (0x61404 : word) = Some W_61404.
Proof. vm_refl. Qed.
Lemma D_61404 : decode_any W_61404 = Some (OpImm ALU_ADD 12 11 273, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61408 : bv 32 := 0x02f00593.
Lemma F_61408 : fetch_word AsanUbsan.M.loaded_segments (0x61408 : word) = Some W_61408.
Proof. vm_refl. Qed.
Lemma D_61408 : decode_any W_61408 = Some (OpImm ALU_ADD 11 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6140c : bv 32 := 0x00000693.
Lemma F_6140c : fetch_word AsanUbsan.M.loaded_segments (0x6140c : word) = Some W_6140c.
Proof. vm_refl. Qed.
Lemma D_6140c : decode_any W_6140c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61410 : bv 32 := 0x00000713.
Lemma F_61410 : fetch_word AsanUbsan.M.loaded_segments (0x61410 : word) = Some W_61410.
Proof. vm_refl. Qed.
Lemma D_61410 : decode_any W_61410 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61414 : bv 32 := 0x6d5170ef.
Lemma F_61414 : fetch_word AsanUbsan.M.loaded_segments (0x61414 : word) = Some W_61414.
Proof. vm_refl. Qed.
Lemma D_61414 : decode_any W_61414 = Some (Jal 1 98004, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61418 : bv 32 := 0x00128293.
Lemma F_61418 : fetch_word AsanUbsan.M.loaded_segments (0x61418 : word) = Some W_61418.
Proof. vm_refl. Qed.
Lemma D_61418 : decode_any W_61418 = Some (OpImm ALU_ADD 5 5 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6141c : bv 32 := 0x0032d793.
Lemma F_6141c : fetch_word AsanUbsan.M.loaded_segments (0x6141c : word) = Some W_6141c.
Proof. vm_refl. Qed.
Lemma D_6141c : decode_any W_6141c = Some (ShiftImm ALU_SRL 15 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61420 : bv 32 := 0xfff78793.
Lemma F_61420 : fetch_word AsanUbsan.M.loaded_segments (0x61420 : word) = Some W_61420.
Proof. vm_refl. Qed.
Lemma D_61420 : decode_any W_61420 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61424 : bv 32 := 0xfca7eae3.
Lemma F_61424 : fetch_word AsanUbsan.M.loaded_segments (0x61424 : word) = Some W_61424.
Proof. vm_refl. Qed.
Lemma D_61424 : decode_any W_61424 = Some (Branch BC_LTU 15 10 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61428 : bv 32 := 0x0075f793.
Lemma F_61428 : fetch_word AsanUbsan.M.loaded_segments (0x61428 : word) = Some W_61428.
Proof. vm_refl. Qed.
Lemma D_61428 : decode_any W_61428 = Some (OpImm ALU_AND 15 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6142c : bv 32 := 0x26079a63.
Lemma F_6142c : fetch_word AsanUbsan.M.loaded_segments (0x6142c : word) = Some W_6142c.
Proof. vm_refl. Qed.
Lemma D_6142c : decode_any W_6142c = Some (Branch BC_NE 15 0 628, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61430 : bv 32 := 0x00b505b3.
Lemma F_61430 : fetch_word AsanUbsan.M.loaded_segments (0x61430 : word) = Some W_61430.
Proof. vm_refl. Qed.
Lemma D_61430 : decode_any W_61430 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61434 : bv 32 := 0xff858593.
Lemma F_61434 : fetch_word AsanUbsan.M.loaded_segments (0x61434 : word) = Some W_61434.
Proof. vm_refl. Qed.
Lemma D_61434 : decode_any W_61434 = Some (OpImm ALU_ADD 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61438 : bv 32 := 0x04b77263.
Lemma F_61438 : fetch_word AsanUbsan.M.loaded_segments (0x61438 : word) = Some W_61438.
Proof. vm_refl. Qed.
Lemma D_61438 : decode_any W_61438 = Some (Branch BC_GEU 14 11 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6143c : bv 32 := 0x00075717.
Lemma F_6143c : fetch_word AsanUbsan.M.loaded_segments (0x6143c : word) = Some W_6143c.
Proof. vm_refl. Qed.
Lemma D_6143c : decode_any W_6143c = Some (Auipc 14 117, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61440 : bv 32 := 0x09473703.
Lemma F_61440 : fetch_word AsanUbsan.M.loaded_segments (0x61440 : word) = Some W_61440.
Proof. vm_refl. Qed.
Lemma D_61440 : decode_any W_61440 = Some (Load SZ8 true 14 14 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61444 : bv 32 := 0x00075797.
Lemma F_61444 : fetch_word AsanUbsan.M.loaded_segments (0x61444 : word) = Some W_61444.
Proof. vm_refl. Qed.
Lemma D_61444 : decode_any W_61444 = Some (Auipc 15 117, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61448 : bv 32 := 0x0947b783.
Lemma F_61448 : fetch_word AsanUbsan.M.loaded_segments (0x61448 : word) = Some W_61448.
Proof. vm_refl. Qed.
Lemma D_61448 : decode_any W_61448 = Some (Load SZ8 true 15 15 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6144c : bv 32 := 0x00073883.
Lemma F_6144c : fetch_word AsanUbsan.M.loaded_segments (0x6144c : word) = Some W_6144c.
Proof. vm_refl. Qed.
Lemma D_6144c : decode_any W_6144c = Some (Load SZ8 true 17 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61450 : bv 32 := 0x0007b703.
Lemma F_61450 : fetch_word AsanUbsan.M.loaded_segments (0x61450 : word) = Some W_61450.
Proof. vm_refl. Qed.
Lemma D_61450 : decode_any W_61450 = Some (Load SZ8 true 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61454 : bv 32 := 0xfff88813.
Lemma F_61454 : fetch_word AsanUbsan.M.loaded_segments (0x61454 : word) = Some W_61454.
Proof. vm_refl. Qed.
Lemma D_61454 : decode_any W_61454 = Some (OpImm ALU_ADD 16 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61458 : bv 32 := 0x00b87463.
Lemma F_61458 : fetch_word AsanUbsan.M.loaded_segments (0x61458 : word) = Some W_61458.
Proof. vm_refl. Qed.
Lemma D_61458 : decode_any W_61458 = Some (Branch BC_GEU 16 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6145c : bv 32 := 0x02b77063.
Lemma F_6145c : fetch_word AsanUbsan.M.loaded_segments (0x6145c : word) = Some W_6145c.
Proof. vm_refl. Qed.
Lemma D_6145c : decode_any W_6145c = Some (Branch BC_GEU 14 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61460 : bv 32 := 0x00075797.
Lemma F_61460 : fetch_word AsanUbsan.M.loaded_segments (0x61460 : word) = Some W_61460.
Proof. vm_refl. Qed.
Lemma D_61460 : decode_any W_61460 = Some (Auipc 15 117, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61464 : bv 32 := 0x0807b783.
Lemma F_61464 : fetch_word AsanUbsan.M.loaded_segments (0x61464 : word) = Some W_61464.
Proof. vm_refl. Qed.
Lemma D_61464 : decode_any W_61464 = Some (Load SZ8 true 15 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61468 : bv 32 := 0x0007b303.
Lemma F_61468 : fetch_word AsanUbsan.M.loaded_segments (0x61468 : word) = Some W_61468.
Proof. vm_refl. Qed.
Lemma D_61468 : decode_any W_61468 = Some (Load SZ8 true 6 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6146c : bv 32 := 0x00335793.
Lemma F_6146c : fetch_word AsanUbsan.M.loaded_segments (0x6146c : word) = Some W_6146c.
Proof. vm_refl. Qed.
Lemma D_6146c : decode_any W_6146c = Some (ShiftImm ALU_SRL 15 6 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61470 : bv 32 := 0x009782b3.
Lemma F_61470 : fetch_word AsanUbsan.M.loaded_segments (0x61470 : word) = Some W_61470.
Proof. vm_refl. Qed.
Lemma D_61470 : decode_any W_61470 = Some (Op ALU_ADD 5 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61474 : bv 32 := 0x12b36263.
Lemma F_61474 : fetch_word AsanUbsan.M.loaded_segments (0x61474 : word) = Some W_61474.
Proof. vm_refl. Qed.
Lemma D_61474 : decode_any W_61474 = Some (Branch BC_LTU 6 11 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61478 : bv 32 := 0x12b2f063.
Lemma F_61478 : fetch_word AsanUbsan.M.loaded_segments (0x61478 : word) = Some W_61478.
Proof. vm_refl. Qed.
Lemma D_61478 : decode_any W_61478 = Some (Branch BC_GEU 5 11 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6147c : bv 32 := 0x00075697.
Lemma F_6147c : fetch_word AsanUbsan.M.loaded_segments (0x6147c : word) = Some W_6147c.
Proof. vm_refl. Qed.
Lemma D_6147c : decode_any W_6147c = Some (Auipc 13 117, 4%Z).
Proof. vm_refl. Qed.
