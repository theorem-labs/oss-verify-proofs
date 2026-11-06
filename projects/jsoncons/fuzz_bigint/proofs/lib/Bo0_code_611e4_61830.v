(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_611e4 : bv 32 := 0x0007d517.
Lemma F_611e4 : fetch_word AsanUbsan.M.loaded_segments (0x611e4 : word) = Some W_611e4.
Proof. vm_refl. Qed.
Lemma D_611e4 : decode_any W_611e4 = Some (Auipc 10 125, 4%Z).
Proof. vm_refl. Qed.

Definition W_611e8 : bv 32 := 0xdb850503.
Lemma F_611e8 : fetch_word AsanUbsan.M.loaded_segments (0x611e8 : word) = Some W_611e8.
Proof. vm_refl. Qed.
Lemma D_611e8 : decode_any W_611e8 = Some (Load SZ1 true 10 10 3512, 4%Z).
Proof. vm_refl. Qed.

Definition W_611ec : bv 32 := 0x0230000f.
Lemma F_611ec : fetch_word AsanUbsan.M.loaded_segments (0x611ec : word) = Some W_611ec.
Proof. vm_refl. Qed.
Lemma D_611ec : decode_any W_611ec = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_611f0 : bv 32 := 0x00a03533.
Lemma F_611f0 : fetch_word AsanUbsan.M.loaded_segments (0x611f0 : word) = Some W_611f0.
Proof. vm_refl. Qed.
Lemma D_611f0 : decode_any W_611f0 = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_611f4 : bv 32 := 0x00008067.
Lemma F_611f4 : fetch_word AsanUbsan.M.loaded_segments (0x611f4 : word) = Some W_611f4.
Proof. vm_refl. Qed.
Lemma D_611f4 : decode_any W_611f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_611f8 : bv 32 := 0xfc010113.
Lemma F_611f8 : fetch_word AsanUbsan.M.loaded_segments (0x611f8 : word) = Some W_611f8.
Proof. vm_refl. Qed.
Lemma D_611f8 : decode_any W_611f8 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_611fc : bv 32 := 0x02113c23.
Lemma F_611fc : fetch_word AsanUbsan.M.loaded_segments (0x611fc : word) = Some W_611fc.
Proof. vm_refl. Qed.
Lemma D_611fc : decode_any W_611fc = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_61200 : bv 32 := 0x02813823.
Lemma F_61200 : fetch_word AsanUbsan.M.loaded_segments (0x61200 : word) = Some W_61200.
Proof. vm_refl. Qed.
Lemma D_61200 : decode_any W_61200 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_61204 : bv 32 := 0x02913423.
Lemma F_61204 : fetch_word AsanUbsan.M.loaded_segments (0x61204 : word) = Some W_61204.
Proof. vm_refl. Qed.
Lemma D_61204 : decode_any W_61204 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_61208 : bv 32 := 0x03213023.
Lemma F_61208 : fetch_word AsanUbsan.M.loaded_segments (0x61208 : word) = Some W_61208.
Proof. vm_refl. Qed.
Lemma D_61208 : decode_any W_61208 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6120c : bv 32 := 0x01313c23.
Lemma F_6120c : fetch_word AsanUbsan.M.loaded_segments (0x6120c : word) = Some W_6120c.
Proof. vm_refl. Qed.
Lemma D_6120c : decode_any W_6120c = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_61210 : bv 32 := 0x01413823.
Lemma F_61210 : fetch_word AsanUbsan.M.loaded_segments (0x61210 : word) = Some W_61210.
Proof. vm_refl. Qed.
Lemma D_61210 : decode_any W_61210 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_61214 : bv 32 := 0x01513423.
Lemma F_61214 : fetch_word AsanUbsan.M.loaded_segments (0x61214 : word) = Some W_61214.
Proof. vm_refl. Qed.
Lemma D_61214 : decode_any W_61214 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_61218 : bv 32 := 0x00060a63.
Lemma F_61218 : fetch_word AsanUbsan.M.loaded_segments (0x61218 : word) = Some W_61218.
Proof. vm_refl. Qed.
Lemma D_61218 : decode_any W_61218 = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6121c : bv 32 := 0x0007d697.
Lemma F_6121c : fetch_word AsanUbsan.M.loaded_segments (0x6121c : word) = Some W_6121c.
Proof. vm_refl. Qed.
Lemma D_6121c : decode_any W_6121c = Some (Auipc 13 125, 4%Z).
Proof. vm_refl. Qed.

Definition W_61220 : bv 32 := 0xd8068683.
Lemma F_61220 : fetch_word AsanUbsan.M.loaded_segments (0x61220 : word) = Some W_61220.
Proof. vm_refl. Qed.
Lemma D_61220 : decode_any W_61220 = Some (Load SZ1 true 13 13 3456, 4%Z).
Proof. vm_refl. Qed.

Definition W_61224 : bv 32 := 0x0230000f.
Lemma F_61224 : fetch_word AsanUbsan.M.loaded_segments (0x61224 : word) = Some W_61224.
Proof. vm_refl. Qed.
Lemma D_61224 : decode_any W_61224 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61228 : bv 32 := 0x0a068a63.
Lemma F_61228 : fetch_word AsanUbsan.M.loaded_segments (0x61228 : word) = Some W_61228.
Proof. vm_refl. Qed.
Lemma D_61228 : decode_any W_61228 = Some (Branch BC_EQ 13 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_6122c : bv 32 := 0x00757693.
Lemma F_6122c : fetch_word AsanUbsan.M.loaded_segments (0x6122c : word) = Some W_6122c.
Proof. vm_refl. Qed.
Lemma D_6122c : decode_any W_6122c = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_61230 : bv 32 := 0x42069863.
Lemma F_61230 : fetch_word AsanUbsan.M.loaded_segments (0x61230 : word) = Some W_61230.
Proof. vm_refl. Qed.
Lemma D_61230 : decode_any W_61230 = Some (Branch BC_NE 13 0 1072, 4%Z).
Proof. vm_refl. Qed.

Definition W_61234 : bv 32 := 0x00075697.
Lemma F_61234 : fetch_word AsanUbsan.M.loaded_segments (0x61234 : word) = Some W_61234.
Proof. vm_refl. Qed.
Lemma D_61234 : decode_any W_61234 = Some (Auipc 13 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_61238 : bv 32 := 0x2946b683.
Lemma F_61238 : fetch_word AsanUbsan.M.loaded_segments (0x61238 : word) = Some W_61238.
Proof. vm_refl. Qed.
Lemma D_61238 : decode_any W_61238 = Some (Load SZ8 true 13 13 660, 4%Z).
Proof. vm_refl. Qed.

Definition W_6123c : bv 32 := 0x0006b483.
Lemma F_6123c : fetch_word AsanUbsan.M.loaded_segments (0x6123c : word) = Some W_6123c.
Proof. vm_refl. Qed.
Lemma D_6123c : decode_any W_6123c = Some (Load SZ8 true 9 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61240 : bv 32 := 0xfff48693.
Lemma F_61240 : fetch_word AsanUbsan.M.loaded_segments (0x61240 : word) = Some W_61240.
Proof. vm_refl. Qed.
Lemma D_61240 : decode_any W_61240 = Some (OpImm ALU_ADD 13 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_61244 : bv 32 := 0x00d4b733.
Lemma F_61244 : fetch_word AsanUbsan.M.loaded_segments (0x61244 : word) = Some W_61244.
Proof. vm_refl. Qed.
Lemma D_61244 : decode_any W_61244 = Some (Op ALU_SLTU 14 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_61248 : bv 32 := 0xfff70713.
Lemma F_61248 : fetch_word AsanUbsan.M.loaded_segments (0x61248 : word) = Some W_61248.
Proof. vm_refl. Qed.
Lemma D_61248 : decode_any W_61248 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6124c : bv 32 := 0x00d77733.
Lemma F_6124c : fetch_word AsanUbsan.M.loaded_segments (0x6124c : word) = Some W_6124c.
Proof. vm_refl. Qed.
Lemma D_6124c : decode_any W_6124c = Some (Op ALU_AND 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_61250 : bv 32 := 0x1ca77c63.
Lemma F_61250 : fetch_word AsanUbsan.M.loaded_segments (0x61250 : word) = Some W_61250.
Proof. vm_refl. Qed.
Lemma D_61250 : decode_any W_61250 = Some (Branch BC_GEU 14 10 472, 4%Z).
Proof. vm_refl. Qed.

Definition W_61254 : bv 32 := 0x00075797.
Lemma F_61254 : fetch_word AsanUbsan.M.loaded_segments (0x61254 : word) = Some W_61254.
Proof. vm_refl. Qed.
Lemma D_61254 : decode_any W_61254 = Some (Auipc 15 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_61258 : bv 32 := 0x27c7b783.
Lemma F_61258 : fetch_word AsanUbsan.M.loaded_segments (0x61258 : word) = Some W_61258.
Proof. vm_refl. Qed.
Lemma D_61258 : decode_any W_61258 = Some (Load SZ8 true 15 15 636, 4%Z).
Proof. vm_refl. Qed.

Definition W_6125c : bv 32 := 0x00075817.
Lemma F_6125c : fetch_word AsanUbsan.M.loaded_segments (0x6125c : word) = Some W_6125c.
Proof. vm_refl. Qed.
Lemma D_6125c : decode_any W_6125c = Some (Auipc 16 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_61260 : bv 32 := 0x27c83803.
Lemma F_61260 : fetch_word AsanUbsan.M.loaded_segments (0x61260 : word) = Some W_61260.
Proof. vm_refl. Qed.
Lemma D_61260 : decode_any W_61260 = Some (Load SZ8 true 16 16 636, 4%Z).
Proof. vm_refl. Qed.

Definition W_61264 : bv 32 := 0x0007b883.
Lemma F_61264 : fetch_word AsanUbsan.M.loaded_segments (0x61264 : word) = Some W_61264.
Proof. vm_refl. Qed.
Lemma D_61264 : decode_any W_61264 = Some (Load SZ8 true 17 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61268 : bv 32 := 0x00083783.
Lemma F_61268 : fetch_word AsanUbsan.M.loaded_segments (0x61268 : word) = Some W_61268.
Proof. vm_refl. Qed.
Lemma D_61268 : decode_any W_61268 = Some (Load SZ8 true 15 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6126c : bv 32 := 0xfff88813.
Lemma F_6126c : fetch_word AsanUbsan.M.loaded_segments (0x6126c : word) = Some W_6126c.
Proof. vm_refl. Qed.
Lemma D_6126c : decode_any W_6126c = Some (OpImm ALU_ADD 16 17 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_61270 : bv 32 := 0x00a87463.
Lemma F_61270 : fetch_word AsanUbsan.M.loaded_segments (0x61270 : word) = Some W_61270.
Proof. vm_refl. Qed.
Lemma D_61270 : decode_any W_61270 = Some (Branch BC_GEU 16 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_61274 : bv 32 := 0x1aa7fa63.
Lemma F_61274 : fetch_word AsanUbsan.M.loaded_segments (0x61274 : word) = Some W_61274.
Proof. vm_refl. Qed.
Lemma D_61274 : decode_any W_61274 = Some (Branch BC_GEU 15 10 436, 4%Z).
Proof. vm_refl. Qed.

Definition W_61278 : bv 32 := 0x00075297.
Lemma F_61278 : fetch_word AsanUbsan.M.loaded_segments (0x61278 : word) = Some W_61278.
Proof. vm_refl. Qed.
Lemma D_61278 : decode_any W_61278 = Some (Auipc 5 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_6127c : bv 32 := 0x2682b283.
Lemma F_6127c : fetch_word AsanUbsan.M.loaded_segments (0x6127c : word) = Some W_6127c.
Proof. vm_refl. Qed.
Lemma D_6127c : decode_any W_6127c = Some (Load SZ8 true 5 5 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_61280 : bv 32 := 0x0002be03.
Lemma F_61280 : fetch_word AsanUbsan.M.loaded_segments (0x61280 : word) = Some W_61280.
Proof. vm_refl. Qed.
Lemma D_61280 : decode_any W_61280 = Some (Load SZ8 true 28 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61284 : bv 32 := 0x003e5313.
Lemma F_61284 : fetch_word AsanUbsan.M.loaded_segments (0x61284 : word) = Some W_61284.
Proof. vm_refl. Qed.
Lemma D_61284 : decode_any W_61284 = Some (ShiftImm ALU_SRL 6 28 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61288 : bv 32 := 0x009303b3.
Lemma F_61288 : fetch_word AsanUbsan.M.loaded_segments (0x61288 : word) = Some W_61288.
Proof. vm_refl. Qed.
Lemma D_61288 : decode_any W_61288 = Some (Op ALU_ADD 7 6 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_6128c : bv 32 := 0x00ae6463.
Lemma F_6128c : fetch_word AsanUbsan.M.loaded_segments (0x6128c : word) = Some W_6128c.
Proof. vm_refl. Qed.
Lemma D_6128c : decode_any W_6128c = Some (Branch BC_LTU 28 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_61290 : bv 32 := 0x0ca3e463.
Lemma F_61290 : fetch_word AsanUbsan.M.loaded_segments (0x61290 : word) = Some W_61290.
Proof. vm_refl. Qed.
Lemma D_61290 : decode_any W_61290 = Some (Branch BC_LTU 7 10 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_61294 : bv 32 := 0x00075e17.
Lemma F_61294 : fetch_word AsanUbsan.M.loaded_segments (0x61294 : word) = Some W_61294.
Proof. vm_refl. Qed.
Lemma D_61294 : decode_any W_61294 = Some (Auipc 28 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_61298 : bv 32 := 0x22ce3e03.
Lemma F_61298 : fetch_word AsanUbsan.M.loaded_segments (0x61298 : word) = Some W_61298.
Proof. vm_refl. Qed.
Lemma D_61298 : decode_any W_61298 = Some (Load SZ8 true 28 28 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_6129c : bv 32 := 0x04ee4e03.
Lemma F_6129c : fetch_word AsanUbsan.M.loaded_segments (0x6129c : word) = Some W_6129c.
Proof. vm_refl. Qed.
Lemma D_6129c : decode_any W_6129c = Some (Load SZ1 false 28 28 78, 4%Z).
Proof. vm_refl. Qed.

Definition W_612a0 : bv 32 := 0x3e0e1063.
Lemma F_612a0 : fetch_word AsanUbsan.M.loaded_segments (0x612a0 : word) = Some W_612a0.
Proof. vm_refl. Qed.
Lemma D_612a0 : decode_any W_612a0 = Some (Branch BC_NE 28 0 992, 4%Z).
Proof. vm_refl. Qed.

Definition W_612a4 : bv 32 := 0x04088e63.
Lemma F_612a4 : fetch_word AsanUbsan.M.loaded_segments (0x612a4 : word) = Some W_612a4.
Proof. vm_refl. Qed.
Lemma D_612a4 : decode_any W_612a4 = Some (Branch BC_EQ 17 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_612a8 : bv 32 := 0x0038d393.
Lemma F_612a8 : fetch_word AsanUbsan.M.loaded_segments (0x612a8 : word) = Some W_612a8.
Proof. vm_refl. Qed.
Lemma D_612a8 : decode_any W_612a8 = Some (ShiftImm ALU_SRL 7 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_612ac : bv 32 := 0x00d383b3.
Lemma F_612ac : fetch_word AsanUbsan.M.loaded_segments (0x612ac : word) = Some W_612ac.
Proof. vm_refl. Qed.
Lemma D_612ac : decode_any W_612ac = Some (Op ALU_ADD 7 7 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_612b0 : bv 32 := 0x06a3fe63.
Lemma F_612b0 : fetch_word AsanUbsan.M.loaded_segments (0x612b0 : word) = Some W_612b0.
Proof. vm_refl. Qed.
Lemma D_612b0 : decode_any W_612b0 = Some (Branch BC_GEU 7 10 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_612b4 : bv 32 := 0x00148393.
Lemma F_612b4 : fetch_word AsanUbsan.M.loaded_segments (0x612b4 : word) = Some W_612b4.
Proof. vm_refl. Qed.
Lemma D_612b4 : decode_any W_612b4 = Some (OpImm ALU_ADD 7 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_612b8 : bv 32 := 0x00a86863.
Lemma F_612b8 : fetch_word AsanUbsan.M.loaded_segments (0x612b8 : word) = Some W_612b8.
Proof. vm_refl. Qed.
Lemma D_612b8 : decode_any W_612b8 = Some (Branch BC_LTU 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_612bc : bv 32 := 0x0037de13.
Lemma F_612bc : fetch_word AsanUbsan.M.loaded_segments (0x612bc : word) = Some W_612bc.
Proof. vm_refl. Qed.
Lemma D_612bc : decode_any W_612bc = Some (ShiftImm ALU_SRL 28 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_612c0 : bv 32 := 0x007e0e33.
Lemma F_612c0 : fetch_word AsanUbsan.M.loaded_segments (0x612c0 : word) = Some W_612c0.
Proof. vm_refl. Qed.
Lemma D_612c0 : decode_any W_612c0 = Some (Op ALU_ADD 28 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_612c4 : bv 32 := 0x09c57a63.
Lemma F_612c4 : fetch_word AsanUbsan.M.loaded_segments (0x612c4 : word) = Some W_612c4.
Proof. vm_refl. Qed.
Lemma D_612c4 : decode_any W_612c4 = Some (Branch BC_GEU 10 28 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_612c8 : bv 32 := 0x00178e13.
Lemma F_612c8 : fetch_word AsanUbsan.M.loaded_segments (0x612c8 : word) = Some W_612c8.
Proof. vm_refl. Qed.
Lemma D_612c8 : decode_any W_612c8 = Some (OpImm ALU_ADD 28 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_612cc : bv 32 := 0x3bc56a63.
Lemma F_612cc : fetch_word AsanUbsan.M.loaded_segments (0x612cc : word) = Some W_612cc.
Proof. vm_refl. Qed.
Lemma D_612cc : decode_any W_612cc = Some (Branch BC_LTU 10 28 948, 4%Z).
Proof. vm_refl. Qed.

Definition W_612d0 : bv 32 := 0x00730333.
Lemma F_612d0 : fetch_word AsanUbsan.M.loaded_segments (0x612d0 : word) = Some W_612d0.
Proof. vm_refl. Qed.
Lemma D_612d0 : decode_any W_612d0 = Some (Op ALU_ADD 6 6 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_612d4 : bv 32 := 0x00335313.
Lemma F_612d4 : fetch_word AsanUbsan.M.loaded_segments (0x612d4 : word) = Some W_612d4.
Proof. vm_refl. Qed.
Lemma D_612d4 : decode_any W_612d4 = Some (ShiftImm ALU_SRL 6 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_612d8 : bv 32 := 0x0480006f.
Lemma F_612d8 : fetch_word AsanUbsan.M.loaded_segments (0x612d8 : word) = Some W_612d8.
Proof. vm_refl. Qed.
Lemma D_612d8 : decode_any W_612d8 = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_612dc : bv 32 := 0x03813083.
Lemma F_612dc : fetch_word AsanUbsan.M.loaded_segments (0x612dc : word) = Some W_612dc.
Proof. vm_refl. Qed.
Lemma D_612dc : decode_any W_612dc = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_612e0 : bv 32 := 0x03013403.
Lemma F_612e0 : fetch_word AsanUbsan.M.loaded_segments (0x612e0 : word) = Some W_612e0.
Proof. vm_refl. Qed.
Lemma D_612e0 : decode_any W_612e0 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_612e4 : bv 32 := 0x02813483.
Lemma F_612e4 : fetch_word AsanUbsan.M.loaded_segments (0x612e4 : word) = Some W_612e4.
Proof. vm_refl. Qed.
Lemma D_612e4 : decode_any W_612e4 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_612e8 : bv 32 := 0x02013903.
Lemma F_612e8 : fetch_word AsanUbsan.M.loaded_segments (0x612e8 : word) = Some W_612e8.
Proof. vm_refl. Qed.
Lemma D_612e8 : decode_any W_612e8 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_612ec : bv 32 := 0x01813983.
Lemma F_612ec : fetch_word AsanUbsan.M.loaded_segments (0x612ec : word) = Some W_612ec.
Proof. vm_refl. Qed.
Lemma D_612ec : decode_any W_612ec = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_612f0 : bv 32 := 0x01013a03.
Lemma F_612f0 : fetch_word AsanUbsan.M.loaded_segments (0x612f0 : word) = Some W_612f0.
Proof. vm_refl. Qed.
Lemma D_612f0 : decode_any W_612f0 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_612f4 : bv 32 := 0x00813a83.
Lemma F_612f4 : fetch_word AsanUbsan.M.loaded_segments (0x612f4 : word) = Some W_612f4.
Proof. vm_refl. Qed.
Lemma D_612f4 : decode_any W_612f4 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_612f8 : bv 32 := 0x04010113.
Lemma F_612f8 : fetch_word AsanUbsan.M.loaded_segments (0x612f8 : word) = Some W_612f8.
Proof. vm_refl. Qed.
Lemma D_612f8 : decode_any W_612f8 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_612fc : bv 32 := 0x00008067.
Lemma F_612fc : fetch_word AsanUbsan.M.loaded_segments (0x612fc : word) = Some W_612fc.
Proof. vm_refl. Qed.
Lemma D_612fc : decode_any W_612fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61300 : bv 32 := 0x04048463.
Lemma F_61300 : fetch_word AsanUbsan.M.loaded_segments (0x61300 : word) = Some W_61300.
Proof. vm_refl. Qed.
Lemma D_61300 : decode_any W_61300 = Some (Branch BC_EQ 9 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_61304 : bv 32 := 0x0036d313.
Lemma F_61304 : fetch_word AsanUbsan.M.loaded_segments (0x61304 : word) = Some W_61304.
Proof. vm_refl. Qed.
Lemma D_61304 : decode_any W_61304 = Some (ShiftImm ALU_SRL 6 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61308 : bv 32 := 0x00930333.
Lemma F_61308 : fetch_word AsanUbsan.M.loaded_segments (0x61308 : word) = Some W_61308.
Proof. vm_refl. Qed.
Lemma D_61308 : decode_any W_61308 = Some (Op ALU_ADD 6 6 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_6130c : bv 32 := 0x00030663.
Lemma F_6130c : fetch_word AsanUbsan.M.loaded_segments (0x6130c : word) = Some W_6130c.
Proof. vm_refl. Qed.
Lemma D_6130c : decode_any W_6130c = Some (Branch BC_EQ 6 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_61310 : bv 32 := 0x00130313.
Lemma F_61310 : fetch_word AsanUbsan.M.loaded_segments (0x61310 : word) = Some W_61310.
Proof. vm_refl. Qed.
Lemma D_61310 : decode_any W_61310 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61314 : bv 32 := 0x36656663.
Lemma F_61314 : fetch_word AsanUbsan.M.loaded_segments (0x61314 : word) = Some W_61314.
Proof. vm_refl. Qed.
Lemma D_61314 : decode_any W_61314 = Some (Branch BC_LTU 10 6 876, 4%Z).
Proof. vm_refl. Qed.

Definition W_61318 : bv 32 := 0x00138393.
Lemma F_61318 : fetch_word AsanUbsan.M.loaded_segments (0x61318 : word) = Some W_61318.
Proof. vm_refl. Qed.
Lemma D_61318 : decode_any W_61318 = Some (OpImm ALU_ADD 7 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6131c : bv 32 := 0x0033d313.
Lemma F_6131c : fetch_word AsanUbsan.M.loaded_segments (0x6131c : word) = Some W_6131c.
Proof. vm_refl. Qed.
Lemma D_6131c : decode_any W_6131c = Some (ShiftImm ALU_SRL 6 7 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61320 : bv 32 := 0x00d30333.
Lemma F_61320 : fetch_word AsanUbsan.M.loaded_segments (0x61320 : word) = Some W_61320.
Proof. vm_refl. Qed.
Lemma D_61320 : decode_any W_61320 = Some (Op ALU_ADD 6 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_61324 : bv 32 := 0x02a37a63.
Lemma F_61324 : fetch_word AsanUbsan.M.loaded_segments (0x61324 : word) = Some W_61324.
Proof. vm_refl. Qed.
Lemma D_61324 : decode_any W_61324 = Some (Branch BC_GEU 6 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_61328 : bv 32 := 0x3580006f.
Lemma F_61328 : fetch_word AsanUbsan.M.loaded_segments (0x61328 : word) = Some W_61328.
Proof. vm_refl. Qed.
Lemma D_61328 : decode_any W_61328 = Some (Jal 0 856, 4%Z).
Proof. vm_refl. Qed.

Definition W_6132c : bv 32 := 0x02048663.
Lemma F_6132c : fetch_word AsanUbsan.M.loaded_segments (0x6132c : word) = Some W_6132c.
Proof. vm_refl. Qed.
Lemma D_6132c : decode_any W_6132c = Some (Branch BC_EQ 9 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_61330 : bv 32 := 0x0036d313.
Lemma F_61330 : fetch_word AsanUbsan.M.loaded_segments (0x61330 : word) = Some W_61330.
Proof. vm_refl. Qed.
Lemma D_61330 : decode_any W_61330 = Some (ShiftImm ALU_SRL 6 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61334 : bv 32 := 0x00930333.
Lemma F_61334 : fetch_word AsanUbsan.M.loaded_segments (0x61334 : word) = Some W_61334.
Proof. vm_refl. Qed.
Lemma D_61334 : decode_any W_61334 = Some (Op ALU_ADD 6 6 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_61338 : bv 32 := 0x02030063.
Lemma F_61338 : fetch_word AsanUbsan.M.loaded_segments (0x61338 : word) = Some W_61338.
Proof. vm_refl. Qed.
Lemma D_61338 : decode_any W_61338 = Some (Branch BC_EQ 6 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6133c : bv 32 := 0x00130313.
Lemma F_6133c : fetch_word AsanUbsan.M.loaded_segments (0x6133c : word) = Some W_6133c.
Proof. vm_refl. Qed.
Lemma D_6133c : decode_any W_6133c = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61340 : bv 32 := 0x00657c63.
Lemma F_61340 : fetch_word AsanUbsan.M.loaded_segments (0x61340 : word) = Some W_61340.
Proof. vm_refl. Qed.
Lemma D_61340 : decode_any W_61340 = Some (Branch BC_GEU 10 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_61344 : bv 32 := 0x33c0006f.
Lemma F_61344 : fetch_word AsanUbsan.M.loaded_segments (0x61344 : word) = Some W_61344.
Proof. vm_refl. Qed.
Lemma D_61344 : decode_any W_61344 = Some (Jal 0 828, 4%Z).
Proof. vm_refl. Qed.

Definition W_61348 : bv 32 := 0x00130313.
Lemma F_61348 : fetch_word AsanUbsan.M.loaded_segments (0x61348 : word) = Some W_61348.
Proof. vm_refl. Qed.
Lemma D_61348 : decode_any W_61348 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6134c : bv 32 := 0x00335313.
Lemma F_6134c : fetch_word AsanUbsan.M.loaded_segments (0x6134c : word) = Some W_6134c.
Proof. vm_refl. Qed.
Lemma D_6134c : decode_any W_6134c = Some (ShiftImm ALU_SRL 6 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61350 : bv 32 := 0xfff30313.
Lemma F_61350 : fetch_word AsanUbsan.M.loaded_segments (0x61350 : word) = Some W_61350.
Proof. vm_refl. Qed.
Lemma D_61350 : decode_any W_61350 = Some (OpImm ALU_ADD 6 6 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_61354 : bv 32 := 0x32a36663.
Lemma F_61354 : fetch_word AsanUbsan.M.loaded_segments (0x61354 : word) = Some W_61354.
Proof. vm_refl. Qed.
Lemma D_61354 : decode_any W_61354 = Some (Branch BC_LTU 6 10 812, 4%Z).
Proof. vm_refl. Qed.

Definition W_61358 : bv 32 := 0x0002b383.
Lemma F_61358 : fetch_word AsanUbsan.M.loaded_segments (0x61358 : word) = Some W_61358.
Proof. vm_refl. Qed.
Lemma D_61358 : decode_any W_61358 = Some (Load SZ8 true 7 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6135c : bv 32 := 0x0033d293.
Lemma F_6135c : fetch_word AsanUbsan.M.loaded_segments (0x6135c : word) = Some W_6135c.
Proof. vm_refl. Qed.
Lemma D_6135c : decode_any W_6135c = Some (ShiftImm ALU_SRL 5 7 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61360 : bv 32 := 0x00928333.
Lemma F_61360 : fetch_word AsanUbsan.M.loaded_segments (0x61360 : word) = Some W_61360.
Proof. vm_refl. Qed.
Lemma D_61360 : decode_any W_61360 = Some (Op ALU_ADD 6 5 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_61364 : bv 32 := 0x00a3e463.
Lemma F_61364 : fetch_word AsanUbsan.M.loaded_segments (0x61364 : word) = Some W_61364.
Proof. vm_refl. Qed.
Lemma D_61364 : decode_any W_61364 = Some (Branch BC_LTU 7 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_61368 : bv 32 := 0x0ca36063.
Lemma F_61368 : fetch_word AsanUbsan.M.loaded_segments (0x61368 : word) = Some W_61368.
Proof. vm_refl. Qed.
Lemma D_61368 : decode_any W_61368 = Some (Branch BC_LTU 6 10 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_6136c : bv 32 := 0x00075397.
Lemma F_6136c : fetch_word AsanUbsan.M.loaded_segments (0x6136c : word) = Some W_6136c.
Proof. vm_refl. Qed.
Lemma D_6136c : decode_any W_6136c = Some (Auipc 7 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_61370 : bv 32 := 0x1543b383.
Lemma F_61370 : fetch_word AsanUbsan.M.loaded_segments (0x61370 : word) = Some W_61370.
Proof. vm_refl. Qed.
Lemma D_61370 : decode_any W_61370 = Some (Load SZ8 true 7 7 340, 4%Z).
Proof. vm_refl. Qed.

Definition W_61374 : bv 32 := 0x04e3c383.
Lemma F_61374 : fetch_word AsanUbsan.M.loaded_segments (0x61374 : word) = Some W_61374.
Proof. vm_refl. Qed.
Lemma D_61374 : decode_any W_61374 = Some (Load SZ1 false 7 7 78, 4%Z).
Proof. vm_refl. Qed.

Definition W_61378 : bv 32 := 0x08039063.
Lemma F_61378 : fetch_word AsanUbsan.M.loaded_segments (0x61378 : word) = Some W_61378.
Proof. vm_refl. Qed.
Lemma D_61378 : decode_any W_61378 = Some (Branch BC_NE 7 0 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_6137c : bv 32 := 0x02088c63.
Lemma F_6137c : fetch_word AsanUbsan.M.loaded_segments (0x6137c : word) = Some W_6137c.
Proof. vm_refl. Qed.
Lemma D_6137c : decode_any W_6137c = Some (Branch BC_EQ 17 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_61380 : bv 32 := 0x0038d893.
Lemma F_61380 : fetch_word AsanUbsan.M.loaded_segments (0x61380 : word) = Some W_61380.
Proof. vm_refl. Qed.
Lemma D_61380 : decode_any W_61380 = Some (ShiftImm ALU_SRL 17 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61384 : bv 32 := 0x00d888b3.
Lemma F_61384 : fetch_word AsanUbsan.M.loaded_segments (0x61384 : word) = Some W_61384.
Proof. vm_refl. Qed.
Lemma D_61384 : decode_any W_61384 = Some (Op ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_61388 : bv 32 := 0x04a8fc63.
Lemma F_61388 : fetch_word AsanUbsan.M.loaded_segments (0x61388 : word) = Some W_61388.
Proof. vm_refl. Qed.
Lemma D_61388 : decode_any W_61388 = Some (Branch BC_GEU 17 10 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_6138c : bv 32 := 0x00148893.
Lemma F_6138c : fetch_word AsanUbsan.M.loaded_segments (0x6138c : word) = Some W_6138c.
Proof. vm_refl. Qed.
Lemma D_6138c : decode_any W_6138c = Some (OpImm ALU_ADD 17 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61390 : bv 32 := 0x00a86863.
Lemma F_61390 : fetch_word AsanUbsan.M.loaded_segments (0x61390 : word) = Some W_61390.
Proof. vm_refl. Qed.
Lemma D_61390 : decode_any W_61390 = Some (Branch BC_LTU 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_61394 : bv 32 := 0x0037d813.
Lemma F_61394 : fetch_word AsanUbsan.M.loaded_segments (0x61394 : word) = Some W_61394.
Proof. vm_refl. Qed.
Lemma D_61394 : decode_any W_61394 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61398 : bv 32 := 0x01180833.
Lemma F_61398 : fetch_word AsanUbsan.M.loaded_segments (0x61398 : word) = Some W_61398.
Proof. vm_refl. Qed.
Lemma D_61398 : decode_any W_61398 = Some (Op ALU_ADD 16 16 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_6139c : bv 32 := 0x09057663.
Lemma F_6139c : fetch_word AsanUbsan.M.loaded_segments (0x6139c : word) = Some W_6139c.
Proof. vm_refl. Qed.
Lemma D_6139c : decode_any W_6139c = Some (Branch BC_GEU 10 16 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_613a0 : bv 32 := 0x00178793.
Lemma F_613a0 : fetch_word AsanUbsan.M.loaded_segments (0x613a0 : word) = Some W_613a0.
Proof. vm_refl. Qed.
Lemma D_613a0 : decode_any W_613a0 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_613a4 : bv 32 := 0x04f56a63.
Lemma F_613a4 : fetch_word AsanUbsan.M.loaded_segments (0x613a4 : word) = Some W_613a4.
Proof. vm_refl. Qed.
Lemma D_613a4 : decode_any W_613a4 = Some (Branch BC_LTU 10 15 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_613a8 : bv 32 := 0x011288b3.
Lemma F_613a8 : fetch_word AsanUbsan.M.loaded_segments (0x613a8 : word) = Some W_613a8.
Proof. vm_refl. Qed.
Lemma D_613a8 : decode_any W_613a8 = Some (Op ALU_ADD 17 5 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_613ac : bv 32 := 0x0038d793.
Lemma F_613ac : fetch_word AsanUbsan.M.loaded_segments (0x613ac : word) = Some W_613ac.
Proof. vm_refl. Qed.
Lemma D_613ac : decode_any W_613ac = Some (ShiftImm ALU_SRL 15 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_613b0 : bv 32 := 0x0240006f.
Lemma F_613b0 : fetch_word AsanUbsan.M.loaded_segments (0x613b0 : word) = Some W_613b0.
Proof. vm_refl. Qed.
Lemma D_613b0 : decode_any W_613b0 = Some (Jal 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_613b4 : bv 32 := 0x06048263.
Lemma F_613b4 : fetch_word AsanUbsan.M.loaded_segments (0x613b4 : word) = Some W_613b4.
Proof. vm_refl. Qed.
Lemma D_613b4 : decode_any W_613b4 = Some (Branch BC_EQ 9 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_613b8 : bv 32 := 0x0036d793.
Lemma F_613b8 : fetch_word AsanUbsan.M.loaded_segments (0x613b8 : word) = Some W_613b8.
Proof. vm_refl. Qed.
Lemma D_613b8 : decode_any W_613b8 = Some (ShiftImm ALU_SRL 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_613bc : bv 32 := 0x009787b3.
Lemma F_613bc : fetch_word AsanUbsan.M.loaded_segments (0x613bc : word) = Some W_613bc.
Proof. vm_refl. Qed.
Lemma D_613bc : decode_any W_613bc = Some (Op ALU_ADD 15 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_613c0 : bv 32 := 0x00078663.
Lemma F_613c0 : fetch_word AsanUbsan.M.loaded_segments (0x613c0 : word) = Some W_613c0.
Proof. vm_refl. Qed.
Lemma D_613c0 : decode_any W_613c0 = Some (Branch BC_EQ 15 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_613c4 : bv 32 := 0x00178793.
Lemma F_613c4 : fetch_word AsanUbsan.M.loaded_segments (0x613c4 : word) = Some W_613c4.
Proof. vm_refl. Qed.
Lemma D_613c4 : decode_any W_613c4 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_613c8 : bv 32 := 0x02f56863.
Lemma F_613c8 : fetch_word AsanUbsan.M.loaded_segments (0x613c8 : word) = Some W_613c8.
Proof. vm_refl. Qed.
Lemma D_613c8 : decode_any W_613c8 = Some (Branch BC_LTU 10 15 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_613cc : bv 32 := 0x00130313.
Lemma F_613cc : fetch_word AsanUbsan.M.loaded_segments (0x613cc : word) = Some W_613cc.
Proof. vm_refl. Qed.
Lemma D_613cc : decode_any W_613cc = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_613d0 : bv 32 := 0x00335793.
Lemma F_613d0 : fetch_word AsanUbsan.M.loaded_segments (0x613d0 : word) = Some W_613d0.
Proof. vm_refl. Qed.
Lemma D_613d0 : decode_any W_613d0 = Some (ShiftImm ALU_SRL 15 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_613d4 : bv 32 := 0x00d787b3.
Lemma F_613d4 : fetch_word AsanUbsan.M.loaded_segments (0x613d4 : word) = Some W_613d4.
Proof. vm_refl. Qed.
Lemma D_613d4 : decode_any W_613d4 = Some (Op ALU_ADD 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_613d8 : bv 32 := 0x04a7f863.
Lemma F_613d8 : fetch_word AsanUbsan.M.loaded_segments (0x613d8 : word) = Some W_613d8.
Proof. vm_refl. Qed.
Lemma D_613d8 : decode_any W_613d8 = Some (Branch BC_GEU 15 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_613dc : bv 32 := 0x01c0006f.
Lemma F_613dc : fetch_word AsanUbsan.M.loaded_segments (0x613dc : word) = Some W_613dc.
Proof. vm_refl. Qed.
Lemma D_613dc : decode_any W_613dc = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_613e0 : bv 32 := 0x04048463.
Lemma F_613e0 : fetch_word AsanUbsan.M.loaded_segments (0x613e0 : word) = Some W_613e0.
Proof. vm_refl. Qed.
Lemma D_613e0 : decode_any W_613e0 = Some (Branch BC_EQ 9 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_613e4 : bv 32 := 0x0036d793.
Lemma F_613e4 : fetch_word AsanUbsan.M.loaded_segments (0x613e4 : word) = Some W_613e4.
Proof. vm_refl. Qed.
Lemma D_613e4 : decode_any W_613e4 = Some (ShiftImm ALU_SRL 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_613e8 : bv 32 := 0x009787b3.
Lemma F_613e8 : fetch_word AsanUbsan.M.loaded_segments (0x613e8 : word) = Some W_613e8.
Proof. vm_refl. Qed.
Lemma D_613e8 : decode_any W_613e8 = Some (Op ALU_ADD 15 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_613ec : bv 32 := 0x02078e63.
Lemma F_613ec : fetch_word AsanUbsan.M.loaded_segments (0x613ec : word) = Some W_613ec.
Proof. vm_refl. Qed.
Lemma D_613ec : decode_any W_613ec = Some (Branch BC_EQ 15 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_613f0 : bv 32 := 0x00178793.
Lemma F_613f0 : fetch_word AsanUbsan.M.loaded_segments (0x613f0 : word) = Some W_613f0.
Proof. vm_refl. Qed.
Lemma D_613f0 : decode_any W_613f0 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_613f4 : bv 32 := 0x02f57a63.
Lemma F_613f4 : fetch_word AsanUbsan.M.loaded_segments (0x613f4 : word) = Some W_613f4.
Proof. vm_refl. Qed.
Lemma D_613f4 : decode_any W_613f4 = Some (Branch BC_GEU 10 15 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_613f8 : bv 32 := 0xfffc0517.
Lemma F_613f8 : fetch_word AsanUbsan.M.loaded_segments (0x613f8 : word) = Some W_613f8.
Proof. vm_refl. Qed.
Lemma D_613f8 : decode_any W_613f8 = Some (Auipc 10 1048512, 4%Z).
Proof. vm_refl. Qed.

Definition W_613fc : bv 32 := 0xfffb7597.
Lemma F_613fc : fetch_word AsanUbsan.M.loaded_segments (0x613fc : word) = Some W_613fc.
Proof. vm_refl. Qed.
Lemma D_613fc : decode_any W_613fc = Some (Auipc 11 1048503, 4%Z).
Proof. vm_refl. Qed.

Definition W_61400 : bv 32 := 0x8b850513.
Lemma F_61400 : fetch_word AsanUbsan.M.loaded_segments (0x61400 : word) = Some W_61400.
Proof. vm_refl. Qed.
Lemma D_61400 : decode_any W_61400 = Some (OpImm ALU_ADD 10 10 2232, 4%Z).
Proof. vm_refl. Qed.

Definition W_61404 : bv 32 := 0x11158613.
Lemma F_61404 : fetch_word AsanUbsan.M.loaded_segments (0x61404 : word) = Some W_61404.
Proof. vm_refl. Qed.
Lemma D_61404 : decode_any W_61404 = Some (OpImm ALU_ADD 12 11 273, 4%Z).
Proof. vm_refl. Qed.

Definition W_61408 : bv 32 := 0x02f00593.
Lemma F_61408 : fetch_word AsanUbsan.M.loaded_segments (0x61408 : word) = Some W_61408.
Proof. vm_refl. Qed.
Lemma D_61408 : decode_any W_61408 = Some (OpImm ALU_ADD 11 0 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_6140c : bv 32 := 0x00000693.
Lemma F_6140c : fetch_word AsanUbsan.M.loaded_segments (0x6140c : word) = Some W_6140c.
Proof. vm_refl. Qed.
Lemma D_6140c : decode_any W_6140c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61410 : bv 32 := 0x00000713.
Lemma F_61410 : fetch_word AsanUbsan.M.loaded_segments (0x61410 : word) = Some W_61410.
Proof. vm_refl. Qed.
Lemma D_61410 : decode_any W_61410 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61414 : bv 32 := 0x6d5170ef.
Lemma F_61414 : fetch_word AsanUbsan.M.loaded_segments (0x61414 : word) = Some W_61414.
Proof. vm_refl. Qed.
Lemma D_61414 : decode_any W_61414 = Some (Jal 1 98004, 4%Z).
Proof. vm_refl. Qed.

Definition W_61418 : bv 32 := 0x00128293.
Lemma F_61418 : fetch_word AsanUbsan.M.loaded_segments (0x61418 : word) = Some W_61418.
Proof. vm_refl. Qed.
Lemma D_61418 : decode_any W_61418 = Some (OpImm ALU_ADD 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6141c : bv 32 := 0x0032d793.
Lemma F_6141c : fetch_word AsanUbsan.M.loaded_segments (0x6141c : word) = Some W_6141c.
Proof. vm_refl. Qed.
Lemma D_6141c : decode_any W_6141c = Some (ShiftImm ALU_SRL 15 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61420 : bv 32 := 0xfff78793.
Lemma F_61420 : fetch_word AsanUbsan.M.loaded_segments (0x61420 : word) = Some W_61420.
Proof. vm_refl. Qed.
Lemma D_61420 : decode_any W_61420 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_61424 : bv 32 := 0xfca7eae3.
Lemma F_61424 : fetch_word AsanUbsan.M.loaded_segments (0x61424 : word) = Some W_61424.
Proof. vm_refl. Qed.
Lemma D_61424 : decode_any W_61424 = Some (Branch BC_LTU 15 10 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_61428 : bv 32 := 0x0075f793.
Lemma F_61428 : fetch_word AsanUbsan.M.loaded_segments (0x61428 : word) = Some W_61428.
Proof. vm_refl. Qed.
Lemma D_61428 : decode_any W_61428 = Some (OpImm ALU_AND 15 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_6142c : bv 32 := 0x26079a63.
Lemma F_6142c : fetch_word AsanUbsan.M.loaded_segments (0x6142c : word) = Some W_6142c.
Proof. vm_refl. Qed.
Lemma D_6142c : decode_any W_6142c = Some (Branch BC_NE 15 0 628, 4%Z).
Proof. vm_refl. Qed.

Definition W_61430 : bv 32 := 0x00b505b3.
Lemma F_61430 : fetch_word AsanUbsan.M.loaded_segments (0x61430 : word) = Some W_61430.
Proof. vm_refl. Qed.
Lemma D_61430 : decode_any W_61430 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_61434 : bv 32 := 0xff858593.
Lemma F_61434 : fetch_word AsanUbsan.M.loaded_segments (0x61434 : word) = Some W_61434.
Proof. vm_refl. Qed.
Lemma D_61434 : decode_any W_61434 = Some (OpImm ALU_ADD 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_61438 : bv 32 := 0x04b77263.
Lemma F_61438 : fetch_word AsanUbsan.M.loaded_segments (0x61438 : word) = Some W_61438.
Proof. vm_refl. Qed.
Lemma D_61438 : decode_any W_61438 = Some (Branch BC_GEU 14 11 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_6143c : bv 32 := 0x00075717.
Lemma F_6143c : fetch_word AsanUbsan.M.loaded_segments (0x6143c : word) = Some W_6143c.
Proof. vm_refl. Qed.
Lemma D_6143c : decode_any W_6143c = Some (Auipc 14 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_61440 : bv 32 := 0x09473703.
Lemma F_61440 : fetch_word AsanUbsan.M.loaded_segments (0x61440 : word) = Some W_61440.
Proof. vm_refl. Qed.
Lemma D_61440 : decode_any W_61440 = Some (Load SZ8 true 14 14 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_61444 : bv 32 := 0x00075797.
Lemma F_61444 : fetch_word AsanUbsan.M.loaded_segments (0x61444 : word) = Some W_61444.
Proof. vm_refl. Qed.
Lemma D_61444 : decode_any W_61444 = Some (Auipc 15 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_61448 : bv 32 := 0x0947b783.
Lemma F_61448 : fetch_word AsanUbsan.M.loaded_segments (0x61448 : word) = Some W_61448.
Proof. vm_refl. Qed.
Lemma D_61448 : decode_any W_61448 = Some (Load SZ8 true 15 15 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_6144c : bv 32 := 0x00073883.
Lemma F_6144c : fetch_word AsanUbsan.M.loaded_segments (0x6144c : word) = Some W_6144c.
Proof. vm_refl. Qed.
Lemma D_6144c : decode_any W_6144c = Some (Load SZ8 true 17 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61450 : bv 32 := 0x0007b703.
Lemma F_61450 : fetch_word AsanUbsan.M.loaded_segments (0x61450 : word) = Some W_61450.
Proof. vm_refl. Qed.
Lemma D_61450 : decode_any W_61450 = Some (Load SZ8 true 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61454 : bv 32 := 0xfff88813.
Lemma F_61454 : fetch_word AsanUbsan.M.loaded_segments (0x61454 : word) = Some W_61454.
Proof. vm_refl. Qed.
Lemma D_61454 : decode_any W_61454 = Some (OpImm ALU_ADD 16 17 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_61458 : bv 32 := 0x00b87463.
Lemma F_61458 : fetch_word AsanUbsan.M.loaded_segments (0x61458 : word) = Some W_61458.
Proof. vm_refl. Qed.
Lemma D_61458 : decode_any W_61458 = Some (Branch BC_GEU 16 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6145c : bv 32 := 0x02b77063.
Lemma F_6145c : fetch_word AsanUbsan.M.loaded_segments (0x6145c : word) = Some W_6145c.
Proof. vm_refl. Qed.
Lemma D_6145c : decode_any W_6145c = Some (Branch BC_GEU 14 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_61460 : bv 32 := 0x00075797.
Lemma F_61460 : fetch_word AsanUbsan.M.loaded_segments (0x61460 : word) = Some W_61460.
Proof. vm_refl. Qed.
Lemma D_61460 : decode_any W_61460 = Some (Auipc 15 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_61464 : bv 32 := 0x0807b783.
Lemma F_61464 : fetch_word AsanUbsan.M.loaded_segments (0x61464 : word) = Some W_61464.
Proof. vm_refl. Qed.
Lemma D_61464 : decode_any W_61464 = Some (Load SZ8 true 15 15 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_61468 : bv 32 := 0x0007b303.
Lemma F_61468 : fetch_word AsanUbsan.M.loaded_segments (0x61468 : word) = Some W_61468.
Proof. vm_refl. Qed.
Lemma D_61468 : decode_any W_61468 = Some (Load SZ8 true 6 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6146c : bv 32 := 0x00335793.
Lemma F_6146c : fetch_word AsanUbsan.M.loaded_segments (0x6146c : word) = Some W_6146c.
Proof. vm_refl. Qed.
Lemma D_6146c : decode_any W_6146c = Some (ShiftImm ALU_SRL 15 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61470 : bv 32 := 0x009782b3.
Lemma F_61470 : fetch_word AsanUbsan.M.loaded_segments (0x61470 : word) = Some W_61470.
Proof. vm_refl. Qed.
Lemma D_61470 : decode_any W_61470 = Some (Op ALU_ADD 5 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_61474 : bv 32 := 0x12b36263.
Lemma F_61474 : fetch_word AsanUbsan.M.loaded_segments (0x61474 : word) = Some W_61474.
Proof. vm_refl. Qed.
Lemma D_61474 : decode_any W_61474 = Some (Branch BC_LTU 6 11 292, 4%Z).
Proof. vm_refl. Qed.

Definition W_61478 : bv 32 := 0x12b2f063.
Lemma F_61478 : fetch_word AsanUbsan.M.loaded_segments (0x61478 : word) = Some W_61478.
Proof. vm_refl. Qed.
Lemma D_61478 : decode_any W_61478 = Some (Branch BC_GEU 5 11 288, 4%Z).
Proof. vm_refl. Qed.

Definition W_6147c : bv 32 := 0x00075697.
Lemma F_6147c : fetch_word AsanUbsan.M.loaded_segments (0x6147c : word) = Some W_6147c.
Proof. vm_refl. Qed.
Lemma D_6147c : decode_any W_6147c = Some (Auipc 13 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_61480 : bv 32 := 0x06c6b983.
Lemma F_61480 : fetch_word AsanUbsan.M.loaded_segments (0x61480 : word) = Some W_61480.
Proof. vm_refl. Qed.
Lemma D_61480 : decode_any W_61480 = Some (Load SZ8 true 19 13 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_61484 : bv 32 := 0x0009b303.
Lemma F_61484 : fetch_word AsanUbsan.M.loaded_segments (0x61484 : word) = Some W_61484.
Proof. vm_refl. Qed.
Lemma D_61484 : decode_any W_61484 = Some (Load SZ8 true 6 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61488 : bv 32 := 0x22030c63.
Lemma F_61488 : fetch_word AsanUbsan.M.loaded_segments (0x61488 : word) = Some W_61488.
Proof. vm_refl. Qed.
Lemma D_61488 : decode_any W_61488 = Some (Branch BC_EQ 6 0 568, 4%Z).
Proof. vm_refl. Qed.

Definition W_6148c : bv 32 := 0x00355693.
Lemma F_6148c : fetch_word AsanUbsan.M.loaded_segments (0x6148c : word) = Some W_6148c.
Proof. vm_refl. Qed.
Lemma D_6148c : decode_any W_6148c = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61490 : bv 32 := 0x0035d593.
Lemma F_61490 : fetch_word AsanUbsan.M.loaded_segments (0x61490 : word) = Some W_61490.
Proof. vm_refl. Qed.
Lemma D_61490 : decode_any W_61490 = Some (ShiftImm ALU_SRL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61494 : bv 32 := 0x00d48533.
Lemma F_61494 : fetch_word AsanUbsan.M.loaded_segments (0x61494 : word) = Some W_61494.
Proof. vm_refl. Qed.
Lemma D_61494 : decode_any W_61494 = Some (Op ALU_ADD 10 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_61498 : bv 32 := 0x00158913.
Lemma F_61498 : fetch_word AsanUbsan.M.loaded_segments (0x61498 : word) = Some W_61498.
Proof. vm_refl. Qed.
Lemma D_61498 : decode_any W_61498 = Some (OpImm ALU_ADD 18 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6149c : bv 32 := 0x40d90433.
Lemma F_6149c : fetch_word AsanUbsan.M.loaded_segments (0x6149c : word) = Some W_6149c.
Proof. vm_refl. Qed.
Lemma D_6149c : decode_any W_6149c = Some (Op ALU_SUB 8 18 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_614a0 : bv 32 := 0x0c061063.
Lemma F_614a0 : fetch_word AsanUbsan.M.loaded_segments (0x614a0 : word) = Some W_614a0.
Proof. vm_refl. Qed.
Lemma D_614a0 : decode_any W_614a0 = Some (Branch BC_NE 12 0 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_614a4 : bv 32 := 0x00075597.
Lemma F_614a4 : fetch_word AsanUbsan.M.loaded_segments (0x614a4 : word) = Some W_614a4.
Proof. vm_refl. Qed.
Lemma D_614a4 : decode_any W_614a4 = Some (Auipc 11 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_614a8 : bv 32 := 0x0145b583.
Lemma F_614a8 : fetch_word AsanUbsan.M.loaded_segments (0x614a8 : word) = Some W_614a8.
Proof. vm_refl. Qed.
Lemma D_614a8 : decode_any W_614a8 = Some (Load SZ8 true 11 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_614ac : bv 32 := 0x0785b583.
Lemma F_614ac : fetch_word AsanUbsan.M.loaded_segments (0x614ac : word) = Some W_614ac.
Proof. vm_refl. Qed.
Lemma D_614ac : decode_any W_614ac = Some (Load SZ8 true 11 11 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_614b0 : bv 32 := 0x0ab46863.
Lemma F_614b0 : fetch_word AsanUbsan.M.loaded_segments (0x614b0 : word) = Some W_614b0.
Proof. vm_refl. Qed.
Lemma D_614b0 : decode_any W_614b0 = Some (Branch BC_LTU 8 11 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_614b4 : bv 32 := 0x00075597.
Lemma F_614b4 : fetch_word AsanUbsan.M.loaded_segments (0x614b4 : word) = Some W_614b4.
Proof. vm_refl. Qed.
Lemma D_614b4 : decode_any W_614b4 = Some (Auipc 11 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_614b8 : bv 32 := 0xff45ba03.
Lemma F_614b8 : fetch_word AsanUbsan.M.loaded_segments (0x614b8 : word) = Some W_614b8.
Proof. vm_refl. Qed.
Lemma D_614b8 : decode_any W_614b8 = Some (Load SZ8 true 20 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_614bc : bv 32 := 0x000a3583.
Lemma F_614bc : fetch_word AsanUbsan.M.loaded_segments (0x614bc : word) = Some W_614bc.
Proof. vm_refl. Qed.
Lemma D_614bc : decode_any W_614bc = Some (Load SZ8 true 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_614c0 : bv 32 := 0x00059c63.
Lemma F_614c0 : fetch_word AsanUbsan.M.loaded_segments (0x614c0 : word) = Some W_614c0.
Proof. vm_refl. Qed.
Lemma D_614c0 : decode_any W_614c0 = Some (Branch BC_NE 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_614c4 : bv 32 := 0x00050a93.
Lemma F_614c4 : fetch_word AsanUbsan.M.loaded_segments (0x614c4 : word) = Some W_614c4.
Proof. vm_refl. Qed.
Lemma D_614c4 : decode_any W_614c4 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_614c8 : bv 32 := 0x045110ef.
Lemma F_614c8 : fetch_word AsanUbsan.M.loaded_segments (0x614c8 : word) = Some W_614c8.
Proof. vm_refl. Qed.
Lemma D_614c8 : decode_any W_614c8 = Some (Jal 1 71748, 4%Z).
Proof. vm_refl. Qed.

Definition W_614cc : bv 32 := 0x00050593.
Lemma F_614cc : fetch_word AsanUbsan.M.loaded_segments (0x614cc : word) = Some W_614cc.
Proof. vm_refl. Qed.
Lemma D_614cc : decode_any W_614cc = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_614d0 : bv 32 := 0x000a8513.
Lemma F_614d0 : fetch_word AsanUbsan.M.loaded_segments (0x614d0 : word) = Some W_614d0.
Proof. vm_refl. Qed.
Lemma D_614d0 : decode_any W_614d0 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_614d4 : bv 32 := 0x00ba3023.
Lemma F_614d4 : fetch_word AsanUbsan.M.loaded_segments (0x614d4 : word) = Some W_614d4.
Proof. vm_refl. Qed.
Lemma D_614d4 : decode_any W_614d4 = Some (Store SZ8 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_614d8 : bv 32 := 0xfff58613.
Lemma F_614d8 : fetch_word AsanUbsan.M.loaded_segments (0x614d8 : word) = Some W_614d8.
Proof. vm_refl. Qed.
Lemma D_614d8 : decode_any W_614d8 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_614dc : bv 32 := 0x00c5f633.
Lemma F_614dc : fetch_word AsanUbsan.M.loaded_segments (0x614dc : word) = Some W_614dc.
Proof. vm_refl. Qed.
Lemma D_614dc : decode_any W_614dc = Some (Op ALU_AND 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_614e0 : bv 32 := 0x20061063.
Lemma F_614e0 : fetch_word AsanUbsan.M.loaded_segments (0x614e0 : word) = Some W_614e0.
Proof. vm_refl. Qed.
Lemma D_614e0 : decode_any W_614e0 = Some (Branch BC_NE 12 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_614e4 : bv 32 := 0x00990a33.
Lemma F_614e4 : fetch_word AsanUbsan.M.loaded_segments (0x614e4 : word) = Some W_614e4.
Proof. vm_refl. Qed.
Lemma D_614e4 : decode_any W_614e4 = Some (Op ALU_ADD 20 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_614e8 : bv 32 := 0x00b50633.
Lemma F_614e8 : fetch_word AsanUbsan.M.loaded_segments (0x614e8 : word) = Some W_614e8.
Proof. vm_refl. Qed.
Lemma D_614e8 : decode_any W_614e8 = Some (Op ALU_ADD 12 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_614ec : bv 32 := 0x40b005b3.
Lemma F_614ec : fetch_word AsanUbsan.M.loaded_segments (0x614ec : word) = Some W_614ec.
Proof. vm_refl. Qed.
Lemma D_614ec : decode_any W_614ec = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_614f0 : bv 32 := 0xfff60613.
Lemma F_614f0 : fetch_word AsanUbsan.M.loaded_segments (0x614f0 : word) = Some W_614f0.
Proof. vm_refl. Qed.
Lemma D_614f0 : decode_any W_614f0 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_614f4 : bv 32 := 0x00b674b3.
Lemma F_614f4 : fetch_word AsanUbsan.M.loaded_segments (0x614f4 : word) = Some W_614f4.
Proof. vm_refl. Qed.
Lemma D_614f4 : decode_any W_614f4 = Some (Op ALU_AND 9 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_614f8 : bv 32 := 0x00ba7933.
Lemma F_614f8 : fetch_word AsanUbsan.M.loaded_segments (0x614f8 : word) = Some W_614f8.
Proof. vm_refl. Qed.
Lemma D_614f8 : decode_any W_614f8 = Some (Op ALU_AND 18 20 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_614fc : bv 32 := 0x0724f663.
Lemma F_614fc : fetch_word AsanUbsan.M.loaded_segments (0x614fc : word) = Some W_614fc.
Proof. vm_refl. Qed.
Lemma D_614fc : decode_any W_614fc = Some (Branch BC_GEU 9 18 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_61500 : bv 32 := 0x00a48a63.
Lemma F_61500 : fetch_word AsanUbsan.M.loaded_segments (0x61500 : word) = Some W_61500.
Proof. vm_refl. Qed.
Lemma D_61500 : decode_any W_61500 = Some (Branch BC_EQ 9 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_61504 : bv 32 := 0x0009b683.
Lemma F_61504 : fetch_word AsanUbsan.M.loaded_segments (0x61504 : word) = Some W_61504.
Proof. vm_refl. Qed.
Lemma D_61504 : decode_any W_61504 = Some (Load SZ8 true 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61508 : bv 32 := 0x40a48633.
Lemma F_61508 : fetch_word AsanUbsan.M.loaded_segments (0x61508 : word) = Some W_61508.
Proof. vm_refl. Qed.
Lemma D_61508 : decode_any W_61508 = Some (Op ALU_SUB 12 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6150c : bv 32 := 0x00000593.
Lemma F_6150c : fetch_word AsanUbsan.M.loaded_segments (0x6150c : word) = Some W_6150c.
Proof. vm_refl. Qed.
Lemma D_6150c : decode_any W_6150c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61510 : bv 32 := 0x000680e7.
Lemma F_61510 : fetch_word AsanUbsan.M.loaded_segments (0x61510 : word) = Some W_61510.
Proof. vm_refl. Qed.
Lemma D_61510 : decode_any W_61510 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61514 : bv 32 := 0x012a0c63.
Lemma F_61514 : fetch_word AsanUbsan.M.loaded_segments (0x61514 : word) = Some W_61514.
Proof. vm_refl. Qed.
Lemma D_61514 : decode_any W_61514 = Some (Branch BC_EQ 20 18 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_61518 : bv 32 := 0x0009b683.
Lemma F_61518 : fetch_word AsanUbsan.M.loaded_segments (0x61518 : word) = Some W_61518.
Proof. vm_refl. Qed.
Lemma D_61518 : decode_any W_61518 = Some (Load SZ8 true 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6151c : bv 32 := 0x412a0633.
Lemma F_6151c : fetch_word AsanUbsan.M.loaded_segments (0x6151c : word) = Some W_6151c.
Proof. vm_refl. Qed.
Lemma D_6151c : decode_any W_6151c = Some (Op ALU_SUB 12 20 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_61520 : bv 32 := 0x00090513.
Lemma F_61520 : fetch_word AsanUbsan.M.loaded_segments (0x61520 : word) = Some W_61520.
Proof. vm_refl. Qed.
Lemma D_61520 : decode_any W_61520 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61524 : bv 32 := 0x00000593.
Lemma F_61524 : fetch_word AsanUbsan.M.loaded_segments (0x61524 : word) = Some W_61524.
Proof. vm_refl. Qed.
Lemma D_61524 : decode_any W_61524 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61528 : bv 32 := 0x000680e7.
Lemma F_61528 : fetch_word AsanUbsan.M.loaded_segments (0x61528 : word) = Some W_61528.
Proof. vm_refl. Qed.
Lemma D_61528 : decode_any W_61528 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6152c : bv 32 := 0xfff90593.
Lemma F_6152c : fetch_word AsanUbsan.M.loaded_segments (0x6152c : word) = Some W_6152c.
Proof. vm_refl. Qed.
Lemma D_6152c : decode_any W_6152c = Some (OpImm ALU_ADD 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_61530 : bv 32 := 0x00100693.
Lemma F_61530 : fetch_word AsanUbsan.M.loaded_segments (0x61530 : word) = Some W_61530.
Proof. vm_refl. Qed.
Lemma D_61530 : decode_any W_61530 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61534 : bv 32 := 0x00048513.
Lemma F_61534 : fetch_word AsanUbsan.M.loaded_segments (0x61534 : word) = Some W_61534.
Proof. vm_refl. Qed.
Lemma D_61534 : decode_any W_61534 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61538 : bv 32 := 0x00000613.
Lemma F_61538 : fetch_word AsanUbsan.M.loaded_segments (0x61538 : word) = Some W_61538.
Proof. vm_refl. Qed.
Lemma D_61538 : decode_any W_61538 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6153c : bv 32 := 0x03813083.
Lemma F_6153c : fetch_word AsanUbsan.M.loaded_segments (0x6153c : word) = Some W_6153c.
Proof. vm_refl. Qed.
Lemma D_6153c : decode_any W_6153c = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_61540 : bv 32 := 0x03013403.
Lemma F_61540 : fetch_word AsanUbsan.M.loaded_segments (0x61540 : word) = Some W_61540.
Proof. vm_refl. Qed.
Lemma D_61540 : decode_any W_61540 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_61544 : bv 32 := 0x02813483.
Lemma F_61544 : fetch_word AsanUbsan.M.loaded_segments (0x61544 : word) = Some W_61544.
Proof. vm_refl. Qed.
Lemma D_61544 : decode_any W_61544 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_61548 : bv 32 := 0x02013903.
Lemma F_61548 : fetch_word AsanUbsan.M.loaded_segments (0x61548 : word) = Some W_61548.
Proof. vm_refl. Qed.
Lemma D_61548 : decode_any W_61548 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6154c : bv 32 := 0x01813983.
Lemma F_6154c : fetch_word AsanUbsan.M.loaded_segments (0x6154c : word) = Some W_6154c.
Proof. vm_refl. Qed.
Lemma D_6154c : decode_any W_6154c = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_61550 : bv 32 := 0x01013a03.
Lemma F_61550 : fetch_word AsanUbsan.M.loaded_segments (0x61550 : word) = Some W_61550.
Proof. vm_refl. Qed.
Lemma D_61550 : decode_any W_61550 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_61554 : bv 32 := 0x00813a83.
Lemma F_61554 : fetch_word AsanUbsan.M.loaded_segments (0x61554 : word) = Some W_61554.
Proof. vm_refl. Qed.
Lemma D_61554 : decode_any W_61554 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_61558 : bv 32 := 0x04010113.
Lemma F_61558 : fetch_word AsanUbsan.M.loaded_segments (0x61558 : word) = Some W_61558.
Proof. vm_refl. Qed.
Lemma D_61558 : decode_any W_61558 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6155c : bv 32 := 0x5941806f.
Lemma F_6155c : fetch_word AsanUbsan.M.loaded_segments (0x6155c : word) = Some W_6155c.
Proof. vm_refl. Qed.
Lemma D_6155c : decode_any W_6155c = Some (Jal 0 99732, 4%Z).
Proof. vm_refl. Qed.

Definition W_61560 : bv 32 := 0x00060593.
Lemma F_61560 : fetch_word AsanUbsan.M.loaded_segments (0x61560 : word) = Some W_61560.
Proof. vm_refl. Qed.
Lemma D_61560 : decode_any W_61560 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61564 : bv 32 := 0x00c0006f.
Lemma F_61564 : fetch_word AsanUbsan.M.loaded_segments (0x61564 : word) = Some W_61564.
Proof. vm_refl. Qed.
Lemma D_61564 : decode_any W_61564 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_61568 : bv 32 := 0x0009b303.
Lemma F_61568 : fetch_word AsanUbsan.M.loaded_segments (0x61568 : word) = Some W_61568.
Proof. vm_refl. Qed.
Lemma D_61568 : decode_any W_61568 = Some (Load SZ8 true 6 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6156c : bv 32 := 0x00000593.
Lemma F_6156c : fetch_word AsanUbsan.M.loaded_segments (0x6156c : word) = Some W_6156c.
Proof. vm_refl. Qed.
Lemma D_6156c : decode_any W_6156c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61570 : bv 32 := 0x00040613.
Lemma F_61570 : fetch_word AsanUbsan.M.loaded_segments (0x61570 : word) = Some W_61570.
Proof. vm_refl. Qed.
Lemma D_61570 : decode_any W_61570 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61574 : bv 32 := 0x03813083.
Lemma F_61574 : fetch_word AsanUbsan.M.loaded_segments (0x61574 : word) = Some W_61574.
Proof. vm_refl. Qed.
Lemma D_61574 : decode_any W_61574 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_61578 : bv 32 := 0x03013403.
Lemma F_61578 : fetch_word AsanUbsan.M.loaded_segments (0x61578 : word) = Some W_61578.
Proof. vm_refl. Qed.
Lemma D_61578 : decode_any W_61578 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_6157c : bv 32 := 0x02813483.
Lemma F_6157c : fetch_word AsanUbsan.M.loaded_segments (0x6157c : word) = Some W_6157c.
Proof. vm_refl. Qed.
Lemma D_6157c : decode_any W_6157c = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_61580 : bv 32 := 0x02013903.
Lemma F_61580 : fetch_word AsanUbsan.M.loaded_segments (0x61580 : word) = Some W_61580.
Proof. vm_refl. Qed.
Lemma D_61580 : decode_any W_61580 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_61584 : bv 32 := 0x01813983.
Lemma F_61584 : fetch_word AsanUbsan.M.loaded_segments (0x61584 : word) = Some W_61584.
Proof. vm_refl. Qed.
Lemma D_61584 : decode_any W_61584 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_61588 : bv 32 := 0x01013a03.
Lemma F_61588 : fetch_word AsanUbsan.M.loaded_segments (0x61588 : word) = Some W_61588.
Proof. vm_refl. Qed.
Lemma D_61588 : decode_any W_61588 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6158c : bv 32 := 0x00813a83.
Lemma F_6158c : fetch_word AsanUbsan.M.loaded_segments (0x6158c : word) = Some W_6158c.
Proof. vm_refl. Qed.
Lemma D_6158c : decode_any W_6158c = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_61590 : bv 32 := 0x04010113.
Lemma F_61590 : fetch_word AsanUbsan.M.loaded_segments (0x61590 : word) = Some W_61590.
Proof. vm_refl. Qed.
Lemma D_61590 : decode_any W_61590 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_61594 : bv 32 := 0x00030067.
Lemma F_61594 : fetch_word AsanUbsan.M.loaded_segments (0x61594 : word) = Some W_61594.
Proof. vm_refl. Qed.
Lemma D_61594 : decode_any W_61594 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61598 : bv 32 := 0x00075317.
Lemma F_61598 : fetch_word AsanUbsan.M.loaded_segments (0x61598 : word) = Some W_61598.
Proof. vm_refl. Qed.
Lemma D_61598 : decode_any W_61598 = Some (Auipc 6 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_6159c : bv 32 := 0xf2833303.
Lemma F_6159c : fetch_word AsanUbsan.M.loaded_segments (0x6159c : word) = Some W_6159c.
Proof. vm_refl. Qed.
Lemma D_6159c : decode_any W_6159c = Some (Load SZ8 true 6 6 3880, 4%Z).
Proof. vm_refl. Qed.

Definition W_615a0 : bv 32 := 0x04e34303.
Lemma F_615a0 : fetch_word AsanUbsan.M.loaded_segments (0x615a0 : word) = Some W_615a0.
Proof. vm_refl. Qed.
Lemma D_615a0 : decode_any W_615a0 = Some (Load SZ1 false 6 6 78, 4%Z).
Proof. vm_refl. Qed.

Definition W_615a4 : bv 32 := 0x08031e63.
Lemma F_615a4 : fetch_word AsanUbsan.M.loaded_segments (0x615a4 : word) = Some W_615a4.
Proof. vm_refl. Qed.
Lemma D_615a4 : decode_any W_615a4 = Some (Branch BC_NE 6 0 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_615a8 : bv 32 := 0x04088063.
Lemma F_615a8 : fetch_word AsanUbsan.M.loaded_segments (0x615a8 : word) = Some W_615a8.
Proof. vm_refl. Qed.
Lemma D_615a8 : decode_any W_615a8 = Some (Branch BC_EQ 17 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_615ac : bv 32 := 0x0038d893.
Lemma F_615ac : fetch_word AsanUbsan.M.loaded_segments (0x615ac : word) = Some W_615ac.
Proof. vm_refl. Qed.
Lemma D_615ac : decode_any W_615ac = Some (ShiftImm ALU_SRL 17 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_615b0 : bv 32 := 0x00d888b3.
Lemma F_615b0 : fetch_word AsanUbsan.M.loaded_segments (0x615b0 : word) = Some W_615b0.
Proof. vm_refl. Qed.
Lemma D_615b0 : decode_any W_615b0 = Some (Op ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_615b4 : bv 32 := 0x06b8f063.
Lemma F_615b4 : fetch_word AsanUbsan.M.loaded_segments (0x615b4 : word) = Some W_615b4.
Proof. vm_refl. Qed.
Lemma D_615b4 : decode_any W_615b4 = Some (Branch BC_GEU 17 11 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_615b8 : bv 32 := 0x00148893.
Lemma F_615b8 : fetch_word AsanUbsan.M.loaded_segments (0x615b8 : word) = Some W_615b8.
Proof. vm_refl. Qed.
Lemma D_615b8 : decode_any W_615b8 = Some (OpImm ALU_ADD 17 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_615bc : bv 32 := 0x00b86863.
Lemma F_615bc : fetch_word AsanUbsan.M.loaded_segments (0x615bc : word) = Some W_615bc.
Proof. vm_refl. Qed.
Lemma D_615bc : decode_any W_615bc = Some (Branch BC_LTU 16 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_615c0 : bv 32 := 0x00375813.
Lemma F_615c0 : fetch_word AsanUbsan.M.loaded_segments (0x615c0 : word) = Some W_615c0.
Proof. vm_refl. Qed.
Lemma D_615c0 : decode_any W_615c0 = Some (ShiftImm ALU_SRL 16 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_615c4 : bv 32 := 0x01180833.
Lemma F_615c4 : fetch_word AsanUbsan.M.loaded_segments (0x615c4 : word) = Some W_615c4.
Proof. vm_refl. Qed.
Lemma D_615c4 : decode_any W_615c4 = Some (Op ALU_ADD 16 16 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_615c8 : bv 32 := 0xeb05fae3.
Lemma F_615c8 : fetch_word AsanUbsan.M.loaded_segments (0x615c8 : word) = Some W_615c8.
Proof. vm_refl. Qed.
Lemma D_615c8 : decode_any W_615c8 = Some (Branch BC_GEU 11 16 7860, 4%Z).
Proof. vm_refl. Qed.

Definition W_615cc : bv 32 := 0x00170713.
Lemma F_615cc : fetch_word AsanUbsan.M.loaded_segments (0x615cc : word) = Some W_615cc.
Proof. vm_refl. Qed.
Lemma D_615cc : decode_any W_615cc = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_615d0 : bv 32 := 0x06e5e863.
Lemma F_615d0 : fetch_word AsanUbsan.M.loaded_segments (0x615d0 : word) = Some W_615d0.
Proof. vm_refl. Qed.
Lemma D_615d0 : decode_any W_615d0 = Some (Branch BC_LTU 11 14 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_615d4 : bv 32 := 0x011787b3.
Lemma F_615d4 : fetch_word AsanUbsan.M.loaded_segments (0x615d4 : word) = Some W_615d4.
Proof. vm_refl. Qed.
Lemma D_615d4 : decode_any W_615d4 = Some (Op ALU_ADD 15 15 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_615d8 : bv 32 := 0x0037d793.
Lemma F_615d8 : fetch_word AsanUbsan.M.loaded_segments (0x615d8 : word) = Some W_615d8.
Proof. vm_refl. Qed.
Lemma D_615d8 : decode_any W_615d8 = Some (ShiftImm ALU_SRL 15 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_615dc : bv 32 := 0x00d786b3.
Lemma F_615dc : fetch_word AsanUbsan.M.loaded_segments (0x615dc : word) = Some W_615dc.
Proof. vm_refl. Qed.
Lemma D_615dc : decode_any W_615dc = Some (Op ALU_ADD 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_615e0 : bv 32 := 0xe8b6fee3.
Lemma F_615e0 : fetch_word AsanUbsan.M.loaded_segments (0x615e0 : word) = Some W_615e0.
Proof. vm_refl. Qed.
Lemma D_615e0 : decode_any W_615e0 = Some (Branch BC_GEU 13 11 7836, 4%Z).
Proof. vm_refl. Qed.

Definition W_615e4 : bv 32 := 0x05c0006f.
Lemma F_615e4 : fetch_word AsanUbsan.M.loaded_segments (0x615e4 : word) = Some W_615e4.
Proof. vm_refl. Qed.
Lemma D_615e4 : decode_any W_615e4 = Some (Jal 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_615e8 : bv 32 := 0x04048463.
Lemma F_615e8 : fetch_word AsanUbsan.M.loaded_segments (0x615e8 : word) = Some W_615e8.
Proof. vm_refl. Qed.
Lemma D_615e8 : decode_any W_615e8 = Some (Branch BC_EQ 9 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_615ec : bv 32 := 0x0036d713.
Lemma F_615ec : fetch_word AsanUbsan.M.loaded_segments (0x615ec : word) = Some W_615ec.
Proof. vm_refl. Qed.
Lemma D_615ec : decode_any W_615ec = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_615f0 : bv 32 := 0x00970733.
Lemma F_615f0 : fetch_word AsanUbsan.M.loaded_segments (0x615f0 : word) = Some W_615f0.
Proof. vm_refl. Qed.
Lemma D_615f0 : decode_any W_615f0 = Some (Op ALU_ADD 14 14 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_615f4 : bv 32 := 0x00070663.
Lemma F_615f4 : fetch_word AsanUbsan.M.loaded_segments (0x615f4 : word) = Some W_615f4.
Proof. vm_refl. Qed.
Lemma D_615f4 : decode_any W_615f4 = Some (Branch BC_EQ 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_615f8 : bv 32 := 0x00170713.
Lemma F_615f8 : fetch_word AsanUbsan.M.loaded_segments (0x615f8 : word) = Some W_615f8.
Proof. vm_refl. Qed.
Lemma D_615f8 : decode_any W_615f8 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_615fc : bv 32 := 0x04e5e263.
Lemma F_615fc : fetch_word AsanUbsan.M.loaded_segments (0x615fc : word) = Some W_615fc.
Proof. vm_refl. Qed.
Lemma D_615fc : decode_any W_615fc = Some (Branch BC_LTU 11 14 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_61600 : bv 32 := 0x00128293.
Lemma F_61600 : fetch_word AsanUbsan.M.loaded_segments (0x61600 : word) = Some W_61600.
Proof. vm_refl. Qed.
Lemma D_61600 : decode_any W_61600 = Some (OpImm ALU_ADD 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61604 : bv 32 := 0x0032d713.
Lemma F_61604 : fetch_word AsanUbsan.M.loaded_segments (0x61604 : word) = Some W_61604.
Proof. vm_refl. Qed.
Lemma D_61604 : decode_any W_61604 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61608 : bv 32 := 0x00d706b3.
Lemma F_61608 : fetch_word AsanUbsan.M.loaded_segments (0x61608 : word) = Some W_61608.
Proof. vm_refl. Qed.
Lemma D_61608 : decode_any W_61608 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6160c : bv 32 := 0xe6b6f8e3.
Lemma F_6160c : fetch_word AsanUbsan.M.loaded_segments (0x6160c : word) = Some W_6160c.
Proof. vm_refl. Qed.
Lemma D_6160c : decode_any W_6160c = Some (Branch BC_GEU 13 11 7792, 4%Z).
Proof. vm_refl. Qed.

Definition W_61610 : bv 32 := 0x0300006f.
Lemma F_61610 : fetch_word AsanUbsan.M.loaded_segments (0x61610 : word) = Some W_61610.
Proof. vm_refl. Qed.
Lemma D_61610 : decode_any W_61610 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_61614 : bv 32 := 0xe60484e3.
Lemma F_61614 : fetch_word AsanUbsan.M.loaded_segments (0x61614 : word) = Some W_61614.
Proof. vm_refl. Qed.
Lemma D_61614 : decode_any W_61614 = Some (Branch BC_EQ 9 0 7784, 4%Z).
Proof. vm_refl. Qed.

Definition W_61618 : bv 32 := 0x0036d693.
Lemma F_61618 : fetch_word AsanUbsan.M.loaded_segments (0x61618 : word) = Some W_61618.
Proof. vm_refl. Qed.
Lemma D_61618 : decode_any W_61618 = Some (ShiftImm ALU_SRL 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6161c : bv 32 := 0x009686b3.
Lemma F_6161c : fetch_word AsanUbsan.M.loaded_segments (0x6161c : word) = Some W_6161c.
Proof. vm_refl. Qed.
Lemma D_6161c : decode_any W_6161c = Some (Op ALU_ADD 13 13 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_61620 : bv 32 := 0xe4068ee3.
Lemma F_61620 : fetch_word AsanUbsan.M.loaded_segments (0x61620 : word) = Some W_61620.
Proof. vm_refl. Qed.
Lemma D_61620 : decode_any W_61620 = Some (Branch BC_EQ 13 0 7772, 4%Z).
Proof. vm_refl. Qed.

Definition W_61624 : bv 32 := 0x00168693.
Lemma F_61624 : fetch_word AsanUbsan.M.loaded_segments (0x61624 : word) = Some W_61624.
Proof. vm_refl. Qed.
Lemma D_61624 : decode_any W_61624 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61628 : bv 32 := 0xe4d5fae3.
Lemma F_61628 : fetch_word AsanUbsan.M.loaded_segments (0x61628 : word) = Some W_61628.
Proof. vm_refl. Qed.
Lemma D_61628 : decode_any W_61628 = Some (Branch BC_GEU 11 13 7764, 4%Z).
Proof. vm_refl. Qed.

Definition W_6162c : bv 32 := 0x0140006f.
Lemma F_6162c : fetch_word AsanUbsan.M.loaded_segments (0x6162c : word) = Some W_6162c.
Proof. vm_refl. Qed.
Lemma D_6162c : decode_any W_6162c = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_61630 : bv 32 := 0x00178793.
Lemma F_61630 : fetch_word AsanUbsan.M.loaded_segments (0x61630 : word) = Some W_61630.
Proof. vm_refl. Qed.
Lemma D_61630 : decode_any W_61630 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61634 : bv 32 := 0x0037d793.
Lemma F_61634 : fetch_word AsanUbsan.M.loaded_segments (0x61634 : word) = Some W_61634.
Proof. vm_refl. Qed.
Lemma D_61634 : decode_any W_61634 = Some (ShiftImm ALU_SRL 15 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61638 : bv 32 := 0xfff78793.
Lemma F_61638 : fetch_word AsanUbsan.M.loaded_segments (0x61638 : word) = Some W_61638.
Proof. vm_refl. Qed.
Lemma D_61638 : decode_any W_61638 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6163c : bv 32 := 0xe4b7f0e3.
Lemma F_6163c : fetch_word AsanUbsan.M.loaded_segments (0x6163c : word) = Some W_6163c.
Proof. vm_refl. Qed.
Lemma D_6163c : decode_any W_6163c = Some (Branch BC_GEU 15 11 7744, 4%Z).
Proof. vm_refl. Qed.

Definition W_61640 : bv 32 := 0xfffbf517.
Lemma F_61640 : fetch_word AsanUbsan.M.loaded_segments (0x61640 : word) = Some W_61640.
Proof. vm_refl. Qed.
Lemma D_61640 : decode_any W_61640 = Some (Auipc 10 1048511, 4%Z).
Proof. vm_refl. Qed.

Definition W_61644 : bv 32 := 0xfffb3597.
Lemma F_61644 : fetch_word AsanUbsan.M.loaded_segments (0x61644 : word) = Some W_61644.
Proof. vm_refl. Qed.
Lemma D_61644 : decode_any W_61644 = Some (Auipc 11 1048499, 4%Z).
Proof. vm_refl. Qed.

Definition W_61648 : bv 32 := 0x67050513.
Lemma F_61648 : fetch_word AsanUbsan.M.loaded_segments (0x61648 : word) = Some W_61648.
Proof. vm_refl. Qed.
Lemma D_61648 : decode_any W_61648 = Some (OpImm ALU_ADD 10 10 1648, 4%Z).
Proof. vm_refl. Qed.

Definition W_6164c : bv 32 := 0x86b58613.
Lemma F_6164c : fetch_word AsanUbsan.M.loaded_segments (0x6164c : word) = Some W_6164c.
Proof. vm_refl. Qed.
Lemma D_6164c : decode_any W_6164c = Some (OpImm ALU_ADD 12 11 2155, 4%Z).
Proof. vm_refl. Qed.

Definition W_61650 : bv 32 := 0x03100593.
Lemma F_61650 : fetch_word AsanUbsan.M.loaded_segments (0x61650 : word) = Some W_61650.
Proof. vm_refl. Qed.
Lemma D_61650 : decode_any W_61650 = Some (OpImm ALU_ADD 11 0 49, 4%Z).
Proof. vm_refl. Qed.

Definition W_61654 : bv 32 := 0x00000693.
Lemma F_61654 : fetch_word AsanUbsan.M.loaded_segments (0x61654 : word) = Some W_61654.
Proof. vm_refl. Qed.
Lemma D_61654 : decode_any W_61654 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61658 : bv 32 := 0x00000713.
Lemma F_61658 : fetch_word AsanUbsan.M.loaded_segments (0x61658 : word) = Some W_61658.
Proof. vm_refl. Qed.
Lemma D_61658 : decode_any W_61658 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6165c : bv 32 := 0x48d170ef.
Lemma F_6165c : fetch_word AsanUbsan.M.loaded_segments (0x6165c : word) = Some W_6165c.
Proof. vm_refl. Qed.
Lemma D_6165c : decode_any W_6165c = Some (Jal 1 97420, 4%Z).
Proof. vm_refl. Qed.

Definition W_61660 : bv 32 := 0xfffbf517.
Lemma F_61660 : fetch_word AsanUbsan.M.loaded_segments (0x61660 : word) = Some W_61660.
Proof. vm_refl. Qed.
Lemma D_61660 : decode_any W_61660 = Some (Auipc 10 1048511, 4%Z).
Proof. vm_refl. Qed.

Definition W_61664 : bv 32 := 0xfffbd597.
Lemma F_61664 : fetch_word AsanUbsan.M.loaded_segments (0x61664 : word) = Some W_61664.
Proof. vm_refl. Qed.
Lemma D_61664 : decode_any W_61664 = Some (Auipc 11 1048509, 4%Z).
Proof. vm_refl. Qed.

Definition W_61668 : bv 32 := 0x65050513.
Lemma F_61668 : fetch_word AsanUbsan.M.loaded_segments (0x61668 : word) = Some W_61668.
Proof. vm_refl. Qed.
Lemma D_61668 : decode_any W_61668 = Some (OpImm ALU_ADD 10 10 1616, 4%Z).
Proof. vm_refl. Qed.

Definition W_6166c : bv 32 := 0x17e58613.
Lemma F_6166c : fetch_word AsanUbsan.M.loaded_segments (0x6166c : word) = Some W_6166c.
Proof. vm_refl. Qed.
Lemma D_6166c : decode_any W_6166c = Some (OpImm ALU_ADD 12 11 382, 4%Z).
Proof. vm_refl. Qed.

Definition W_61670 : bv 32 := 0x02700593.
Lemma F_61670 : fetch_word AsanUbsan.M.loaded_segments (0x61670 : word) = Some W_61670.
Proof. vm_refl. Qed.
Lemma D_61670 : decode_any W_61670 = Some (OpImm ALU_ADD 11 0 39, 4%Z).
Proof. vm_refl. Qed.

Definition W_61674 : bv 32 := 0x00000693.
Lemma F_61674 : fetch_word AsanUbsan.M.loaded_segments (0x61674 : word) = Some W_61674.
Proof. vm_refl. Qed.
Lemma D_61674 : decode_any W_61674 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61678 : bv 32 := 0x00000713.
Lemma F_61678 : fetch_word AsanUbsan.M.loaded_segments (0x61678 : word) = Some W_61678.
Proof. vm_refl. Qed.
Lemma D_61678 : decode_any W_61678 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6167c : bv 32 := 0x46d170ef.
Lemma F_6167c : fetch_word AsanUbsan.M.loaded_segments (0x6167c : word) = Some W_6167c.
Proof. vm_refl. Qed.
Lemma D_6167c : decode_any W_6167c = Some (Jal 1 97388, 4%Z).
Proof. vm_refl. Qed.

Definition W_61680 : bv 32 := 0x00075317.
Lemma F_61680 : fetch_word AsanUbsan.M.loaded_segments (0x61680 : word) = Some W_61680.
Proof. vm_refl. Qed.
Lemma D_61680 : decode_any W_61680 = Some (Auipc 6 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_61684 : bv 32 := 0xe8833303.
Lemma F_61684 : fetch_word AsanUbsan.M.loaded_segments (0x61684 : word) = Some W_61684.
Proof. vm_refl. Qed.
Lemma D_61684 : decode_any W_61684 = Some (Load SZ8 true 6 6 3720, 4%Z).
Proof. vm_refl. Qed.

Definition W_61688 : bv 32 := 0xcc0308e3.
Lemma F_61688 : fetch_word AsanUbsan.M.loaded_segments (0x61688 : word) = Some W_61688.
Proof. vm_refl. Qed.
Lemma D_61688 : decode_any W_61688 = Some (Branch BC_EQ 6 0 7376, 4%Z).
Proof. vm_refl. Qed.

Definition W_6168c : bv 32 := 0x00075517.
Lemma F_6168c : fetch_word AsanUbsan.M.loaded_segments (0x6168c : word) = Some W_6168c.
Proof. vm_refl. Qed.
Lemma D_6168c : decode_any W_6168c = Some (Auipc 10 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_61690 : bv 32 := 0xe8453503.
Lemma F_61690 : fetch_word AsanUbsan.M.loaded_segments (0x61690 : word) = Some W_61690.
Proof. vm_refl. Qed.
Lemma D_61690 : decode_any W_61690 = Some (Load SZ8 true 10 10 3716, 4%Z).
Proof. vm_refl. Qed.

Definition W_61694 : bv 32 := 0x00052503.
Lemma F_61694 : fetch_word AsanUbsan.M.loaded_segments (0x61694 : word) = Some W_61694.
Proof. vm_refl. Qed.
Lemma D_61694 : decode_any W_61694 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61698 : bv 32 := 0x04051c63.
Lemma F_61698 : fetch_word AsanUbsan.M.loaded_segments (0x61698 : word) = Some W_61698.
Proof. vm_refl. Qed.
Lemma D_61698 : decode_any W_61698 = Some (Branch BC_NE 10 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_6169c : bv 32 := 0x0000006f.
Lemma F_6169c : fetch_word AsanUbsan.M.loaded_segments (0x6169c : word) = Some W_6169c.
Proof. vm_refl. Qed.
Lemma D_6169c : decode_any W_6169c = Some (Jal 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_616a0 : bv 32 := 0xfffbf517.
Lemma F_616a0 : fetch_word AsanUbsan.M.loaded_segments (0x616a0 : word) = Some W_616a0.
Proof. vm_refl. Qed.
Lemma D_616a0 : decode_any W_616a0 = Some (Auipc 10 1048511, 4%Z).
Proof. vm_refl. Qed.

Definition W_616a4 : bv 32 := 0xfffb2597.
Lemma F_616a4 : fetch_word AsanUbsan.M.loaded_segments (0x616a4 : word) = Some W_616a4.
Proof. vm_refl. Qed.
Lemma D_616a4 : decode_any W_616a4 = Some (Auipc 11 1048498, 4%Z).
Proof. vm_refl. Qed.

Definition W_616a8 : bv 32 := 0x61050513.
Lemma F_616a8 : fetch_word AsanUbsan.M.loaded_segments (0x616a8 : word) = Some W_616a8.
Proof. vm_refl. Qed.
Lemma D_616a8 : decode_any W_616a8 = Some (OpImm ALU_ADD 10 10 1552, 4%Z).
Proof. vm_refl. Qed.

Definition W_616ac : bv 32 := 0xe7d58613.
Lemma F_616ac : fetch_word AsanUbsan.M.loaded_segments (0x616ac : word) = Some W_616ac.
Proof. vm_refl. Qed.
Lemma D_616ac : decode_any W_616ac = Some (OpImm ALU_ADD 12 11 3709, 4%Z).
Proof. vm_refl. Qed.

Definition W_616b0 : bv 32 := 0x03000593.
Lemma F_616b0 : fetch_word AsanUbsan.M.loaded_segments (0x616b0 : word) = Some W_616b0.
Proof. vm_refl. Qed.
Lemma D_616b0 : decode_any W_616b0 = Some (OpImm ALU_ADD 11 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_616b4 : bv 32 := 0x00000693.
Lemma F_616b4 : fetch_word AsanUbsan.M.loaded_segments (0x616b4 : word) = Some W_616b4.
Proof. vm_refl. Qed.
Lemma D_616b4 : decode_any W_616b4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_616b8 : bv 32 := 0x00000713.
Lemma F_616b8 : fetch_word AsanUbsan.M.loaded_segments (0x616b8 : word) = Some W_616b8.
Proof. vm_refl. Qed.
Lemma D_616b8 : decode_any W_616b8 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_616bc : bv 32 := 0x42d170ef.
Lemma F_616bc : fetch_word AsanUbsan.M.loaded_segments (0x616bc : word) = Some W_616bc.
Proof. vm_refl. Qed.
Lemma D_616bc : decode_any W_616bc = Some (Jal 1 97324, 4%Z).
Proof. vm_refl. Qed.

Definition W_616c0 : bv 32 := 0xfffbf517.
Lemma F_616c0 : fetch_word AsanUbsan.M.loaded_segments (0x616c0 : word) = Some W_616c0.
Proof. vm_refl. Qed.
Lemma D_616c0 : decode_any W_616c0 = Some (Auipc 10 1048511, 4%Z).
Proof. vm_refl. Qed.

Definition W_616c4 : bv 32 := 0xfffb8597.
Lemma F_616c4 : fetch_word AsanUbsan.M.loaded_segments (0x616c4 : word) = Some W_616c4.
Proof. vm_refl. Qed.
Lemma D_616c4 : decode_any W_616c4 = Some (Auipc 11 1048504, 4%Z).
Proof. vm_refl. Qed.

Definition W_616c8 : bv 32 := 0x5f050513.
Lemma F_616c8 : fetch_word AsanUbsan.M.loaded_segments (0x616c8 : word) = Some W_616c8.
Proof. vm_refl. Qed.
Lemma D_616c8 : decode_any W_616c8 = Some (OpImm ALU_ADD 10 10 1520, 4%Z).
Proof. vm_refl. Qed.

Definition W_616cc : bv 32 := 0x84058613.
Lemma F_616cc : fetch_word AsanUbsan.M.loaded_segments (0x616cc : word) = Some W_616cc.
Proof. vm_refl. Qed.
Lemma D_616cc : decode_any W_616cc = Some (OpImm ALU_ADD 12 11 2112, 4%Z).
Proof. vm_refl. Qed.

Definition W_616d0 : bv 32 := 0x03200593.
Lemma F_616d0 : fetch_word AsanUbsan.M.loaded_segments (0x616d0 : word) = Some W_616d0.
Proof. vm_refl. Qed.
Lemma D_616d0 : decode_any W_616d0 = Some (OpImm ALU_ADD 11 0 50, 4%Z).
Proof. vm_refl. Qed.

Definition W_616d4 : bv 32 := 0x00000693.
Lemma F_616d4 : fetch_word AsanUbsan.M.loaded_segments (0x616d4 : word) = Some W_616d4.
Proof. vm_refl. Qed.
Lemma D_616d4 : decode_any W_616d4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_616d8 : bv 32 := 0x00000713.
Lemma F_616d8 : fetch_word AsanUbsan.M.loaded_segments (0x616d8 : word) = Some W_616d8.
Proof. vm_refl. Qed.
Lemma D_616d8 : decode_any W_616d8 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_616dc : bv 32 := 0x40d170ef.
Lemma F_616dc : fetch_word AsanUbsan.M.loaded_segments (0x616dc : word) = Some W_616dc.
Proof. vm_refl. Qed.
Lemma D_616dc : decode_any W_616dc = Some (Jal 1 97292, 4%Z).
Proof. vm_refl. Qed.

Definition W_616e0 : bv 32 := 0xfffb1517.
Lemma F_616e0 : fetch_word AsanUbsan.M.loaded_segments (0x616e0 : word) = Some W_616e0.
Proof. vm_refl. Qed.
Lemma D_616e0 : decode_any W_616e0 = Some (Auipc 10 1048497, 4%Z).
Proof. vm_refl. Qed.

Definition W_616e4 : bv 32 := 0x09250513.
Lemma F_616e4 : fetch_word AsanUbsan.M.loaded_segments (0x616e4 : word) = Some W_616e4.
Proof. vm_refl. Qed.
Lemma D_616e4 : decode_any W_616e4 = Some (OpImm ALU_ADD 10 10 146, 4%Z).
Proof. vm_refl. Qed.

Definition W_616e8 : bv 32 := 0x5ad0c0ef.
Lemma F_616e8 : fetch_word AsanUbsan.M.loaded_segments (0x616e8 : word) = Some W_616e8.
Proof. vm_refl. Qed.
Lemma D_616e8 : decode_any W_616e8 = Some (Jal 1 52652, 4%Z).
Proof. vm_refl. Qed.

Definition W_616ec : bv 32 := 0x331170ef.
Lemma F_616ec : fetch_word AsanUbsan.M.loaded_segments (0x616ec : word) = Some W_616ec.
Proof. vm_refl. Qed.
Lemma D_616ec : decode_any W_616ec = Some (Jal 1 97072, 4%Z).
Proof. vm_refl. Qed.

Definition W_616f0 : bv 32 := 0x455190ef.
Lemma F_616f0 : fetch_word AsanUbsan.M.loaded_segments (0x616f0 : word) = Some W_616f0.
Proof. vm_refl. Qed.
Lemma D_616f0 : decode_any W_616f0 = Some (Jal 1 105556, 4%Z).
Proof. vm_refl. Qed.

Definition W_616f4 : bv 32 := 0x00075597.
Lemma F_616f4 : fetch_word AsanUbsan.M.loaded_segments (0x616f4 : word) = Some W_616f4.
Proof. vm_refl. Qed.
Lemma D_616f4 : decode_any W_616f4 = Some (Auipc 11 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_616f8 : bv 32 := 0xdd45b583.
Lemma F_616f8 : fetch_word AsanUbsan.M.loaded_segments (0x616f8 : word) = Some W_616f8.
Proof. vm_refl. Qed.
Lemma D_616f8 : decode_any W_616f8 = Some (Load SZ8 true 11 11 3540, 4%Z).
Proof. vm_refl. Qed.

Definition W_616fc : bv 32 := 0x0005b583.
Lemma F_616fc : fetch_word AsanUbsan.M.loaded_segments (0x616fc : word) = Some W_616fc.
Proof. vm_refl. Qed.
Lemma D_616fc : decode_any W_616fc = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61700 : bv 32 := 0xfff58613.
Lemma F_61700 : fetch_word AsanUbsan.M.loaded_segments (0x61700 : word) = Some W_61700.
Proof. vm_refl. Qed.
Lemma D_61700 : decode_any W_61700 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_61704 : bv 32 := 0x00c5b6b3.
Lemma F_61704 : fetch_word AsanUbsan.M.loaded_segments (0x61704 : word) = Some W_61704.
Proof. vm_refl. Qed.
Lemma D_61704 : decode_any W_61704 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_61708 : bv 32 := 0xfff68693.
Lemma F_61708 : fetch_word AsanUbsan.M.loaded_segments (0x61708 : word) = Some W_61708.
Proof. vm_refl. Qed.
Lemma D_61708 : decode_any W_61708 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6170c : bv 32 := 0x00c6f6b3.
Lemma F_6170c : fetch_word AsanUbsan.M.loaded_segments (0x6170c : word) = Some W_6170c.
Proof. vm_refl. Qed.
Lemma D_6170c : decode_any W_6170c = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_61710 : bv 32 := 0x04a6f263.
Lemma F_61710 : fetch_word AsanUbsan.M.loaded_segments (0x61710 : word) = Some W_61710.
Proof. vm_refl. Qed.
Lemma D_61710 : decode_any W_61710 = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_61714 : bv 32 := 0x00075697.
Lemma F_61714 : fetch_word AsanUbsan.M.loaded_segments (0x61714 : word) = Some W_61714.
Proof. vm_refl. Qed.
Lemma D_61714 : decode_any W_61714 = Some (Auipc 13 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_61718 : bv 32 := 0xdbc6b683.
Lemma F_61718 : fetch_word AsanUbsan.M.loaded_segments (0x61718 : word) = Some W_61718.
Proof. vm_refl. Qed.
Lemma D_61718 : decode_any W_61718 = Some (Load SZ8 true 13 13 3516, 4%Z).
Proof. vm_refl. Qed.

Definition W_6171c : bv 32 := 0x00075717.
Lemma F_6171c : fetch_word AsanUbsan.M.loaded_segments (0x6171c : word) = Some W_6171c.
Proof. vm_refl. Qed.
Lemma D_6171c : decode_any W_6171c = Some (Auipc 14 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_61720 : bv 32 := 0xdbc73703.
Lemma F_61720 : fetch_word AsanUbsan.M.loaded_segments (0x61720 : word) = Some W_61720.
Proof. vm_refl. Qed.
Lemma D_61720 : decode_any W_61720 = Some (Load SZ8 true 14 14 3516, 4%Z).
Proof. vm_refl. Qed.

Definition W_61724 : bv 32 := 0x0006b803.
Lemma F_61724 : fetch_word AsanUbsan.M.loaded_segments (0x61724 : word) = Some W_61724.
Proof. vm_refl. Qed.
Lemma D_61724 : decode_any W_61724 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61728 : bv 32 := 0x00073683.
Lemma F_61728 : fetch_word AsanUbsan.M.loaded_segments (0x61728 : word) = Some W_61728.
Proof. vm_refl. Qed.
Lemma D_61728 : decode_any W_61728 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6172c : bv 32 := 0xfff80793.
Lemma F_6172c : fetch_word AsanUbsan.M.loaded_segments (0x6172c : word) = Some W_6172c.
Proof. vm_refl. Qed.
Lemma D_6172c : decode_any W_6172c = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_61730 : bv 32 := 0x00a7f463.
Lemma F_61730 : fetch_word AsanUbsan.M.loaded_segments (0x61730 : word) = Some W_61730.
Proof. vm_refl. Qed.
Lemma D_61730 : decode_any W_61730 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_61734 : bv 32 := 0x02a6f063.
Lemma F_61734 : fetch_word AsanUbsan.M.loaded_segments (0x61734 : word) = Some W_61734.
Proof. vm_refl. Qed.
Lemma D_61734 : decode_any W_61734 = Some (Branch BC_GEU 13 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_61738 : bv 32 := 0x00075717.
Lemma F_61738 : fetch_word AsanUbsan.M.loaded_segments (0x61738 : word) = Some W_61738.
Proof. vm_refl. Qed.
Lemma D_61738 : decode_any W_61738 = Some (Auipc 14 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_6173c : bv 32 := 0xda873703.
Lemma F_6173c : fetch_word AsanUbsan.M.loaded_segments (0x6173c : word) = Some W_6173c.
Proof. vm_refl. Qed.
Lemma D_6173c : decode_any W_6173c = Some (Load SZ8 true 14 14 3496, 4%Z).
Proof. vm_refl. Qed.

Definition W_61740 : bv 32 := 0x00073283.
Lemma F_61740 : fetch_word AsanUbsan.M.loaded_segments (0x61740 : word) = Some W_61740.
Proof. vm_refl. Qed.
Lemma D_61740 : decode_any W_61740 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61744 : bv 32 := 0x0032d713.
Lemma F_61744 : fetch_word AsanUbsan.M.loaded_segments (0x61744 : word) = Some W_61744.
Proof. vm_refl. Qed.
Lemma D_61744 : decode_any W_61744 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61748 : bv 32 := 0x00b708b3.
Lemma F_61748 : fetch_word AsanUbsan.M.loaded_segments (0x61748 : word) = Some W_61748.
Proof. vm_refl. Qed.
Lemma D_61748 : decode_any W_61748 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6174c : bv 32 := 0x00a2ea63.
Lemma F_6174c : fetch_word AsanUbsan.M.loaded_segments (0x6174c : word) = Some W_6174c.
Proof. vm_refl. Qed.
Lemma D_6174c : decode_any W_6174c = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_61750 : bv 32 := 0x00a8f863.
Lemma F_61750 : fetch_word AsanUbsan.M.loaded_segments (0x61750 : word) = Some W_61750.
Proof. vm_refl. Qed.
Lemma D_61750 : decode_any W_61750 = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_61754 : bv 32 := 0x00355513.
Lemma F_61754 : fetch_word AsanUbsan.M.loaded_segments (0x61754 : word) = Some W_61754.
Proof. vm_refl. Qed.
Lemma D_61754 : decode_any W_61754 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61758 : bv 32 := 0x00a58533.
Lemma F_61758 : fetch_word AsanUbsan.M.loaded_segments (0x61758 : word) = Some W_61758.
Proof. vm_refl. Qed.
Lemma D_61758 : decode_any W_61758 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6175c : bv 32 := 0x00008067.
Lemma F_6175c : fetch_word AsanUbsan.M.loaded_segments (0x6175c : word) = Some W_6175c.
Proof. vm_refl. Qed.
Lemma D_6175c : decode_any W_6175c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61760 : bv 32 := 0x00075297.
Lemma F_61760 : fetch_word AsanUbsan.M.loaded_segments (0x61760 : word) = Some W_61760.
Proof. vm_refl. Qed.
Lemma D_61760 : decode_any W_61760 = Some (Auipc 5 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_61764 : bv 32 := 0xd602b283.
Lemma F_61764 : fetch_word AsanUbsan.M.loaded_segments (0x61764 : word) = Some W_61764.
Proof. vm_refl. Qed.
Lemma D_61764 : decode_any W_61764 = Some (Load SZ8 true 5 5 3424, 4%Z).
Proof. vm_refl. Qed.

Definition W_61768 : bv 32 := 0x04e2c283.
Lemma F_61768 : fetch_word AsanUbsan.M.loaded_segments (0x61768 : word) = Some W_61768.
Proof. vm_refl. Qed.
Lemma D_61768 : decode_any W_61768 = Some (Load SZ1 false 5 5 78, 4%Z).
Proof. vm_refl. Qed.

Definition W_6176c : bv 32 := 0x08029e63.
Lemma F_6176c : fetch_word AsanUbsan.M.loaded_segments (0x6176c : word) = Some W_6176c.
Proof. vm_refl. Qed.
Lemma D_6176c : decode_any W_6176c = Some (Branch BC_NE 5 0 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_61770 : bv 32 := 0x04080063.
Lemma F_61770 : fetch_word AsanUbsan.M.loaded_segments (0x61770 : word) = Some W_61770.
Proof. vm_refl. Qed.
Lemma D_61770 : decode_any W_61770 = Some (Branch BC_EQ 16 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_61774 : bv 32 := 0x00385813.
Lemma F_61774 : fetch_word AsanUbsan.M.loaded_segments (0x61774 : word) = Some W_61774.
Proof. vm_refl. Qed.
Lemma D_61774 : decode_any W_61774 = Some (ShiftImm ALU_SRL 16 16 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61778 : bv 32 := 0x00c80833.
Lemma F_61778 : fetch_word AsanUbsan.M.loaded_segments (0x61778 : word) = Some W_61778.
Proof. vm_refl. Qed.
Lemma D_61778 : decode_any W_61778 = Some (Op ALU_ADD 16 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6177c : bv 32 := 0x06a87063.
Lemma F_6177c : fetch_word AsanUbsan.M.loaded_segments (0x6177c : word) = Some W_6177c.
Proof. vm_refl. Qed.
Lemma D_6177c : decode_any W_6177c = Some (Branch BC_GEU 16 10 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_61780 : bv 32 := 0x00158813.
Lemma F_61780 : fetch_word AsanUbsan.M.loaded_segments (0x61780 : word) = Some W_61780.
Proof. vm_refl. Qed.
Lemma D_61780 : decode_any W_61780 = Some (OpImm ALU_ADD 16 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61784 : bv 32 := 0x00a7e863.
Lemma F_61784 : fetch_word AsanUbsan.M.loaded_segments (0x61784 : word) = Some W_61784.
Proof. vm_refl. Qed.
Lemma D_61784 : decode_any W_61784 = Some (Branch BC_LTU 15 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_61788 : bv 32 := 0x0036d793.
Lemma F_61788 : fetch_word AsanUbsan.M.loaded_segments (0x61788 : word) = Some W_61788.
Proof. vm_refl. Qed.
Lemma D_61788 : decode_any W_61788 = Some (ShiftImm ALU_SRL 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6178c : bv 32 := 0x010787b3.
Lemma F_6178c : fetch_word AsanUbsan.M.loaded_segments (0x6178c : word) = Some W_6178c.
Proof. vm_refl. Qed.
Lemma D_6178c : decode_any W_6178c = Some (Op ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_61790 : bv 32 := 0xfcf572e3.
Lemma F_61790 : fetch_word AsanUbsan.M.loaded_segments (0x61790 : word) = Some W_61790.
Proof. vm_refl. Qed.
Lemma D_61790 : decode_any W_61790 = Some (Branch BC_GEU 10 15 8132, 4%Z).
Proof. vm_refl. Qed.

Definition W_61794 : bv 32 := 0x00168693.
Lemma F_61794 : fetch_word AsanUbsan.M.loaded_segments (0x61794 : word) = Some W_61794.
Proof. vm_refl. Qed.
Lemma D_61794 : decode_any W_61794 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61798 : bv 32 := 0x06d56863.
Lemma F_61798 : fetch_word AsanUbsan.M.loaded_segments (0x61798 : word) = Some W_61798.
Proof. vm_refl. Qed.
Lemma D_61798 : decode_any W_61798 = Some (Branch BC_LTU 10 13 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_6179c : bv 32 := 0x01070733.
Lemma F_6179c : fetch_word AsanUbsan.M.loaded_segments (0x6179c : word) = Some W_6179c.
Proof. vm_refl. Qed.
Lemma D_6179c : decode_any W_6179c = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_617a0 : bv 32 := 0x00375713.
Lemma F_617a0 : fetch_word AsanUbsan.M.loaded_segments (0x617a0 : word) = Some W_617a0.
Proof. vm_refl. Qed.
Lemma D_617a0 : decode_any W_617a0 = Some (ShiftImm ALU_SRL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_617a4 : bv 32 := 0x00c70633.
Lemma F_617a4 : fetch_word AsanUbsan.M.loaded_segments (0x617a4 : word) = Some W_617a4.
Proof. vm_refl. Qed.
Lemma D_617a4 : decode_any W_617a4 = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_617a8 : bv 32 := 0xfaa676e3.
Lemma F_617a8 : fetch_word AsanUbsan.M.loaded_segments (0x617a8 : word) = Some W_617a8.
Proof. vm_refl. Qed.
Lemma D_617a8 : decode_any W_617a8 = Some (Branch BC_GEU 12 10 8108, 4%Z).
Proof. vm_refl. Qed.

Definition W_617ac : bv 32 := 0x05c0006f.
Lemma F_617ac : fetch_word AsanUbsan.M.loaded_segments (0x617ac : word) = Some W_617ac.
Proof. vm_refl. Qed.
Lemma D_617ac : decode_any W_617ac = Some (Jal 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_617b0 : bv 32 := 0x04058463.
Lemma F_617b0 : fetch_word AsanUbsan.M.loaded_segments (0x617b0 : word) = Some W_617b0.
Proof. vm_refl. Qed.
Lemma D_617b0 : decode_any W_617b0 = Some (Branch BC_EQ 11 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_617b4 : bv 32 := 0x00365693.
Lemma F_617b4 : fetch_word AsanUbsan.M.loaded_segments (0x617b4 : word) = Some W_617b4.
Proof. vm_refl. Qed.
Lemma D_617b4 : decode_any W_617b4 = Some (ShiftImm ALU_SRL 13 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_617b8 : bv 32 := 0x00b686b3.
Lemma F_617b8 : fetch_word AsanUbsan.M.loaded_segments (0x617b8 : word) = Some W_617b8.
Proof. vm_refl. Qed.
Lemma D_617b8 : decode_any W_617b8 = Some (Op ALU_ADD 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_617bc : bv 32 := 0x00068663.
Lemma F_617bc : fetch_word AsanUbsan.M.loaded_segments (0x617bc : word) = Some W_617bc.
Proof. vm_refl. Qed.
Lemma D_617bc : decode_any W_617bc = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_617c0 : bv 32 := 0x00168693.
Lemma F_617c0 : fetch_word AsanUbsan.M.loaded_segments (0x617c0 : word) = Some W_617c0.
Proof. vm_refl. Qed.
Lemma D_617c0 : decode_any W_617c0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_617c4 : bv 32 := 0x04d56263.
Lemma F_617c4 : fetch_word AsanUbsan.M.loaded_segments (0x617c4 : word) = Some W_617c4.
Proof. vm_refl. Qed.
Lemma D_617c4 : decode_any W_617c4 = Some (Branch BC_LTU 10 13 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_617c8 : bv 32 := 0x00188893.
Lemma F_617c8 : fetch_word AsanUbsan.M.loaded_segments (0x617c8 : word) = Some W_617c8.
Proof. vm_refl. Qed.
Lemma D_617c8 : decode_any W_617c8 = Some (OpImm ALU_ADD 17 17 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_617cc : bv 32 := 0x0038d693.
Lemma F_617cc : fetch_word AsanUbsan.M.loaded_segments (0x617cc : word) = Some W_617cc.
Proof. vm_refl. Qed.
Lemma D_617cc : decode_any W_617cc = Some (ShiftImm ALU_SRL 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_617d0 : bv 32 := 0x00c68633.
Lemma F_617d0 : fetch_word AsanUbsan.M.loaded_segments (0x617d0 : word) = Some W_617d0.
Proof. vm_refl. Qed.
Lemma D_617d0 : decode_any W_617d0 = Some (Op ALU_ADD 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_617d4 : bv 32 := 0xf8a670e3.
Lemma F_617d4 : fetch_word AsanUbsan.M.loaded_segments (0x617d4 : word) = Some W_617d4.
Proof. vm_refl. Qed.
Lemma D_617d4 : decode_any W_617d4 = Some (Branch BC_GEU 12 10 8064, 4%Z).
Proof. vm_refl. Qed.

Definition W_617d8 : bv 32 := 0x0300006f.
Lemma F_617d8 : fetch_word AsanUbsan.M.loaded_segments (0x617d8 : word) = Some W_617d8.
Proof. vm_refl. Qed.
Lemma D_617d8 : decode_any W_617d8 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_617dc : bv 32 := 0xf6058ce3.
Lemma F_617dc : fetch_word AsanUbsan.M.loaded_segments (0x617dc : word) = Some W_617dc.
Proof. vm_refl. Qed.
Lemma D_617dc : decode_any W_617dc = Some (Branch BC_EQ 11 0 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_617e0 : bv 32 := 0x00365613.
Lemma F_617e0 : fetch_word AsanUbsan.M.loaded_segments (0x617e0 : word) = Some W_617e0.
Proof. vm_refl. Qed.
Lemma D_617e0 : decode_any W_617e0 = Some (ShiftImm ALU_SRL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_617e4 : bv 32 := 0x00b60633.
Lemma F_617e4 : fetch_word AsanUbsan.M.loaded_segments (0x617e4 : word) = Some W_617e4.
Proof. vm_refl. Qed.
Lemma D_617e4 : decode_any W_617e4 = Some (Op ALU_ADD 12 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_617e8 : bv 32 := 0xf60606e3.
Lemma F_617e8 : fetch_word AsanUbsan.M.loaded_segments (0x617e8 : word) = Some W_617e8.
Proof. vm_refl. Qed.
Lemma D_617e8 : decode_any W_617e8 = Some (Branch BC_EQ 12 0 8044, 4%Z).
Proof. vm_refl. Qed.

Definition W_617ec : bv 32 := 0x00160613.
Lemma F_617ec : fetch_word AsanUbsan.M.loaded_segments (0x617ec : word) = Some W_617ec.
Proof. vm_refl. Qed.
Lemma D_617ec : decode_any W_617ec = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_617f0 : bv 32 := 0xf6c572e3.
Lemma F_617f0 : fetch_word AsanUbsan.M.loaded_segments (0x617f0 : word) = Some W_617f0.
Proof. vm_refl. Qed.
Lemma D_617f0 : decode_any W_617f0 = Some (Branch BC_GEU 10 12 8036, 4%Z).
Proof. vm_refl. Qed.

Definition W_617f4 : bv 32 := 0x0140006f.
Lemma F_617f4 : fetch_word AsanUbsan.M.loaded_segments (0x617f4 : word) = Some W_617f4.
Proof. vm_refl. Qed.
Lemma D_617f4 : decode_any W_617f4 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_617f8 : bv 32 := 0x00170713.
Lemma F_617f8 : fetch_word AsanUbsan.M.loaded_segments (0x617f8 : word) = Some W_617f8.
Proof. vm_refl. Qed.
Lemma D_617f8 : decode_any W_617f8 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_617fc : bv 32 := 0x00375713.
Lemma F_617fc : fetch_word AsanUbsan.M.loaded_segments (0x617fc : word) = Some W_617fc.
Proof. vm_refl. Qed.
Lemma D_617fc : decode_any W_617fc = Some (ShiftImm ALU_SRL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61800 : bv 32 := 0xfff70713.
Lemma F_61800 : fetch_word AsanUbsan.M.loaded_segments (0x61800 : word) = Some W_61800.
Proof. vm_refl. Qed.
Lemma D_61800 : decode_any W_61800 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_61804 : bv 32 := 0xf4a778e3.
Lemma F_61804 : fetch_word AsanUbsan.M.loaded_segments (0x61804 : word) = Some W_61804.
Proof. vm_refl. Qed.
Lemma D_61804 : decode_any W_61804 = Some (Branch BC_GEU 14 10 8016, 4%Z).
Proof. vm_refl. Qed.

Definition W_61808 : bv 32 := 0xff010113.
Lemma F_61808 : fetch_word AsanUbsan.M.loaded_segments (0x61808 : word) = Some W_61808.
Proof. vm_refl. Qed.
Lemma D_61808 : decode_any W_61808 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_6180c : bv 32 := 0x00113423.
Lemma F_6180c : fetch_word AsanUbsan.M.loaded_segments (0x6180c : word) = Some W_6180c.
Proof. vm_refl. Qed.
Lemma D_6180c : decode_any W_6180c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_61810 : bv 32 := 0xfffc0517.
Lemma F_61810 : fetch_word AsanUbsan.M.loaded_segments (0x61810 : word) = Some W_61810.
Proof. vm_refl. Qed.
Lemma D_61810 : decode_any W_61810 = Some (Auipc 10 1048512, 4%Z).
Proof. vm_refl. Qed.

Definition W_61814 : bv 32 := 0xfffb6597.
Lemma F_61814 : fetch_word AsanUbsan.M.loaded_segments (0x61814 : word) = Some W_61814.
Proof. vm_refl. Qed.
Lemma D_61814 : decode_any W_61814 = Some (Auipc 11 1048502, 4%Z).
Proof. vm_refl. Qed.

Definition W_61818 : bv 32 := 0xb8a50513.
Lemma F_61818 : fetch_word AsanUbsan.M.loaded_segments (0x61818 : word) = Some W_61818.
Proof. vm_refl. Qed.
Lemma D_61818 : decode_any W_61818 = Some (OpImm ALU_ADD 10 10 2954, 4%Z).
Proof. vm_refl. Qed.

Definition W_6181c : bv 32 := 0x04c58613.
Lemma F_6181c : fetch_word AsanUbsan.M.loaded_segments (0x6181c : word) = Some W_6181c.
Proof. vm_refl. Qed.
Lemma D_6181c : decode_any W_6181c = Some (OpImm ALU_ADD 12 11 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_61820 : bv 32 := 0x17700593.
Lemma F_61820 : fetch_word AsanUbsan.M.loaded_segments (0x61820 : word) = Some W_61820.
Proof. vm_refl. Qed.
Lemma D_61820 : decode_any W_61820 = Some (OpImm ALU_ADD 11 0 375, 4%Z).
Proof. vm_refl. Qed.

Definition W_61824 : bv 32 := 0x00000693.
Lemma F_61824 : fetch_word AsanUbsan.M.loaded_segments (0x61824 : word) = Some W_61824.
Proof. vm_refl. Qed.
Lemma D_61824 : decode_any W_61824 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61828 : bv 32 := 0x00000713.
Lemma F_61828 : fetch_word AsanUbsan.M.loaded_segments (0x61828 : word) = Some W_61828.
Proof. vm_refl. Qed.
Lemma D_61828 : decode_any W_61828 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6182c : bv 32 := 0x2bd170ef.
Lemma F_6182c : fetch_word AsanUbsan.M.loaded_segments (0x6182c : word) = Some W_6182c.
Proof. vm_refl. Qed.
Lemma D_6182c : decode_any W_6182c = Some (Jal 1 96956, 4%Z).
Proof. vm_refl. Qed.
