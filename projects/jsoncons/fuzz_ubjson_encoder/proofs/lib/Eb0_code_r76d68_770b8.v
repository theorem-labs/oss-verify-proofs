(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_92170 : bv 32 := 0xf7010113.
Lemma F_92170 : fetch_word AsanUbsan.M.loaded_segments (0x921c0 : word) = Some W_92170.
Proof. vm_refl. Qed.
Lemma D_92170 : decode_any W_92170 = Some (OpImm ALU_ADD 2 2 3952, 4%Z).
Proof. vm_refl. Qed.

Definition W_92174 : bv 32 := 0x08113423.
Lemma F_92174 : fetch_word AsanUbsan.M.loaded_segments (0x921c4 : word) = Some W_92174.
Proof. vm_refl. Qed.
Lemma D_92174 : decode_any W_92174 = Some (Store SZ8 2 1 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_92178 : bv 32 := 0x08813023.
Lemma F_92178 : fetch_word AsanUbsan.M.loaded_segments (0x921c8 : word) = Some W_92178.
Proof. vm_refl. Qed.
Lemma D_92178 : decode_any W_92178 = Some (Store SZ8 2 8 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_9217c : bv 32 := 0x06913c23.
Lemma F_9217c : fetch_word AsanUbsan.M.loaded_segments (0x921cc : word) = Some W_9217c.
Proof. vm_refl. Qed.
Lemma D_9217c : decode_any W_9217c = Some (Store SZ8 2 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_92180 : bv 32 := 0x07213823.
Lemma F_92180 : fetch_word AsanUbsan.M.loaded_segments (0x921d0 : word) = Some W_92180.
Proof. vm_refl. Qed.
Lemma D_92180 : decode_any W_92180 = Some (Store SZ8 2 18 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_92184 : bv 32 := 0x07313423.
Lemma F_92184 : fetch_word AsanUbsan.M.loaded_segments (0x921d4 : word) = Some W_92184.
Proof. vm_refl. Qed.
Lemma D_92184 : decode_any W_92184 = Some (Store SZ8 2 19 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_92188 : bv 32 := 0x07413023.
Lemma F_92188 : fetch_word AsanUbsan.M.loaded_segments (0x921d8 : word) = Some W_92188.
Proof. vm_refl. Qed.
Lemma D_92188 : decode_any W_92188 = Some (Store SZ8 2 20 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_9218c : bv 32 := 0x05513c23.
Lemma F_9218c : fetch_word AsanUbsan.M.loaded_segments (0x921dc : word) = Some W_9218c.
Proof. vm_refl. Qed.
Lemma D_9218c : decode_any W_9218c = Some (Store SZ8 2 21 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_92190 : bv 32 := 0x05613823.
Lemma F_92190 : fetch_word AsanUbsan.M.loaded_segments (0x921e0 : word) = Some W_92190.
Proof. vm_refl. Qed.
Lemma D_92190 : decode_any W_92190 = Some (Store SZ8 2 22 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_92194 : bv 32 := 0x05713423.
Lemma F_92194 : fetch_word AsanUbsan.M.loaded_segments (0x921e4 : word) = Some W_92194.
Proof. vm_refl. Qed.
Lemma D_92194 : decode_any W_92194 = Some (Store SZ8 2 23 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_92198 : bv 32 := 0x05813023.
Lemma F_92198 : fetch_word AsanUbsan.M.loaded_segments (0x921e8 : word) = Some W_92198.
Proof. vm_refl. Qed.
Lemma D_92198 : decode_any W_92198 = Some (Store SZ8 2 24 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_9219c : bv 32 := 0x03913c23.
Lemma F_9219c : fetch_word AsanUbsan.M.loaded_segments (0x921ec : word) = Some W_9219c.
Proof. vm_refl. Qed.
Lemma D_9219c : decode_any W_9219c = Some (Store SZ8 2 25 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_921a0 : bv 32 := 0x03a13823.
Lemma F_921a0 : fetch_word AsanUbsan.M.loaded_segments (0x921f0 : word) = Some W_921a0.
Proof. vm_refl. Qed.
Lemma D_921a0 : decode_any W_921a0 = Some (Store SZ8 2 26 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_921a4 : bv 32 := 0x03b13423.
Lemma F_921a4 : fetch_word AsanUbsan.M.loaded_segments (0x921f4 : word) = Some W_921a4.
Proof. vm_refl. Qed.
Lemma D_921a4 : decode_any W_921a4 = Some (Store SZ8 2 27 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_921a8 : bv 32 := 0x00058913.
Lemma F_921a8 : fetch_word AsanUbsan.M.loaded_segments (0x921f8 : word) = Some W_921a8.
Proof. vm_refl. Qed.
Lemma D_921a8 : decode_any W_921a8 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_921ac : bv 32 := 0x000ab597.
Lemma F_921ac : fetch_word AsanUbsan.M.loaded_segments (0x921fc : word) = Some W_921ac.
Proof. vm_refl. Qed.
Lemma D_921ac : decode_any W_921ac = Some (Auipc 11 171, 4%Z).
Proof. vm_refl. Qed.

Definition W_921b0 : bv 32 := 0x6bc5b583.
Lemma F_921b0 : fetch_word AsanUbsan.M.loaded_segments (0x92200 : word) = Some W_921b0.
Proof. vm_refl. Qed.
Lemma D_921b0 : decode_any W_921b0 = Some (Load SZ8 true 11 11 1724, 4%Z).
Proof. vm_refl. Qed.

Definition W_921b4 : bv 32 := 0x0895c583.
Lemma F_921b4 : fetch_word AsanUbsan.M.loaded_segments (0x92204 : word) = Some W_921b4.
Proof. vm_refl. Qed.
Lemma D_921b4 : decode_any W_921b4 = Some (Load SZ1 false 11 11 137, 4%Z).
Proof. vm_refl. Qed.

Definition W_921b8 : bv 32 := 0x18058a63.
Lemma F_921b8 : fetch_word AsanUbsan.M.loaded_segments (0x92208 : word) = Some W_921b8.
Proof. vm_refl. Qed.
Lemma D_921b8 : decode_any W_921b8 = Some (Branch BC_EQ 11 0 404, 4%Z).
Proof. vm_refl. Qed.

Definition W_921bc : bv 32 := 0x00050993.
Lemma F_921bc : fetch_word AsanUbsan.M.loaded_segments (0x9220c : word) = Some W_921bc.
Proof. vm_refl. Qed.
Lemma D_921bc : decode_any W_921bc = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_921c0 : bv 32 := 0x000ab517.
Lemma F_921c0 : fetch_word AsanUbsan.M.loaded_segments (0x92210 : word) = Some W_921c0.
Proof. vm_refl. Qed.
Lemma D_921c0 : decode_any W_921c0 = Some (Auipc 10 171, 4%Z).
Proof. vm_refl. Qed.

Definition W_921c4 : bv 32 := 0x70853d03.
Lemma F_921c4 : fetch_word AsanUbsan.M.loaded_segments (0x92214 : word) = Some W_921c4.
Proof. vm_refl. Qed.
Lemma D_921c4 : decode_any W_921c4 = Some (Load SZ8 true 26 10 1800, 4%Z).
Proof. vm_refl. Qed.

Definition W_921c8 : bv 32 := 0x0009ba03.
Lemma F_921c8 : fetch_word AsanUbsan.M.loaded_segments (0x92218 : word) = Some W_921c8.
Proof. vm_refl. Qed.
Lemma D_921c8 : decode_any W_921c8 = Some (Load SZ8 true 20 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_921cc : bv 32 := 0x000ac517.
Lemma F_921cc : fetch_word AsanUbsan.M.loaded_segments (0x9221c : word) = Some W_921cc.
Proof. vm_refl. Qed.
Lemma D_921cc : decode_any W_921cc = Some (Auipc 10 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_921d0 : bv 32 := 0x000d2583.
Lemma F_921d0 : fetch_word AsanUbsan.M.loaded_segments (0x92220 : word) = Some W_921d0.
Proof. vm_refl. Qed.
Lemma D_921d0 : decode_any W_921d0 = Some (Load SZ4 true 11 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_921d4 : bv 32 := 0x4b453a83.
Lemma F_921d4 : fetch_word AsanUbsan.M.loaded_segments (0x92224 : word) = Some W_921d4.
Proof. vm_refl. Qed.
Lemma D_921d4 : decode_any W_921d4 = Some (Load SZ8 true 21 10 1204, 4%Z).
Proof. vm_refl. Qed.

Definition W_921d8 : bv 32 := 0x00300513.
Lemma F_921d8 : fetch_word AsanUbsan.M.loaded_segments (0x92228 : word) = Some W_921d8.
Proof. vm_refl. Qed.
Lemma D_921d8 : decode_any W_921d8 = Some (OpImm ALU_ADD 10 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_921dc : bv 32 := 0x004a8ab3.
Lemma F_921dc : fetch_word AsanUbsan.M.loaded_segments (0x9222c : word) = Some W_921dc.
Proof. vm_refl. Qed.
Lemma D_921dc : decode_any W_921dc = Some (Op ALU_ADD 21 21 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_921e0 : bv 32 := 0x1ea5fa63.
Lemma F_921e0 : fetch_word AsanUbsan.M.loaded_segments (0x92230 : word) = Some W_921e0.
Proof. vm_refl. Qed.
Lemma D_921e0 : decode_any W_921e0 = Some (Branch BC_GEU 11 10 500, 4%Z).
Proof. vm_refl. Qed.

Definition W_921e4 : bv 32 := 0x000abb03.
Lemma F_921e4 : fetch_word AsanUbsan.M.loaded_segments (0x92234 : word) = Some W_921e4.
Proof. vm_refl. Qed.
Lemma D_921e4 : decode_any W_921e4 = Some (Load SZ8 true 22 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_921e8 : bv 32 := 0xfff00513.
Lemma F_921e8 : fetch_word AsanUbsan.M.loaded_segments (0x92238 : word) = Some W_921e8.
Proof. vm_refl. Qed.
Lemma D_921e8 : decode_any W_921e8 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_921ec : bv 32 := 0x0230000f.
Lemma F_921ec : fetch_word AsanUbsan.M.loaded_segments (0x9223c : word) = Some W_921ec.
Proof. vm_refl. Qed.
Lemma D_921ec : decode_any W_921ec = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_921f0 : bv 32 := 0x14ab0e63.
Lemma F_921f0 : fetch_word AsanUbsan.M.loaded_segments (0x92240 : word) = Some W_921f0.
Proof. vm_refl. Qed.
Lemma D_921f0 : decode_any W_921f0 = Some (Branch BC_EQ 22 10 348, 4%Z).
Proof. vm_refl. Qed.

Definition W_921f4 : bv 32 := 0x080b1263.
Lemma F_921f4 : fetch_word AsanUbsan.M.loaded_segments (0x92244 : word) = Some W_921f4.
Proof. vm_refl. Qed.
Lemma D_921f4 : decode_any W_921f4 = Some (Branch BC_NE 22 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_92278 : bv 32 := 0x0c0b0a63.
Lemma F_92278 : fetch_word AsanUbsan.M.loaded_segments (0x922c8 : word) = Some W_92278.
Proof. vm_refl. Qed.
Lemma D_92278 : decode_any W_92278 = Some (Branch BC_EQ 22 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_9227c : bv 32 := 0x00c13823.
Lemma F_9227c : fetch_word AsanUbsan.M.loaded_segments (0x922cc : word) = Some W_9227c.
Proof. vm_refl. Qed.
Lemma D_9227c : decode_any W_9227c = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_92280 : bv 32 := 0x00d13c23.
Lemma F_92280 : fetch_word AsanUbsan.M.loaded_segments (0x922d0 : word) = Some W_92280.
Proof. vm_refl. Qed.
Lemma D_92280 : decode_any W_92280 = Some (Store SZ8 2 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_92284 : bv 32 := 0x0ff00513.
Lemma F_92284 : fetch_word AsanUbsan.M.loaded_segments (0x922d4 : word) = Some W_92284.
Proof. vm_refl. Qed.
Lemma D_92284 : decode_any W_92284 = Some (OpImm ALU_ADD 10 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_92288 : bv 32 := 0x0aaa6863.
Lemma F_92288 : fetch_word AsanUbsan.M.loaded_segments (0x922d8 : word) = Some W_92288.
Proof. vm_refl. Qed.
Lemma D_92288 : decode_any W_92288 = Some (Branch BC_LTU 20 10 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_92338 : bv 32 := 0x000b0513.
Lemma F_92338 : fetch_word AsanUbsan.M.loaded_segments (0x92388 : word) = Some W_92338.
Proof. vm_refl. Qed.
Lemma D_92338 : decode_any W_92338 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9233c : bv 32 := 0x004a1413.
Lemma F_9233c : fetch_word AsanUbsan.M.loaded_segments (0x9238c : word) = Some W_9233c.
Proof. vm_refl. Qed.
Lemma D_9233c : decode_any W_9233c = Some (ShiftImm ALU_SLL 8 20 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_92340 : bv 32 := 0x00850433.
Lemma F_92340 : fetch_word AsanUbsan.M.loaded_segments (0x92390 : word) = Some W_92340.
Proof. vm_refl. Qed.
Lemma D_92340 : decode_any W_92340 = Some (Op ALU_ADD 8 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_92344 : bv 32 := 0x00843503.
Lemma F_92344 : fetch_word AsanUbsan.M.loaded_segments (0x92394 : word) = Some W_92344.
Proof. vm_refl. Qed.
Lemma D_92344 : decode_any W_92344 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_92348 : bv 32 := 0x04050263.
Lemma F_92348 : fetch_word AsanUbsan.M.loaded_segments (0x92398 : word) = Some W_92348.
Proof. vm_refl. Qed.
Lemma D_92348 : decode_any W_92348 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_9234c : bv 32 := 0x00000513.
Lemma F_9234c : fetch_word AsanUbsan.M.loaded_segments (0x9239c : word) = Some W_9234c.
Proof. vm_refl. Qed.
Lemma D_9234c : decode_any W_9234c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92350 : bv 32 := 0x08813083.
Lemma F_92350 : fetch_word AsanUbsan.M.loaded_segments (0x923a0 : word) = Some W_92350.
Proof. vm_refl. Qed.
Lemma D_92350 : decode_any W_92350 = Some (Load SZ8 true 1 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_92354 : bv 32 := 0x08013403.
Lemma F_92354 : fetch_word AsanUbsan.M.loaded_segments (0x923a4 : word) = Some W_92354.
Proof. vm_refl. Qed.
Lemma D_92354 : decode_any W_92354 = Some (Load SZ8 true 8 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_92358 : bv 32 := 0x07813483.
Lemma F_92358 : fetch_word AsanUbsan.M.loaded_segments (0x923a8 : word) = Some W_92358.
Proof. vm_refl. Qed.
Lemma D_92358 : decode_any W_92358 = Some (Load SZ8 true 9 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_9235c : bv 32 := 0x07013903.
Lemma F_9235c : fetch_word AsanUbsan.M.loaded_segments (0x923ac : word) = Some W_9235c.
Proof. vm_refl. Qed.
Lemma D_9235c : decode_any W_9235c = Some (Load SZ8 true 18 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_92360 : bv 32 := 0x06813983.
Lemma F_92360 : fetch_word AsanUbsan.M.loaded_segments (0x923b0 : word) = Some W_92360.
Proof. vm_refl. Qed.
Lemma D_92360 : decode_any W_92360 = Some (Load SZ8 true 19 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_92364 : bv 32 := 0x06013a03.
Lemma F_92364 : fetch_word AsanUbsan.M.loaded_segments (0x923b4 : word) = Some W_92364.
Proof. vm_refl. Qed.
Lemma D_92364 : decode_any W_92364 = Some (Load SZ8 true 20 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_92368 : bv 32 := 0x05813a83.
Lemma F_92368 : fetch_word AsanUbsan.M.loaded_segments (0x923b8 : word) = Some W_92368.
Proof. vm_refl. Qed.
Lemma D_92368 : decode_any W_92368 = Some (Load SZ8 true 21 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_9236c : bv 32 := 0x05013b03.
Lemma F_9236c : fetch_word AsanUbsan.M.loaded_segments (0x923bc : word) = Some W_9236c.
Proof. vm_refl. Qed.
Lemma D_9236c : decode_any W_9236c = Some (Load SZ8 true 22 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_92370 : bv 32 := 0x04813b83.
Lemma F_92370 : fetch_word AsanUbsan.M.loaded_segments (0x923c0 : word) = Some W_92370.
Proof. vm_refl. Qed.
Lemma D_92370 : decode_any W_92370 = Some (Load SZ8 true 23 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_92374 : bv 32 := 0x04013c03.
Lemma F_92374 : fetch_word AsanUbsan.M.loaded_segments (0x923c4 : word) = Some W_92374.
Proof. vm_refl. Qed.
Lemma D_92374 : decode_any W_92374 = Some (Load SZ8 true 24 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_92378 : bv 32 := 0x03813c83.
Lemma F_92378 : fetch_word AsanUbsan.M.loaded_segments (0x923c8 : word) = Some W_92378.
Proof. vm_refl. Qed.
Lemma D_92378 : decode_any W_92378 = Some (Load SZ8 true 25 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_9237c : bv 32 := 0x03013d03.
Lemma F_9237c : fetch_word AsanUbsan.M.loaded_segments (0x923cc : word) = Some W_9237c.
Proof. vm_refl. Qed.
Lemma D_9237c : decode_any W_9237c = Some (Load SZ8 true 26 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_92380 : bv 32 := 0x02813d83.
Lemma F_92380 : fetch_word AsanUbsan.M.loaded_segments (0x923d0 : word) = Some W_92380.
Proof. vm_refl. Qed.
Lemma D_92380 : decode_any W_92380 = Some (Load SZ8 true 27 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_92384 : bv 32 := 0x09010113.
Lemma F_92384 : fetch_word AsanUbsan.M.loaded_segments (0x923d4 : word) = Some W_92384.
Proof. vm_refl. Qed.
Lemma D_92384 : decode_any W_92384 = Some (OpImm ALU_ADD 2 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_92388 : bv 32 := 0x00008067.
Lemma F_92388 : fetch_word AsanUbsan.M.loaded_segments (0x923d8 : word) = Some W_92388.
Proof. vm_refl. Qed.
Lemma D_92388 : decode_any W_92388 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
