(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_6c1a0 : bv 32 := 0x0e40006f.
Lemma F_6c1a0 : fetch_word AsanUbsan.M.loaded_segments (0x6c1e8 : word) = Some W_6c1a0.
Proof. vm_refl. Qed.
Lemma D_6c1a0 : decode_any W_6c1a0 = Some (Jal 0 228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c1c4 : bv 32 := 0x1dc0206f.
Lemma F_6c1c4 : fetch_word AsanUbsan.M.loaded_segments (0x6c20c : word) = Some W_6c1c4.
Proof. vm_refl. Qed.
Lemma D_6c1c4 : decode_any W_6c1c4 = Some (Jal 0 8668, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c224 : bv 32 := 0x4a50706f.
Lemma F_6c224 : fetch_word AsanUbsan.M.loaded_segments (0x6c26c : word) = Some W_6c224.
Proof. vm_refl. Qed.
Lemma D_6c224 : decode_any W_6c224 = Some (Jal 0 31908, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c284 : bv 32 := 0x81010113.
Lemma F_6c284 : fetch_word AsanUbsan.M.loaded_segments (0x6c2cc : word) = Some W_6c284.
Proof. vm_refl. Qed.
Lemma D_6c284 : decode_any W_6c284 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c288 : bv 32 := 0x7e113423.
Lemma F_6c288 : fetch_word AsanUbsan.M.loaded_segments (0x6c2d0 : word) = Some W_6c288.
Proof. vm_refl. Qed.
Lemma D_6c288 : decode_any W_6c288 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c28c : bv 32 := 0x7e813023.
Lemma F_6c28c : fetch_word AsanUbsan.M.loaded_segments (0x6c2d4 : word) = Some W_6c28c.
Proof. vm_refl. Qed.
Lemma D_6c28c : decode_any W_6c28c = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c290 : bv 32 := 0x7c913c23.
Lemma F_6c290 : fetch_word AsanUbsan.M.loaded_segments (0x6c2d8 : word) = Some W_6c290.
Proof. vm_refl. Qed.
Lemma D_6c290 : decode_any W_6c290 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c294 : bv 32 := 0x7d213823.
Lemma F_6c294 : fetch_word AsanUbsan.M.loaded_segments (0x6c2dc : word) = Some W_6c294.
Proof. vm_refl. Qed.
Lemma D_6c294 : decode_any W_6c294 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c298 : bv 32 := 0x7d313423.
Lemma F_6c298 : fetch_word AsanUbsan.M.loaded_segments (0x6c2e0 : word) = Some W_6c298.
Proof. vm_refl. Qed.
Lemma D_6c298 : decode_any W_6c298 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c29c : bv 32 := 0x7d413023.
Lemma F_6c29c : fetch_word AsanUbsan.M.loaded_segments (0x6c2e4 : word) = Some W_6c29c.
Proof. vm_refl. Qed.
Lemma D_6c29c : decode_any W_6c29c = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c2a0 : bv 32 := 0x7b513c23.
Lemma F_6c2a0 : fetch_word AsanUbsan.M.loaded_segments (0x6c2e8 : word) = Some W_6c2a0.
Proof. vm_refl. Qed.
Lemma D_6c2a0 : decode_any W_6c2a0 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c2a4 : bv 32 := 0x7b613823.
Lemma F_6c2a4 : fetch_word AsanUbsan.M.loaded_segments (0x6c2ec : word) = Some W_6c2a4.
Proof. vm_refl. Qed.
Lemma D_6c2a4 : decode_any W_6c2a4 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c2a8 : bv 32 := 0x7f010413.
Lemma F_6c2a8 : fetch_word AsanUbsan.M.loaded_segments (0x6c2f0 : word) = Some W_6c2a8.
Proof. vm_refl. Qed.
Lemma D_6c2a8 : decode_any W_6c2a8 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c2ac : bv 32 := 0xf9010113.
Lemma F_6c2ac : fetch_word AsanUbsan.M.loaded_segments (0x6c2f4 : word) = Some W_6c2ac.
Proof. vm_refl. Qed.
Lemma D_6c2ac : decode_any W_6c2ac = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c2b0 : bv 32 := 0x00050913.
Lemma F_6c2b0 : fetch_word AsanUbsan.M.loaded_segments (0x6c2f8 : word) = Some W_6c2b0.
Proof. vm_refl. Qed.
Lemma D_6c2b0 : decode_any W_6c2b0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c2b4 : bv 32 := 0x5551c0ef.
Lemma F_6c2b4 : fetch_word AsanUbsan.M.loaded_segments (0x6c2fc : word) = Some W_6c2b4.
Proof. vm_refl. Qed.
Lemma D_6c2b4 : decode_any W_6c2b4 = Some (Jal 1 118100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c2b8 : bv 32 := 0x0a050863.
Lemma F_6c2b8 : fetch_word AsanUbsan.M.loaded_segments (0x6c300 : word) = Some W_6c2b8.
Proof. vm_refl. Qed.
Lemma D_6c2b8 : decode_any W_6c2b8 = Some (Branch BC_EQ 10 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c2bc : bv 32 := 0x45d1d0ef.
Lemma F_6c2bc : fetch_word AsanUbsan.M.loaded_segments (0x6c304 : word) = Some W_6c2bc.
Proof. vm_refl. Qed.
Lemma D_6c2bc : decode_any W_6c2bc = Some (Jal 1 121948, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c2c0 : bv 32 := 0x000fa597.
Lemma F_6c2c0 : fetch_word AsanUbsan.M.loaded_segments (0x6c308 : word) = Some W_6c2c0.
Proof. vm_refl. Qed.
Lemma D_6c2c0 : decode_any W_6c2c0 = Some (Auipc 11 250, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c2c4 : bv 32 := 0x0505b583.
Lemma F_6c2c4 : fetch_word AsanUbsan.M.loaded_segments (0x6c30c : word) = Some W_6c2c4.
Proof. vm_refl. Qed.
Lemma D_6c2c4 : decode_any W_6c2c4 = Some (Load SZ8 true 11 11 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c2c8 : bv 32 := 0x00050493.
Lemma F_6c2c8 : fetch_word AsanUbsan.M.loaded_segments (0x6c310 : word) = Some W_6c2c8.
Proof. vm_refl. Qed.
Lemma D_6c2c8 : decode_any W_6c2c8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c2cc : bv 32 := 0x00090513.
Lemma F_6c2cc : fetch_word AsanUbsan.M.loaded_segments (0x6c314 : word) = Some W_6c2cc.
Proof. vm_refl. Qed.
Lemma D_6c2cc : decode_any W_6c2cc = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c2d0 : bv 32 := 0x000580e7.
Lemma F_6c2d0 : fetch_word AsanUbsan.M.loaded_segments (0x6c318 : word) = Some W_6c2d0.
Proof. vm_refl. Qed.
Lemma D_6c2d0 : decode_any W_6c2d0 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c2d4 : bv 32 := 0x06048463.
Lemma F_6c2d4 : fetch_word AsanUbsan.M.loaded_segments (0x6c31c : word) = Some W_6c2d4.
Proof. vm_refl. Qed.
Lemma D_6c2d4 : decode_any W_6c2d4 = Some (Branch BC_EQ 9 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c2d8 : bv 32 := 0x000f8597.
Lemma F_6c2d8 : fetch_word AsanUbsan.M.loaded_segments (0x6c320 : word) = Some W_6c2d8.
Proof. vm_refl. Qed.
Lemma D_6c2d8 : decode_any W_6c2d8 = Some (Auipc 11 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c2dc : bv 32 := 0x1e85b983.
Lemma F_6c2dc : fetch_word AsanUbsan.M.loaded_segments (0x6c324 : word) = Some W_6c2dc.
Proof. vm_refl. Qed.
Lemma D_6c2dc : decode_any W_6c2dc = Some (Load SZ8 true 19 11 488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c2e0 : bv 32 := 0x0fb9c583.
Lemma F_6c2e0 : fetch_word AsanUbsan.M.loaded_segments (0x6c328 : word) = Some W_6c2e0.
Proof. vm_refl. Qed.
Lemma D_6c2e0 : decode_any W_6c2e0 = Some (Load SZ1 false 11 19 251, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c2e4 : bv 32 := 0x04058c63.
Lemma F_6c2e4 : fetch_word AsanUbsan.M.loaded_segments (0x6c32c : word) = Some W_6c2e4.
Proof. vm_refl. Qed.
Lemma D_6c2e4 : decode_any W_6c2e4 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c2e8 : bv 32 := 0x00150493.
Lemma F_6c2e8 : fetch_word AsanUbsan.M.loaded_segments (0x6c330 : word) = Some W_6c2e8.
Proof. vm_refl. Qed.
Lemma D_6c2e8 : decode_any W_6c2e8 = Some (OpImm ALU_ADD 9 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c2ec : bv 32 := 0xfff94593.
Lemma F_6c2ec : fetch_word AsanUbsan.M.loaded_segments (0x6c334 : word) = Some W_6c2ec.
Proof. vm_refl. Qed.
Lemma D_6c2ec : decode_any W_6c2ec = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c2f0 : bv 32 := 0x80040a13.
Lemma F_6c2f0 : fetch_word AsanUbsan.M.loaded_segments (0x6c338 : word) = Some W_6c2f0.
Proof. vm_refl. Qed.
Lemma D_6c2f0 : decode_any W_6c2f0 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c2f4 : bv 32 := 0xfa8a0a13.
Lemma F_6c2f4 : fetch_word AsanUbsan.M.loaded_segments (0x6c33c : word) = Some W_6c2f4.
Proof. vm_refl. Qed.
Lemma D_6c2f4 : decode_any W_6c2f4 = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c2f8 : bv 32 := 0x0a95e063.
Lemma F_6c2f8 : fetch_word AsanUbsan.M.loaded_segments (0x6c340 : word) = Some W_6c2f8.
Proof. vm_refl. Qed.
Lemma D_6c2f8 : decode_any W_6c2f8 = Some (Branch BC_LTU 11 9 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c2fc : bv 32 := 0x04000593.
Lemma F_6c2fc : fetch_word AsanUbsan.M.loaded_segments (0x6c344 : word) = Some W_6c2fc.
Proof. vm_refl. Qed.
Lemma D_6c2fc : decode_any W_6c2fc = Some (OpImm ALU_ADD 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c300 : bv 32 := 0x10b57263.
Lemma F_6c300 : fetch_word AsanUbsan.M.loaded_segments (0x6c348 : word) = Some W_6c300.
Proof. vm_refl. Qed.
Lemma D_6c300 : decode_any W_6c300 = Some (Branch BC_GEU 10 11 260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c304 : bv 32 := 0x000f8597.
Lemma F_6c304 : fetch_word AsanUbsan.M.loaded_segments (0x6c34c : word) = Some W_6c304.
Proof. vm_refl. Qed.
Lemma D_6c304 : decode_any W_6c304 = Some (Auipc 11 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c308 : bv 32 := 0x1cc5b583.
Lemma F_6c308 : fetch_word AsanUbsan.M.loaded_segments (0x6c350 : word) = Some W_6c308.
Proof. vm_refl. Qed.
Lemma D_6c308 : decode_any W_6c308 = Some (Load SZ8 true 11 11 460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c30c : bv 32 := 0x0005b603.
Lemma F_6c30c : fetch_word AsanUbsan.M.loaded_segments (0x6c354 : word) = Some W_6c30c.
Proof. vm_refl. Qed.
Lemma D_6c30c : decode_any W_6c30c = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c310 : bv 32 := 0x012506b3.
Lemma F_6c310 : fetch_word AsanUbsan.M.loaded_segments (0x6c358 : word) = Some W_6c310.
Proof. vm_refl. Qed.
Lemma D_6c310 : decode_any W_6c310 = Some (Op ALU_ADD 13 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c314 : bv 32 := 0x00395593.
Lemma F_6c314 : fetch_word AsanUbsan.M.loaded_segments (0x6c35c : word) = Some W_6c314.
Proof. vm_refl. Qed.
Lemma D_6c314 : decode_any W_6c314 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c318 : bv 32 := 0x0036d713.
Lemma F_6c318 : fetch_word AsanUbsan.M.loaded_segments (0x6c360 : word) = Some W_6c318.
Proof. vm_refl. Qed.
Lemma D_6c318 : decode_any W_6c318 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c31c : bv 32 := 0x00b605b3.
Lemma F_6c31c : fetch_word AsanUbsan.M.loaded_segments (0x6c364 : word) = Some W_6c31c.
Proof. vm_refl. Qed.
Lemma D_6c31c : decode_any W_6c31c = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c320 : bv 32 := 0x00e60633.
Lemma F_6c320 : fetch_word AsanUbsan.M.loaded_segments (0x6c368 : word) = Some W_6c320.
Proof. vm_refl. Qed.
Lemma D_6c320 : decode_any W_6c320 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c324 : bv 32 := 0xff85f713.
Lemma F_6c324 : fetch_word AsanUbsan.M.loaded_segments (0x6c36c : word) = Some W_6c324.
Proof. vm_refl. Qed.
Lemma D_6c324 : decode_any W_6c324 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c328 : bv 32 := 0xff867793.
Lemma F_6c328 : fetch_word AsanUbsan.M.loaded_segments (0x6c370 : word) = Some W_6c328.
Proof. vm_refl. Qed.
Lemma D_6c328 : decode_any W_6c328 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c32c : bv 32 := 0x00073703.
Lemma F_6c32c : fetch_word AsanUbsan.M.loaded_segments (0x6c374 : word) = Some W_6c32c.
Proof. vm_refl. Qed.
Lemma D_6c32c : decode_any W_6c32c = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c330 : bv 32 := 0x0007b783.
Lemma F_6c330 : fetch_word AsanUbsan.M.loaded_segments (0x6c378 : word) = Some W_6c330.
Proof. vm_refl. Qed.
Lemma D_6c330 : decode_any W_6c330 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c334 : bv 32 := 0x00e7e733.
Lemma F_6c334 : fetch_word AsanUbsan.M.loaded_segments (0x6c37c : word) = Some W_6c334.
Proof. vm_refl. Qed.
Lemma D_6c334 : decode_any W_6c334 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c338 : bv 32 := 0x0c071e63.
Lemma F_6c338 : fetch_word AsanUbsan.M.loaded_segments (0x6c380 : word) = Some W_6c338.
Proof. vm_refl. Qed.
Lemma D_6c338 : decode_any W_6c338 = Some (Branch BC_NE 14 0 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c33c : bv 32 := 0x07010113.
Lemma F_6c33c : fetch_word AsanUbsan.M.loaded_segments (0x6c384 : word) = Some W_6c33c.
Proof. vm_refl. Qed.
Lemma D_6c33c : decode_any W_6c33c = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c340 : bv 32 := 0x7e813083.
Lemma F_6c340 : fetch_word AsanUbsan.M.loaded_segments (0x6c388 : word) = Some W_6c340.
Proof. vm_refl. Qed.
Lemma D_6c340 : decode_any W_6c340 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c344 : bv 32 := 0x7e013403.
Lemma F_6c344 : fetch_word AsanUbsan.M.loaded_segments (0x6c38c : word) = Some W_6c344.
Proof. vm_refl. Qed.
Lemma D_6c344 : decode_any W_6c344 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c348 : bv 32 := 0x7d813483.
Lemma F_6c348 : fetch_word AsanUbsan.M.loaded_segments (0x6c390 : word) = Some W_6c348.
Proof. vm_refl. Qed.
Lemma D_6c348 : decode_any W_6c348 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c34c : bv 32 := 0x7d013903.
Lemma F_6c34c : fetch_word AsanUbsan.M.loaded_segments (0x6c394 : word) = Some W_6c34c.
Proof. vm_refl. Qed.
Lemma D_6c34c : decode_any W_6c34c = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c350 : bv 32 := 0x7c813983.
Lemma F_6c350 : fetch_word AsanUbsan.M.loaded_segments (0x6c398 : word) = Some W_6c350.
Proof. vm_refl. Qed.
Lemma D_6c350 : decode_any W_6c350 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c354 : bv 32 := 0x7c013a03.
Lemma F_6c354 : fetch_word AsanUbsan.M.loaded_segments (0x6c39c : word) = Some W_6c354.
Proof. vm_refl. Qed.
Lemma D_6c354 : decode_any W_6c354 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c358 : bv 32 := 0x7b813a83.
Lemma F_6c358 : fetch_word AsanUbsan.M.loaded_segments (0x6c3a0 : word) = Some W_6c358.
Proof. vm_refl. Qed.
Lemma D_6c358 : decode_any W_6c358 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c35c : bv 32 := 0x7b013b03.
Lemma F_6c35c : fetch_word AsanUbsan.M.loaded_segments (0x6c3a4 : word) = Some W_6c35c.
Proof. vm_refl. Qed.
Lemma D_6c35c : decode_any W_6c35c = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c360 : bv 32 := 0x7f010113.
Lemma F_6c360 : fetch_word AsanUbsan.M.loaded_segments (0x6c3a8 : word) = Some W_6c360.
Proof. vm_refl. Qed.
Lemma D_6c360 : decode_any W_6c360 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c364 : bv 32 := 0x00008067.
Lemma F_6c364 : fetch_word AsanUbsan.M.loaded_segments (0x6c3ac : word) = Some W_6c364.
Proof. vm_refl. Qed.
Lemma D_6c364 : decode_any W_6c364 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c404 : bv 32 := 0x00050a93.
Lemma F_6c404 : fetch_word AsanUbsan.M.loaded_segments (0x6c44c : word) = Some W_6c404.
Proof. vm_refl. Qed.
Lemma D_6c404 : decode_any W_6c404 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c408 : bv 32 := 0x04049263.
Lemma F_6c408 : fetch_word AsanUbsan.M.loaded_segments (0x6c450 : word) = Some W_6c408.
Proof. vm_refl. Qed.
Lemma D_6c408 : decode_any W_6c408 = Some (Branch BC_NE 9 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c414 : bv 32 := 0x00050a93.
Lemma F_6c414 : fetch_word AsanUbsan.M.loaded_segments (0x6c45c : word) = Some W_6c414.
Proof. vm_refl. Qed.
Lemma D_6c414 : decode_any W_6c414 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c418 : bv 32 := 0x00060503.
Lemma F_6c418 : fetch_word AsanUbsan.M.loaded_segments (0x6c460 : word) = Some W_6c418.
Proof. vm_refl. Qed.
Lemma D_6c418 : decode_any W_6c418 = Some (Load SZ1 true 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c41c : bv 32 := 0x0076f693.
Lemma F_6c41c : fetch_word AsanUbsan.M.loaded_segments (0x6c464 : word) = Some W_6c41c.
Proof. vm_refl. Qed.
Lemma D_6c41c : decode_any W_6c41c = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c420 : bv 32 := 0x00a03733.
Lemma F_6c420 : fetch_word AsanUbsan.M.loaded_segments (0x6c468 : word) = Some W_6c420.
Proof. vm_refl. Qed.
Lemma D_6c420 : decode_any W_6c420 = Some (Op ALU_SLTU 14 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c424 : bv 32 := 0x00a6a533.
Lemma F_6c424 : fetch_word AsanUbsan.M.loaded_segments (0x6c46c : word) = Some W_6c424.
Proof. vm_refl. Qed.
Lemma D_6c424 : decode_any W_6c424 = Some (Op ALU_SLT 10 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c428 : bv 32 := 0x00154513.
Lemma F_6c428 : fetch_word AsanUbsan.M.loaded_segments (0x6c470 : word) = Some W_6c428.
Proof. vm_refl. Qed.
Lemma D_6c428 : decode_any W_6c428 = Some (OpImm ALU_XOR 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c42c : bv 32 := 0x00a77533.
Lemma F_6c42c : fetch_word AsanUbsan.M.loaded_segments (0x6c474 : word) = Some W_6c42c.
Proof. vm_refl. Qed.
Lemma D_6c42c : decode_any W_6c42c = Some (Op ALU_AND 10 14 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c430 : bv 32 := 0x00c5fa63.
Lemma F_6c430 : fetch_word AsanUbsan.M.loaded_segments (0x6c478 : word) = Some W_6c430.
Proof. vm_refl. Qed.
Lemma D_6c430 : decode_any W_6c430 = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c434 : bv 32 := 0x0005c683.
Lemma F_6c434 : fetch_word AsanUbsan.M.loaded_segments (0x6c47c : word) = Some W_6c434.
Proof. vm_refl. Qed.
Lemma D_6c434 : decode_any W_6c434 = Some (Load SZ1 false 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c438 : bv 32 := 0x00158593.
Lemma F_6c438 : fetch_word AsanUbsan.M.loaded_segments (0x6c480 : word) = Some W_6c438.
Proof. vm_refl. Qed.
Lemma D_6c438 : decode_any W_6c438 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c43c : bv 32 := 0x00a6e533.
Lemma F_6c43c : fetch_word AsanUbsan.M.loaded_segments (0x6c484 : word) = Some W_6c43c.
Proof. vm_refl. Qed.
Lemma D_6c43c : decode_any W_6c43c = Some (Op ALU_OR 10 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c440 : bv 32 := 0xfec59ae3.
Lemma F_6c440 : fetch_word AsanUbsan.M.loaded_segments (0x6c488 : word) = Some W_6c440.
Proof. vm_refl. Qed.
Lemma D_6c440 : decode_any W_6c440 = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c444 : bv 32 := 0x0ff57513.
Lemma F_6c444 : fetch_word AsanUbsan.M.loaded_segments (0x6c48c : word) = Some W_6c444.
Proof. vm_refl. Qed.
Lemma D_6c444 : decode_any W_6c444 = Some (OpImm ALU_AND 10 10 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c448 : bv 32 := 0x0c050463.
Lemma F_6c448 : fetch_word AsanUbsan.M.loaded_segments (0x6c490 : word) = Some W_6c448.
Proof. vm_refl. Qed.
Lemma D_6c448 : decode_any W_6c448 = Some (Branch BC_EQ 10 0 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c44c : bv 32 := 0x00090513.
Lemma F_6c44c : fetch_word AsanUbsan.M.loaded_segments (0x6c494 : word) = Some W_6c44c.
Proof. vm_refl. Qed.
Lemma D_6c44c : decode_any W_6c44c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c450 : bv 32 := 0x00048593.
Lemma F_6c450 : fetch_word AsanUbsan.M.loaded_segments (0x6c498 : word) = Some W_6c450.
Proof. vm_refl. Qed.
Lemma D_6c450 : decode_any W_6c450 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c454 : bv 32 := 0x6a1170ef.
Lemma F_6c454 : fetch_word AsanUbsan.M.loaded_segments (0x6c49c : word) = Some W_6c454.
Proof. vm_refl. Qed.
Lemma D_6c454 : decode_any W_6c454 = Some (Jal 1 97952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c458 : bv 32 := 0x0a050c63.
Lemma F_6c458 : fetch_word AsanUbsan.M.loaded_segments (0x6c4a0 : word) = Some W_6c458.
Proof. vm_refl. Qed.
Lemma D_6c458 : decode_any W_6c458 = Some (Branch BC_EQ 10 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c510 : bv 32 := 0x000a8513.
Lemma F_6c510 : fetch_word AsanUbsan.M.loaded_segments (0x6c558 : word) = Some W_6c510.
Proof. vm_refl. Qed.
Lemma D_6c510 : decode_any W_6c510 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c514 : bv 32 := 0xe29ff06f.
Lemma F_6c514 : fetch_word AsanUbsan.M.loaded_segments (0x6c55c : word) = Some W_6c514.
Proof. vm_refl. Qed.
Lemma D_6c514 : decode_any W_6c514 = Some (Jal 0 2096680, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c568 : bv 32 := 0x06048a63.
Lemma F_6c568 : fetch_word AsanUbsan.M.loaded_segments (0x6c5b0 : word) = Some W_6c568.
Proof. vm_refl. Qed.
Lemma D_6c568 : decode_any W_6c568 = Some (Branch BC_EQ 9 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c56c : bv 32 := 0x000f8597.
Lemma F_6c56c : fetch_word AsanUbsan.M.loaded_segments (0x6c5b4 : word) = Some W_6c56c.
Proof. vm_refl. Qed.
Lemma D_6c56c : decode_any W_6c56c = Some (Auipc 11 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c570 : bv 32 := 0xf545ba83.
Lemma F_6c570 : fetch_word AsanUbsan.M.loaded_segments (0x6c5b8 : word) = Some W_6c570.
Proof. vm_refl. Qed.
Lemma D_6c570 : decode_any W_6c570 = Some (Load SZ8 true 21 11 3924, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c574 : bv 32 := 0x0fbac583.
Lemma F_6c574 : fetch_word AsanUbsan.M.loaded_segments (0x6c5bc : word) = Some W_6c574.
Proof. vm_refl. Qed.
Lemma D_6c574 : decode_any W_6c574 = Some (Load SZ1 false 11 21 251, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c578 : bv 32 := 0x06058263.
Lemma F_6c578 : fetch_word AsanUbsan.M.loaded_segments (0x6c5c0 : word) = Some W_6c578.
Proof. vm_refl. Qed.
Lemma D_6c578 : decode_any W_6c578 = Some (Branch BC_EQ 11 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c57c : bv 32 := 0x00150493.
Lemma F_6c57c : fetch_word AsanUbsan.M.loaded_segments (0x6c5c4 : word) = Some W_6c57c.
Proof. vm_refl. Qed.
Lemma D_6c57c : decode_any W_6c57c = Some (OpImm ALU_ADD 9 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c580 : bv 32 := 0x0934f463.
Lemma F_6c580 : fetch_word AsanUbsan.M.loaded_segments (0x6c5c8 : word) = Some W_6c580.
Proof. vm_refl. Qed.
Lemma D_6c580 : decode_any W_6c580 = Some (Branch BC_GEU 9 19 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c584 : bv 32 := 0xfff94593.
Lemma F_6c584 : fetch_word AsanUbsan.M.loaded_segments (0x6c5cc : word) = Some W_6c584.
Proof. vm_refl. Qed.
Lemma D_6c584 : decode_any W_6c584 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c588 : bv 32 := 0x80040a13.
Lemma F_6c588 : fetch_word AsanUbsan.M.loaded_segments (0x6c5d0 : word) = Some W_6c588.
Proof. vm_refl. Qed.
Lemma D_6c588 : decode_any W_6c588 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c58c : bv 32 := 0xfa8a0a13.
Lemma F_6c58c : fetch_word AsanUbsan.M.loaded_segments (0x6c5d4 : word) = Some W_6c58c.
Proof. vm_refl. Qed.
Lemma D_6c58c : decode_any W_6c58c = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c590 : bv 32 := 0x0895e663.
Lemma F_6c590 : fetch_word AsanUbsan.M.loaded_segments (0x6c5d8 : word) = Some W_6c590.
Proof. vm_refl. Qed.
Lemma D_6c590 : decode_any W_6c590 = Some (Branch BC_LTU 11 9 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c594 : bv 32 := 0xfbf48593.
Lemma F_6c594 : fetch_word AsanUbsan.M.loaded_segments (0x6c5dc : word) = Some W_6c594.
Proof. vm_refl. Qed.
Lemma D_6c594 : decode_any W_6c594 = Some (OpImm ALU_ADD 11 9 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c598 : bv 32 := 0xfbf00613.
Lemma F_6c598 : fetch_word AsanUbsan.M.loaded_segments (0x6c5e0 : word) = Some W_6c598.
Proof. vm_refl. Qed.
Lemma D_6c598 : decode_any W_6c598 = Some (OpImm ALU_ADD 12 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c59c : bv 32 := 0x0eb67863.
Lemma F_6c59c : fetch_word AsanUbsan.M.loaded_segments (0x6c5e4 : word) = Some W_6c59c.
Proof. vm_refl. Qed.
Lemma D_6c59c : decode_any W_6c59c = Some (Branch BC_GEU 12 11 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c5a0 : bv 32 := 0x000f8597.
Lemma F_6c5a0 : fetch_word AsanUbsan.M.loaded_segments (0x6c5e8 : word) = Some W_6c5a0.
Proof. vm_refl. Qed.
Lemma D_6c5a0 : decode_any W_6c5a0 = Some (Auipc 11 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c5a4 : bv 32 := 0xf305b583.
Lemma F_6c5a4 : fetch_word AsanUbsan.M.loaded_segments (0x6c5ec : word) = Some W_6c5a4.
Proof. vm_refl. Qed.
Lemma D_6c5a4 : decode_any W_6c5a4 = Some (Load SZ8 true 11 11 3888, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c5a8 : bv 32 := 0x009906b3.
Lemma F_6c5a8 : fetch_word AsanUbsan.M.loaded_segments (0x6c5f0 : word) = Some W_6c5a8.
Proof. vm_refl. Qed.
Lemma D_6c5a8 : decode_any W_6c5a8 = Some (Op ALU_ADD 13 18 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c5ac : bv 32 := 0x0005b603.
Lemma F_6c5ac : fetch_word AsanUbsan.M.loaded_segments (0x6c5f4 : word) = Some W_6c5ac.
Proof. vm_refl. Qed.
Lemma D_6c5ac : decode_any W_6c5ac = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c5b0 : bv 32 := 0x00395593.
Lemma F_6c5b0 : fetch_word AsanUbsan.M.loaded_segments (0x6c5f8 : word) = Some W_6c5b0.
Proof. vm_refl. Qed.
Lemma D_6c5b0 : decode_any W_6c5b0 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c5b4 : bv 32 := 0xfff68693.
Lemma F_6c5b4 : fetch_word AsanUbsan.M.loaded_segments (0x6c5fc : word) = Some W_6c5b4.
Proof. vm_refl. Qed.
Lemma D_6c5b4 : decode_any W_6c5b4 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c5b8 : bv 32 := 0x0036d713.
Lemma F_6c5b8 : fetch_word AsanUbsan.M.loaded_segments (0x6c600 : word) = Some W_6c5b8.
Proof. vm_refl. Qed.
Lemma D_6c5b8 : decode_any W_6c5b8 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c5bc : bv 32 := 0x00b605b3.
Lemma F_6c5bc : fetch_word AsanUbsan.M.loaded_segments (0x6c604 : word) = Some W_6c5bc.
Proof. vm_refl. Qed.
Lemma D_6c5bc : decode_any W_6c5bc = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c5c0 : bv 32 := 0x00e60633.
Lemma F_6c5c0 : fetch_word AsanUbsan.M.loaded_segments (0x6c608 : word) = Some W_6c5c0.
Proof. vm_refl. Qed.
Lemma D_6c5c0 : decode_any W_6c5c0 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c5c4 : bv 32 := 0xff85f713.
Lemma F_6c5c4 : fetch_word AsanUbsan.M.loaded_segments (0x6c60c : word) = Some W_6c5c4.
Proof. vm_refl. Qed.
Lemma D_6c5c4 : decode_any W_6c5c4 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c5c8 : bv 32 := 0xff867793.
Lemma F_6c5c8 : fetch_word AsanUbsan.M.loaded_segments (0x6c610 : word) = Some W_6c5c8.
Proof. vm_refl. Qed.
Lemma D_6c5c8 : decode_any W_6c5c8 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c5cc : bv 32 := 0x00073703.
Lemma F_6c5cc : fetch_word AsanUbsan.M.loaded_segments (0x6c614 : word) = Some W_6c5cc.
Proof. vm_refl. Qed.
Lemma D_6c5cc : decode_any W_6c5cc = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c5d0 : bv 32 := 0x0007b783.
Lemma F_6c5d0 : fetch_word AsanUbsan.M.loaded_segments (0x6c618 : word) = Some W_6c5d0.
Proof. vm_refl. Qed.
Lemma D_6c5d0 : decode_any W_6c5d0 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c5d4 : bv 32 := 0x00e7e733.
Lemma F_6c5d4 : fetch_word AsanUbsan.M.loaded_segments (0x6c61c : word) = Some W_6c5d4.
Proof. vm_refl. Qed.
Lemma D_6c5d4 : decode_any W_6c5d4 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c5d8 : bv 32 := 0x0a071e63.
Lemma F_6c5d8 : fetch_word AsanUbsan.M.loaded_segments (0x6c620 : word) = Some W_6c5d8.
Proof. vm_refl. Qed.
Lemma D_6c5d8 : decode_any W_6c5d8 = Some (Branch BC_NE 14 0 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c68c : bv 32 := 0x02049e63.
Lemma F_6c68c : fetch_word AsanUbsan.M.loaded_segments (0x6c6d4 : word) = Some W_6c68c.
Proof. vm_refl. Qed.
Lemma D_6c68c : decode_any W_6c68c = Some (Branch BC_NE 9 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6c8 : bv 32 := 0x00050b13.
Lemma F_6c6c8 : fetch_word AsanUbsan.M.loaded_segments (0x6c710 : word) = Some W_6c6c8.
Proof. vm_refl. Qed.
Lemma D_6c6c8 : decode_any W_6c6c8 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6cc : bv 32 := 0x00090513.
Lemma F_6c6cc : fetch_word AsanUbsan.M.loaded_segments (0x6c714 : word) = Some W_6c6cc.
Proof. vm_refl. Qed.
Lemma D_6c6cc : decode_any W_6c6cc = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6d0 : bv 32 := 0x00048593.
Lemma F_6c6d0 : fetch_word AsanUbsan.M.loaded_segments (0x6c718 : word) = Some W_6c6d0.
Proof. vm_refl. Qed.
Lemma D_6c6d0 : decode_any W_6c6d0 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6d4 : bv 32 := 0x421170ef.
Lemma F_6c6d4 : fetch_word AsanUbsan.M.loaded_segments (0x6c71c : word) = Some W_6c6d4.
Proof. vm_refl. Qed.
Lemma D_6c6d4 : decode_any W_6c6d4 = Some (Jal 1 97312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6d8 : bv 32 := 0x00050913.
Lemma F_6c6d8 : fetch_word AsanUbsan.M.loaded_segments (0x6c720 : word) = Some W_6c6d8.
Proof. vm_refl. Qed.
Lemma D_6c6d8 : decode_any W_6c6d8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6dc : bv 32 := 0x000b0513.
Lemma F_6c6dc : fetch_word AsanUbsan.M.loaded_segments (0x6c724 : word) = Some W_6c6dc.
Proof. vm_refl. Qed.
Lemma D_6c6dc : decode_any W_6c6dc = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6e0 : bv 32 := 0xee090ee3.
Lemma F_6c6e0 : fetch_word AsanUbsan.M.loaded_segments (0x6c728 : word) = Some W_6c6e0.
Proof. vm_refl. Qed.
Lemma D_6c6e0 : decode_any W_6c6e0 = Some (Branch BC_EQ 18 0 7932, 4%Z).
Proof. vm_refl. Qed.

