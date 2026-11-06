(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6a8c4 : bv 32 := 0x0e40006f.
Lemma F_6a8c4 : fetch_word AsanUbsan.M.loaded_segments (0x6a90c : word) = Some W_6a8c4.
Proof. vm_refl. Qed.
Lemma D_6a8c4 : decode_any W_6a8c4 = Some (Jal 0 228, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a8e8 : bv 32 := 0x1dc0206f.
Lemma F_6a8e8 : fetch_word AsanUbsan.M.loaded_segments (0x6a930 : word) = Some W_6a8e8.
Proof. vm_refl. Qed.
Lemma D_6a8e8 : decode_any W_6a8e8 = Some (Jal 0 8668, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a948 : bv 32 := 0x4a50706f.
Lemma F_6a948 : fetch_word AsanUbsan.M.loaded_segments (0x6a990 : word) = Some W_6a948.
Proof. vm_refl. Qed.
Lemma D_6a948 : decode_any W_6a948 = Some (Jal 0 31908, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a9a8 : bv 32 := 0x81010113.
Lemma F_6a9a8 : fetch_word AsanUbsan.M.loaded_segments (0x6a9f0 : word) = Some W_6a9a8.
Proof. vm_refl. Qed.
Lemma D_6a9a8 : decode_any W_6a9a8 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a9ac : bv 32 := 0x7e113423.
Lemma F_6a9ac : fetch_word AsanUbsan.M.loaded_segments (0x6a9f4 : word) = Some W_6a9ac.
Proof. vm_refl. Qed.
Lemma D_6a9ac : decode_any W_6a9ac = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a9b0 : bv 32 := 0x7e813023.
Lemma F_6a9b0 : fetch_word AsanUbsan.M.loaded_segments (0x6a9f8 : word) = Some W_6a9b0.
Proof. vm_refl. Qed.
Lemma D_6a9b0 : decode_any W_6a9b0 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a9b4 : bv 32 := 0x7c913c23.
Lemma F_6a9b4 : fetch_word AsanUbsan.M.loaded_segments (0x6a9fc : word) = Some W_6a9b4.
Proof. vm_refl. Qed.
Lemma D_6a9b4 : decode_any W_6a9b4 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a9b8 : bv 32 := 0x7d213823.
Lemma F_6a9b8 : fetch_word AsanUbsan.M.loaded_segments (0x6aa00 : word) = Some W_6a9b8.
Proof. vm_refl. Qed.
Lemma D_6a9b8 : decode_any W_6a9b8 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a9bc : bv 32 := 0x7d313423.
Lemma F_6a9bc : fetch_word AsanUbsan.M.loaded_segments (0x6aa04 : word) = Some W_6a9bc.
Proof. vm_refl. Qed.
Lemma D_6a9bc : decode_any W_6a9bc = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a9c0 : bv 32 := 0x7d413023.
Lemma F_6a9c0 : fetch_word AsanUbsan.M.loaded_segments (0x6aa08 : word) = Some W_6a9c0.
Proof. vm_refl. Qed.
Lemma D_6a9c0 : decode_any W_6a9c0 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a9c4 : bv 32 := 0x7b513c23.
Lemma F_6a9c4 : fetch_word AsanUbsan.M.loaded_segments (0x6aa0c : word) = Some W_6a9c4.
Proof. vm_refl. Qed.
Lemma D_6a9c4 : decode_any W_6a9c4 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a9c8 : bv 32 := 0x7b613823.
Lemma F_6a9c8 : fetch_word AsanUbsan.M.loaded_segments (0x6aa10 : word) = Some W_6a9c8.
Proof. vm_refl. Qed.
Lemma D_6a9c8 : decode_any W_6a9c8 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a9cc : bv 32 := 0x7f010413.
Lemma F_6a9cc : fetch_word AsanUbsan.M.loaded_segments (0x6aa14 : word) = Some W_6a9cc.
Proof. vm_refl. Qed.
Lemma D_6a9cc : decode_any W_6a9cc = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a9d0 : bv 32 := 0xf9010113.
Lemma F_6a9d0 : fetch_word AsanUbsan.M.loaded_segments (0x6aa18 : word) = Some W_6a9d0.
Proof. vm_refl. Qed.
Lemma D_6a9d0 : decode_any W_6a9d0 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a9d4 : bv 32 := 0x00050913.
Lemma F_6a9d4 : fetch_word AsanUbsan.M.loaded_segments (0x6aa1c : word) = Some W_6a9d4.
Proof. vm_refl. Qed.
Lemma D_6a9d4 : decode_any W_6a9d4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a9d8 : bv 32 := 0x5551c0ef.
Lemma F_6a9d8 : fetch_word AsanUbsan.M.loaded_segments (0x6aa20 : word) = Some W_6a9d8.
Proof. vm_refl. Qed.
Lemma D_6a9d8 : decode_any W_6a9d8 = Some (Jal 1 118100, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a9dc : bv 32 := 0x0a050863.
Lemma F_6a9dc : fetch_word AsanUbsan.M.loaded_segments (0x6aa24 : word) = Some W_6a9dc.
Proof. vm_refl. Qed.
Lemma D_6a9dc : decode_any W_6a9dc = Some (Branch BC_EQ 10 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a9e0 : bv 32 := 0x45d1d0ef.
Lemma F_6a9e0 : fetch_word AsanUbsan.M.loaded_segments (0x6aa28 : word) = Some W_6a9e0.
Proof. vm_refl. Qed.
Lemma D_6a9e0 : decode_any W_6a9e0 = Some (Jal 1 121948, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a9e4 : bv 32 := 0x000ec597.
Lemma F_6a9e4 : fetch_word AsanUbsan.M.loaded_segments (0x6aa2c : word) = Some W_6a9e4.
Proof. vm_refl. Qed.
Lemma D_6a9e4 : decode_any W_6a9e4 = Some (Auipc 11 236, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a9e8 : bv 32 := 0x9045b583.
Lemma F_6a9e8 : fetch_word AsanUbsan.M.loaded_segments (0x6aa30 : word) = Some W_6a9e8.
Proof. vm_refl. Qed.
Lemma D_6a9e8 : decode_any W_6a9e8 = Some (Load SZ8 true 11 11 2308, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a9ec : bv 32 := 0x00050493.
Lemma F_6a9ec : fetch_word AsanUbsan.M.loaded_segments (0x6aa34 : word) = Some W_6a9ec.
Proof. vm_refl. Qed.
Lemma D_6a9ec : decode_any W_6a9ec = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a9f0 : bv 32 := 0x00090513.
Lemma F_6a9f0 : fetch_word AsanUbsan.M.loaded_segments (0x6aa38 : word) = Some W_6a9f0.
Proof. vm_refl. Qed.
Lemma D_6a9f0 : decode_any W_6a9f0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a9f4 : bv 32 := 0x000580e7.
Lemma F_6a9f4 : fetch_word AsanUbsan.M.loaded_segments (0x6aa3c : word) = Some W_6a9f4.
Proof. vm_refl. Qed.
Lemma D_6a9f4 : decode_any W_6a9f4 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a9f8 : bv 32 := 0x06048463.
Lemma F_6a9f8 : fetch_word AsanUbsan.M.loaded_segments (0x6aa40 : word) = Some W_6a9f8.
Proof. vm_refl. Qed.
Lemma D_6a9f8 : decode_any W_6a9f8 = Some (Branch BC_EQ 9 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a9fc : bv 32 := 0x000ea597.
Lemma F_6a9fc : fetch_word AsanUbsan.M.loaded_segments (0x6aa44 : word) = Some W_6a9fc.
Proof. vm_refl. Qed.
Lemma D_6a9fc : decode_any W_6a9fc = Some (Auipc 11 234, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa00 : bv 32 := 0xaac5b983.
Lemma F_6aa00 : fetch_word AsanUbsan.M.loaded_segments (0x6aa48 : word) = Some W_6aa00.
Proof. vm_refl. Qed.
Lemma D_6aa00 : decode_any W_6aa00 = Some (Load SZ8 true 19 11 2732, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa04 : bv 32 := 0x0fb9c583.
Lemma F_6aa04 : fetch_word AsanUbsan.M.loaded_segments (0x6aa4c : word) = Some W_6aa04.
Proof. vm_refl. Qed.
Lemma D_6aa04 : decode_any W_6aa04 = Some (Load SZ1 false 11 19 251, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa08 : bv 32 := 0x04058c63.
Lemma F_6aa08 : fetch_word AsanUbsan.M.loaded_segments (0x6aa50 : word) = Some W_6aa08.
Proof. vm_refl. Qed.
Lemma D_6aa08 : decode_any W_6aa08 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa0c : bv 32 := 0x00150493.
Lemma F_6aa0c : fetch_word AsanUbsan.M.loaded_segments (0x6aa54 : word) = Some W_6aa0c.
Proof. vm_refl. Qed.
Lemma D_6aa0c : decode_any W_6aa0c = Some (OpImm ALU_ADD 9 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa10 : bv 32 := 0xfff94593.
Lemma F_6aa10 : fetch_word AsanUbsan.M.loaded_segments (0x6aa58 : word) = Some W_6aa10.
Proof. vm_refl. Qed.
Lemma D_6aa10 : decode_any W_6aa10 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa14 : bv 32 := 0x80040a13.
Lemma F_6aa14 : fetch_word AsanUbsan.M.loaded_segments (0x6aa5c : word) = Some W_6aa14.
Proof. vm_refl. Qed.
Lemma D_6aa14 : decode_any W_6aa14 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa18 : bv 32 := 0xfa8a0a13.
Lemma F_6aa18 : fetch_word AsanUbsan.M.loaded_segments (0x6aa60 : word) = Some W_6aa18.
Proof. vm_refl. Qed.
Lemma D_6aa18 : decode_any W_6aa18 = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa1c : bv 32 := 0x0a95e063.
Lemma F_6aa1c : fetch_word AsanUbsan.M.loaded_segments (0x6aa64 : word) = Some W_6aa1c.
Proof. vm_refl. Qed.
Lemma D_6aa1c : decode_any W_6aa1c = Some (Branch BC_LTU 11 9 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa20 : bv 32 := 0x04000593.
Lemma F_6aa20 : fetch_word AsanUbsan.M.loaded_segments (0x6aa68 : word) = Some W_6aa20.
Proof. vm_refl. Qed.
Lemma D_6aa20 : decode_any W_6aa20 = Some (OpImm ALU_ADD 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa24 : bv 32 := 0x10b57263.
Lemma F_6aa24 : fetch_word AsanUbsan.M.loaded_segments (0x6aa6c : word) = Some W_6aa24.
Proof. vm_refl. Qed.
Lemma D_6aa24 : decode_any W_6aa24 = Some (Branch BC_GEU 10 11 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa28 : bv 32 := 0x000ea597.
Lemma F_6aa28 : fetch_word AsanUbsan.M.loaded_segments (0x6aa70 : word) = Some W_6aa28.
Proof. vm_refl. Qed.
Lemma D_6aa28 : decode_any W_6aa28 = Some (Auipc 11 234, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa2c : bv 32 := 0xa905b583.
Lemma F_6aa2c : fetch_word AsanUbsan.M.loaded_segments (0x6aa74 : word) = Some W_6aa2c.
Proof. vm_refl. Qed.
Lemma D_6aa2c : decode_any W_6aa2c = Some (Load SZ8 true 11 11 2704, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa30 : bv 32 := 0x0005b603.
Lemma F_6aa30 : fetch_word AsanUbsan.M.loaded_segments (0x6aa78 : word) = Some W_6aa30.
Proof. vm_refl. Qed.
Lemma D_6aa30 : decode_any W_6aa30 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa34 : bv 32 := 0x012506b3.
Lemma F_6aa34 : fetch_word AsanUbsan.M.loaded_segments (0x6aa7c : word) = Some W_6aa34.
Proof. vm_refl. Qed.
Lemma D_6aa34 : decode_any W_6aa34 = Some (Op ALU_ADD 13 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa38 : bv 32 := 0x00395593.
Lemma F_6aa38 : fetch_word AsanUbsan.M.loaded_segments (0x6aa80 : word) = Some W_6aa38.
Proof. vm_refl. Qed.
Lemma D_6aa38 : decode_any W_6aa38 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa3c : bv 32 := 0x0036d713.
Lemma F_6aa3c : fetch_word AsanUbsan.M.loaded_segments (0x6aa84 : word) = Some W_6aa3c.
Proof. vm_refl. Qed.
Lemma D_6aa3c : decode_any W_6aa3c = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa40 : bv 32 := 0x00b605b3.
Lemma F_6aa40 : fetch_word AsanUbsan.M.loaded_segments (0x6aa88 : word) = Some W_6aa40.
Proof. vm_refl. Qed.
Lemma D_6aa40 : decode_any W_6aa40 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa44 : bv 32 := 0x00e60633.
Lemma F_6aa44 : fetch_word AsanUbsan.M.loaded_segments (0x6aa8c : word) = Some W_6aa44.
Proof. vm_refl. Qed.
Lemma D_6aa44 : decode_any W_6aa44 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa48 : bv 32 := 0xff85f713.
Lemma F_6aa48 : fetch_word AsanUbsan.M.loaded_segments (0x6aa90 : word) = Some W_6aa48.
Proof. vm_refl. Qed.
Lemma D_6aa48 : decode_any W_6aa48 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa4c : bv 32 := 0xff867793.
Lemma F_6aa4c : fetch_word AsanUbsan.M.loaded_segments (0x6aa94 : word) = Some W_6aa4c.
Proof. vm_refl. Qed.
Lemma D_6aa4c : decode_any W_6aa4c = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa50 : bv 32 := 0x00073703.
Lemma F_6aa50 : fetch_word AsanUbsan.M.loaded_segments (0x6aa98 : word) = Some W_6aa50.
Proof. vm_refl. Qed.
Lemma D_6aa50 : decode_any W_6aa50 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa54 : bv 32 := 0x0007b783.
Lemma F_6aa54 : fetch_word AsanUbsan.M.loaded_segments (0x6aa9c : word) = Some W_6aa54.
Proof. vm_refl. Qed.
Lemma D_6aa54 : decode_any W_6aa54 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa58 : bv 32 := 0x00e7e733.
Lemma F_6aa58 : fetch_word AsanUbsan.M.loaded_segments (0x6aaa0 : word) = Some W_6aa58.
Proof. vm_refl. Qed.
Lemma D_6aa58 : decode_any W_6aa58 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa5c : bv 32 := 0x0c071e63.
Lemma F_6aa5c : fetch_word AsanUbsan.M.loaded_segments (0x6aaa4 : word) = Some W_6aa5c.
Proof. vm_refl. Qed.
Lemma D_6aa5c : decode_any W_6aa5c = Some (Branch BC_NE 14 0 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa60 : bv 32 := 0x07010113.
Lemma F_6aa60 : fetch_word AsanUbsan.M.loaded_segments (0x6aaa8 : word) = Some W_6aa60.
Proof. vm_refl. Qed.
Lemma D_6aa60 : decode_any W_6aa60 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa64 : bv 32 := 0x7e813083.
Lemma F_6aa64 : fetch_word AsanUbsan.M.loaded_segments (0x6aaac : word) = Some W_6aa64.
Proof. vm_refl. Qed.
Lemma D_6aa64 : decode_any W_6aa64 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa68 : bv 32 := 0x7e013403.
Lemma F_6aa68 : fetch_word AsanUbsan.M.loaded_segments (0x6aab0 : word) = Some W_6aa68.
Proof. vm_refl. Qed.
Lemma D_6aa68 : decode_any W_6aa68 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa6c : bv 32 := 0x7d813483.
Lemma F_6aa6c : fetch_word AsanUbsan.M.loaded_segments (0x6aab4 : word) = Some W_6aa6c.
Proof. vm_refl. Qed.
Lemma D_6aa6c : decode_any W_6aa6c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa70 : bv 32 := 0x7d013903.
Lemma F_6aa70 : fetch_word AsanUbsan.M.loaded_segments (0x6aab8 : word) = Some W_6aa70.
Proof. vm_refl. Qed.
Lemma D_6aa70 : decode_any W_6aa70 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa74 : bv 32 := 0x7c813983.
Lemma F_6aa74 : fetch_word AsanUbsan.M.loaded_segments (0x6aabc : word) = Some W_6aa74.
Proof. vm_refl. Qed.
Lemma D_6aa74 : decode_any W_6aa74 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa78 : bv 32 := 0x7c013a03.
Lemma F_6aa78 : fetch_word AsanUbsan.M.loaded_segments (0x6aac0 : word) = Some W_6aa78.
Proof. vm_refl. Qed.
Lemma D_6aa78 : decode_any W_6aa78 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa7c : bv 32 := 0x7b813a83.
Lemma F_6aa7c : fetch_word AsanUbsan.M.loaded_segments (0x6aac4 : word) = Some W_6aa7c.
Proof. vm_refl. Qed.
Lemma D_6aa7c : decode_any W_6aa7c = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa80 : bv 32 := 0x7b013b03.
Lemma F_6aa80 : fetch_word AsanUbsan.M.loaded_segments (0x6aac8 : word) = Some W_6aa80.
Proof. vm_refl. Qed.
Lemma D_6aa80 : decode_any W_6aa80 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa84 : bv 32 := 0x7f010113.
Lemma F_6aa84 : fetch_word AsanUbsan.M.loaded_segments (0x6aacc : word) = Some W_6aa84.
Proof. vm_refl. Qed.
Lemma D_6aa84 : decode_any W_6aa84 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa88 : bv 32 := 0x00008067.
Lemma F_6aa88 : fetch_word AsanUbsan.M.loaded_segments (0x6aad0 : word) = Some W_6aa88.
Proof. vm_refl. Qed.
Lemma D_6aa88 : decode_any W_6aa88 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ab28 : bv 32 := 0x00050a93.
Lemma F_6ab28 : fetch_word AsanUbsan.M.loaded_segments (0x6ab70 : word) = Some W_6ab28.
Proof. vm_refl. Qed.
Lemma D_6ab28 : decode_any W_6ab28 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ab2c : bv 32 := 0x04049263.
Lemma F_6ab2c : fetch_word AsanUbsan.M.loaded_segments (0x6ab74 : word) = Some W_6ab2c.
Proof. vm_refl. Qed.
Lemma D_6ab2c : decode_any W_6ab2c = Some (Branch BC_NE 9 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ab38 : bv 32 := 0x00050a93.
Lemma F_6ab38 : fetch_word AsanUbsan.M.loaded_segments (0x6ab80 : word) = Some W_6ab38.
Proof. vm_refl. Qed.
Lemma D_6ab38 : decode_any W_6ab38 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ab3c : bv 32 := 0x00060503.
Lemma F_6ab3c : fetch_word AsanUbsan.M.loaded_segments (0x6ab84 : word) = Some W_6ab3c.
Proof. vm_refl. Qed.
Lemma D_6ab3c : decode_any W_6ab3c = Some (Load SZ1 true 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ab40 : bv 32 := 0x0076f693.
Lemma F_6ab40 : fetch_word AsanUbsan.M.loaded_segments (0x6ab88 : word) = Some W_6ab40.
Proof. vm_refl. Qed.
Lemma D_6ab40 : decode_any W_6ab40 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ab44 : bv 32 := 0x00a03733.
Lemma F_6ab44 : fetch_word AsanUbsan.M.loaded_segments (0x6ab8c : word) = Some W_6ab44.
Proof. vm_refl. Qed.
Lemma D_6ab44 : decode_any W_6ab44 = Some (Op ALU_SLTU 14 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ab48 : bv 32 := 0x00a6a533.
Lemma F_6ab48 : fetch_word AsanUbsan.M.loaded_segments (0x6ab90 : word) = Some W_6ab48.
Proof. vm_refl. Qed.
Lemma D_6ab48 : decode_any W_6ab48 = Some (Op ALU_SLT 10 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ab4c : bv 32 := 0x00154513.
Lemma F_6ab4c : fetch_word AsanUbsan.M.loaded_segments (0x6ab94 : word) = Some W_6ab4c.
Proof. vm_refl. Qed.
Lemma D_6ab4c : decode_any W_6ab4c = Some (OpImm ALU_XOR 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ab50 : bv 32 := 0x00a77533.
Lemma F_6ab50 : fetch_word AsanUbsan.M.loaded_segments (0x6ab98 : word) = Some W_6ab50.
Proof. vm_refl. Qed.
Lemma D_6ab50 : decode_any W_6ab50 = Some (Op ALU_AND 10 14 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ab54 : bv 32 := 0x00c5fa63.
Lemma F_6ab54 : fetch_word AsanUbsan.M.loaded_segments (0x6ab9c : word) = Some W_6ab54.
Proof. vm_refl. Qed.
Lemma D_6ab54 : decode_any W_6ab54 = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ab58 : bv 32 := 0x0005c683.
Lemma F_6ab58 : fetch_word AsanUbsan.M.loaded_segments (0x6aba0 : word) = Some W_6ab58.
Proof. vm_refl. Qed.
Lemma D_6ab58 : decode_any W_6ab58 = Some (Load SZ1 false 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ab5c : bv 32 := 0x00158593.
Lemma F_6ab5c : fetch_word AsanUbsan.M.loaded_segments (0x6aba4 : word) = Some W_6ab5c.
Proof. vm_refl. Qed.
Lemma D_6ab5c : decode_any W_6ab5c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ab60 : bv 32 := 0x00a6e533.
Lemma F_6ab60 : fetch_word AsanUbsan.M.loaded_segments (0x6aba8 : word) = Some W_6ab60.
Proof. vm_refl. Qed.
Lemma D_6ab60 : decode_any W_6ab60 = Some (Op ALU_OR 10 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ab64 : bv 32 := 0xfec59ae3.
Lemma F_6ab64 : fetch_word AsanUbsan.M.loaded_segments (0x6abac : word) = Some W_6ab64.
Proof. vm_refl. Qed.
Lemma D_6ab64 : decode_any W_6ab64 = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ab68 : bv 32 := 0x0ff57513.
Lemma F_6ab68 : fetch_word AsanUbsan.M.loaded_segments (0x6abb0 : word) = Some W_6ab68.
Proof. vm_refl. Qed.
Lemma D_6ab68 : decode_any W_6ab68 = Some (OpImm ALU_AND 10 10 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ab6c : bv 32 := 0x0c050463.
Lemma F_6ab6c : fetch_word AsanUbsan.M.loaded_segments (0x6abb4 : word) = Some W_6ab6c.
Proof. vm_refl. Qed.
Lemma D_6ab6c : decode_any W_6ab6c = Some (Branch BC_EQ 10 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ab70 : bv 32 := 0x00090513.
Lemma F_6ab70 : fetch_word AsanUbsan.M.loaded_segments (0x6abb8 : word) = Some W_6ab70.
Proof. vm_refl. Qed.
Lemma D_6ab70 : decode_any W_6ab70 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ab74 : bv 32 := 0x00048593.
Lemma F_6ab74 : fetch_word AsanUbsan.M.loaded_segments (0x6abbc : word) = Some W_6ab74.
Proof. vm_refl. Qed.
Lemma D_6ab74 : decode_any W_6ab74 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ab78 : bv 32 := 0x6a1170ef.
Lemma F_6ab78 : fetch_word AsanUbsan.M.loaded_segments (0x6abc0 : word) = Some W_6ab78.
Proof. vm_refl. Qed.
Lemma D_6ab78 : decode_any W_6ab78 = Some (Jal 1 97952, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ab7c : bv 32 := 0x0a050c63.
Lemma F_6ab7c : fetch_word AsanUbsan.M.loaded_segments (0x6abc4 : word) = Some W_6ab7c.
Proof. vm_refl. Qed.
Lemma D_6ab7c : decode_any W_6ab7c = Some (Branch BC_EQ 10 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ac34 : bv 32 := 0x000a8513.
Lemma F_6ac34 : fetch_word AsanUbsan.M.loaded_segments (0x6ac7c : word) = Some W_6ac34.
Proof. vm_refl. Qed.
Lemma D_6ac34 : decode_any W_6ac34 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ac38 : bv 32 := 0xe29ff06f.
Lemma F_6ac38 : fetch_word AsanUbsan.M.loaded_segments (0x6ac80 : word) = Some W_6ac38.
Proof. vm_refl. Qed.
Lemma D_6ac38 : decode_any W_6ac38 = Some (Jal 0 2096680, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ac8c : bv 32 := 0x06048a63.
Lemma F_6ac8c : fetch_word AsanUbsan.M.loaded_segments (0x6acd4 : word) = Some W_6ac8c.
Proof. vm_refl. Qed.
Lemma D_6ac8c : decode_any W_6ac8c = Some (Branch BC_EQ 9 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ac90 : bv 32 := 0x000ea597.
Lemma F_6ac90 : fetch_word AsanUbsan.M.loaded_segments (0x6acd8 : word) = Some W_6ac90.
Proof. vm_refl. Qed.
Lemma D_6ac90 : decode_any W_6ac90 = Some (Auipc 11 234, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ac94 : bv 32 := 0x8185ba83.
Lemma F_6ac94 : fetch_word AsanUbsan.M.loaded_segments (0x6acdc : word) = Some W_6ac94.
Proof. vm_refl. Qed.
Lemma D_6ac94 : decode_any W_6ac94 = Some (Load SZ8 true 21 11 2072, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ac98 : bv 32 := 0x0fbac583.
Lemma F_6ac98 : fetch_word AsanUbsan.M.loaded_segments (0x6ace0 : word) = Some W_6ac98.
Proof. vm_refl. Qed.
Lemma D_6ac98 : decode_any W_6ac98 = Some (Load SZ1 false 11 21 251, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ac9c : bv 32 := 0x06058263.
Lemma F_6ac9c : fetch_word AsanUbsan.M.loaded_segments (0x6ace4 : word) = Some W_6ac9c.
Proof. vm_refl. Qed.
Lemma D_6ac9c : decode_any W_6ac9c = Some (Branch BC_EQ 11 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aca0 : bv 32 := 0x00150493.
Lemma F_6aca0 : fetch_word AsanUbsan.M.loaded_segments (0x6ace8 : word) = Some W_6aca0.
Proof. vm_refl. Qed.
Lemma D_6aca0 : decode_any W_6aca0 = Some (OpImm ALU_ADD 9 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aca4 : bv 32 := 0x0934f463.
Lemma F_6aca4 : fetch_word AsanUbsan.M.loaded_segments (0x6acec : word) = Some W_6aca4.
Proof. vm_refl. Qed.
Lemma D_6aca4 : decode_any W_6aca4 = Some (Branch BC_GEU 9 19 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aca8 : bv 32 := 0xfff94593.
Lemma F_6aca8 : fetch_word AsanUbsan.M.loaded_segments (0x6acf0 : word) = Some W_6aca8.
Proof. vm_refl. Qed.
Lemma D_6aca8 : decode_any W_6aca8 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6acac : bv 32 := 0x80040a13.
Lemma F_6acac : fetch_word AsanUbsan.M.loaded_segments (0x6acf4 : word) = Some W_6acac.
Proof. vm_refl. Qed.
Lemma D_6acac : decode_any W_6acac = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_6acb0 : bv 32 := 0xfa8a0a13.
Lemma F_6acb0 : fetch_word AsanUbsan.M.loaded_segments (0x6acf8 : word) = Some W_6acb0.
Proof. vm_refl. Qed.
Lemma D_6acb0 : decode_any W_6acb0 = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_6acb4 : bv 32 := 0x0895e663.
Lemma F_6acb4 : fetch_word AsanUbsan.M.loaded_segments (0x6acfc : word) = Some W_6acb4.
Proof. vm_refl. Qed.
Lemma D_6acb4 : decode_any W_6acb4 = Some (Branch BC_LTU 11 9 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_6acb8 : bv 32 := 0xfbf48593.
Lemma F_6acb8 : fetch_word AsanUbsan.M.loaded_segments (0x6ad00 : word) = Some W_6acb8.
Proof. vm_refl. Qed.
Lemma D_6acb8 : decode_any W_6acb8 = Some (OpImm ALU_ADD 11 9 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_6acbc : bv 32 := 0xfbf00613.
Lemma F_6acbc : fetch_word AsanUbsan.M.loaded_segments (0x6ad04 : word) = Some W_6acbc.
Proof. vm_refl. Qed.
Lemma D_6acbc : decode_any W_6acbc = Some (OpImm ALU_ADD 12 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_6acc0 : bv 32 := 0x0eb67863.
Lemma F_6acc0 : fetch_word AsanUbsan.M.loaded_segments (0x6ad08 : word) = Some W_6acc0.
Proof. vm_refl. Qed.
Lemma D_6acc0 : decode_any W_6acc0 = Some (Branch BC_GEU 12 11 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_6acc4 : bv 32 := 0x000e9597.
Lemma F_6acc4 : fetch_word AsanUbsan.M.loaded_segments (0x6ad0c : word) = Some W_6acc4.
Proof. vm_refl. Qed.
Lemma D_6acc4 : decode_any W_6acc4 = Some (Auipc 11 233, 4%Z).
Proof. vm_refl. Qed.

Definition W_6acc8 : bv 32 := 0x7f45b583.
Lemma F_6acc8 : fetch_word AsanUbsan.M.loaded_segments (0x6ad10 : word) = Some W_6acc8.
Proof. vm_refl. Qed.
Lemma D_6acc8 : decode_any W_6acc8 = Some (Load SZ8 true 11 11 2036, 4%Z).
Proof. vm_refl. Qed.

Definition W_6accc : bv 32 := 0x009906b3.
Lemma F_6accc : fetch_word AsanUbsan.M.loaded_segments (0x6ad14 : word) = Some W_6accc.
Proof. vm_refl. Qed.
Lemma D_6accc : decode_any W_6accc = Some (Op ALU_ADD 13 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_6acd0 : bv 32 := 0x0005b603.
Lemma F_6acd0 : fetch_word AsanUbsan.M.loaded_segments (0x6ad18 : word) = Some W_6acd0.
Proof. vm_refl. Qed.
Lemma D_6acd0 : decode_any W_6acd0 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6acd4 : bv 32 := 0x00395593.
Lemma F_6acd4 : fetch_word AsanUbsan.M.loaded_segments (0x6ad1c : word) = Some W_6acd4.
Proof. vm_refl. Qed.
Lemma D_6acd4 : decode_any W_6acd4 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6acd8 : bv 32 := 0xfff68693.
Lemma F_6acd8 : fetch_word AsanUbsan.M.loaded_segments (0x6ad20 : word) = Some W_6acd8.
Proof. vm_refl. Qed.
Lemma D_6acd8 : decode_any W_6acd8 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6acdc : bv 32 := 0x0036d713.
Lemma F_6acdc : fetch_word AsanUbsan.M.loaded_segments (0x6ad24 : word) = Some W_6acdc.
Proof. vm_refl. Qed.
Lemma D_6acdc : decode_any W_6acdc = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ace0 : bv 32 := 0x00b605b3.
Lemma F_6ace0 : fetch_word AsanUbsan.M.loaded_segments (0x6ad28 : word) = Some W_6ace0.
Proof. vm_refl. Qed.
Lemma D_6ace0 : decode_any W_6ace0 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ace4 : bv 32 := 0x00e60633.
Lemma F_6ace4 : fetch_word AsanUbsan.M.loaded_segments (0x6ad2c : word) = Some W_6ace4.
Proof. vm_refl. Qed.
Lemma D_6ace4 : decode_any W_6ace4 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ace8 : bv 32 := 0xff85f713.
Lemma F_6ace8 : fetch_word AsanUbsan.M.loaded_segments (0x6ad30 : word) = Some W_6ace8.
Proof. vm_refl. Qed.
Lemma D_6ace8 : decode_any W_6ace8 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6acec : bv 32 := 0xff867793.
Lemma F_6acec : fetch_word AsanUbsan.M.loaded_segments (0x6ad34 : word) = Some W_6acec.
Proof. vm_refl. Qed.
Lemma D_6acec : decode_any W_6acec = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6acf0 : bv 32 := 0x00073703.
Lemma F_6acf0 : fetch_word AsanUbsan.M.loaded_segments (0x6ad38 : word) = Some W_6acf0.
Proof. vm_refl. Qed.
Lemma D_6acf0 : decode_any W_6acf0 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6acf4 : bv 32 := 0x0007b783.
Lemma F_6acf4 : fetch_word AsanUbsan.M.loaded_segments (0x6ad3c : word) = Some W_6acf4.
Proof. vm_refl. Qed.
Lemma D_6acf4 : decode_any W_6acf4 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6acf8 : bv 32 := 0x00e7e733.
Lemma F_6acf8 : fetch_word AsanUbsan.M.loaded_segments (0x6ad40 : word) = Some W_6acf8.
Proof. vm_refl. Qed.
Lemma D_6acf8 : decode_any W_6acf8 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6acfc : bv 32 := 0x0a071e63.
Lemma F_6acfc : fetch_word AsanUbsan.M.loaded_segments (0x6ad44 : word) = Some W_6acfc.
Proof. vm_refl. Qed.
Lemma D_6acfc : decode_any W_6acfc = Some (Branch BC_NE 14 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_6adb0 : bv 32 := 0x02049e63.
Lemma F_6adb0 : fetch_word AsanUbsan.M.loaded_segments (0x6adf8 : word) = Some W_6adb0.
Proof. vm_refl. Qed.
Lemma D_6adb0 : decode_any W_6adb0 = Some (Branch BC_NE 9 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_6adec : bv 32 := 0x00050b13.
Lemma F_6adec : fetch_word AsanUbsan.M.loaded_segments (0x6ae34 : word) = Some W_6adec.
Proof. vm_refl. Qed.
Lemma D_6adec : decode_any W_6adec = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6adf0 : bv 32 := 0x00090513.
Lemma F_6adf0 : fetch_word AsanUbsan.M.loaded_segments (0x6ae38 : word) = Some W_6adf0.
Proof. vm_refl. Qed.
Lemma D_6adf0 : decode_any W_6adf0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6adf4 : bv 32 := 0x00048593.
Lemma F_6adf4 : fetch_word AsanUbsan.M.loaded_segments (0x6ae3c : word) = Some W_6adf4.
Proof. vm_refl. Qed.
Lemma D_6adf4 : decode_any W_6adf4 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6adf8 : bv 32 := 0x421170ef.
Lemma F_6adf8 : fetch_word AsanUbsan.M.loaded_segments (0x6ae40 : word) = Some W_6adf8.
Proof. vm_refl. Qed.
Lemma D_6adf8 : decode_any W_6adf8 = Some (Jal 1 97312, 4%Z).
Proof. vm_refl. Qed.

Definition W_6adfc : bv 32 := 0x00050913.
Lemma F_6adfc : fetch_word AsanUbsan.M.loaded_segments (0x6ae44 : word) = Some W_6adfc.
Proof. vm_refl. Qed.
Lemma D_6adfc : decode_any W_6adfc = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ae00 : bv 32 := 0x000b0513.
Lemma F_6ae00 : fetch_word AsanUbsan.M.loaded_segments (0x6ae48 : word) = Some W_6ae00.
Proof. vm_refl. Qed.
Lemma D_6ae00 : decode_any W_6ae00 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ae04 : bv 32 := 0xee090ee3.
Lemma F_6ae04 : fetch_word AsanUbsan.M.loaded_segments (0x6ae4c : word) = Some W_6ae04.
Proof. vm_refl. Qed.
Lemma D_6ae04 : decode_any W_6ae04 = Some (Branch BC_EQ 18 0 7932, 4%Z).
Proof. vm_refl. Qed.

