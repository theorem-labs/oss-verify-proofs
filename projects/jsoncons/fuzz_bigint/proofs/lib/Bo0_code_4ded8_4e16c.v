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

Definition W_4ded8 : bv 32 := 0x81010113.
Lemma F_4ded8 : fetch_word AsanUbsan.M.loaded_segments (0x4ded8 : word) = Some W_4ded8.
Proof. vm_refl. Qed.
Lemma D_4ded8 : decode_any W_4ded8 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dedc : bv 32 := 0x7e113423.
Lemma F_4dedc : fetch_word AsanUbsan.M.loaded_segments (0x4dedc : word) = Some W_4dedc.
Proof. vm_refl. Qed.
Lemma D_4dedc : decode_any W_4dedc = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dee0 : bv 32 := 0x7e813023.
Lemma F_4dee0 : fetch_word AsanUbsan.M.loaded_segments (0x4dee0 : word) = Some W_4dee0.
Proof. vm_refl. Qed.
Lemma D_4dee0 : decode_any W_4dee0 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dee4 : bv 32 := 0x7c913c23.
Lemma F_4dee4 : fetch_word AsanUbsan.M.loaded_segments (0x4dee4 : word) = Some W_4dee4.
Proof. vm_refl. Qed.
Lemma D_4dee4 : decode_any W_4dee4 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dee8 : bv 32 := 0x7d213823.
Lemma F_4dee8 : fetch_word AsanUbsan.M.loaded_segments (0x4dee8 : word) = Some W_4dee8.
Proof. vm_refl. Qed.
Lemma D_4dee8 : decode_any W_4dee8 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_4deec : bv 32 := 0x7d313423.
Lemma F_4deec : fetch_word AsanUbsan.M.loaded_segments (0x4deec : word) = Some W_4deec.
Proof. vm_refl. Qed.
Lemma D_4deec : decode_any W_4deec = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_4def0 : bv 32 := 0x7d413023.
Lemma F_4def0 : fetch_word AsanUbsan.M.loaded_segments (0x4def0 : word) = Some W_4def0.
Proof. vm_refl. Qed.
Lemma D_4def0 : decode_any W_4def0 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_4def4 : bv 32 := 0x7b513c23.
Lemma F_4def4 : fetch_word AsanUbsan.M.loaded_segments (0x4def4 : word) = Some W_4def4.
Proof. vm_refl. Qed.
Lemma D_4def4 : decode_any W_4def4 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_4def8 : bv 32 := 0x7b613823.
Lemma F_4def8 : fetch_word AsanUbsan.M.loaded_segments (0x4def8 : word) = Some W_4def8.
Proof. vm_refl. Qed.
Lemma D_4def8 : decode_any W_4def8 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_4defc : bv 32 := 0x7f010413.
Lemma F_4defc : fetch_word AsanUbsan.M.loaded_segments (0x4defc : word) = Some W_4defc.
Proof. vm_refl. Qed.
Lemma D_4defc : decode_any W_4defc = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df00 : bv 32 := 0xf9010113.
Lemma F_4df00 : fetch_word AsanUbsan.M.loaded_segments (0x4df00 : word) = Some W_4df00.
Proof. vm_refl. Qed.
Lemma D_4df00 : decode_any W_4df00 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df04 : bv 32 := 0x00050913.
Lemma F_4df04 : fetch_word AsanUbsan.M.loaded_segments (0x4df04 : word) = Some W_4df04.
Proof. vm_refl. Qed.
Lemma D_4df04 : decode_any W_4df04 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df08 : bv 32 := 0x44c180ef.
Lemma F_4df08 : fetch_word AsanUbsan.M.loaded_segments (0x4df08 : word) = Some W_4df08.
Proof. vm_refl. Qed.
Lemma D_4df08 : decode_any W_4df08 = Some (Jal 1 99404, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df0c : bv 32 := 0x0a050863.
Lemma F_4df0c : fetch_word AsanUbsan.M.loaded_segments (0x4df0c : word) = Some W_4df0c.
Proof. vm_refl. Qed.
Lemma D_4df0c : decode_any W_4df0c = Some (Branch BC_EQ 10 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df10 : bv 32 := 0x354190ef.
Lemma F_4df10 : fetch_word AsanUbsan.M.loaded_segments (0x4df10 : word) = Some W_4df10.
Proof. vm_refl. Qed.
Lemma D_4df10 : decode_any W_4df10 = Some (Jal 1 103252, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df14 : bv 32 := 0x0008a597.
Lemma F_4df14 : fetch_word AsanUbsan.M.loaded_segments (0x4df14 : word) = Some W_4df14.
Proof. vm_refl. Qed.
Lemma D_4df14 : decode_any W_4df14 = Some (Auipc 11 138, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df18 : bv 32 := 0x38c5b583.
Lemma F_4df18 : fetch_word AsanUbsan.M.loaded_segments (0x4df18 : word) = Some W_4df18.
Proof. vm_refl. Qed.
Lemma D_4df18 : decode_any W_4df18 = Some (Load SZ8 true 11 11 908, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df1c : bv 32 := 0x00050493.
Lemma F_4df1c : fetch_word AsanUbsan.M.loaded_segments (0x4df1c : word) = Some W_4df1c.
Proof. vm_refl. Qed.
Lemma D_4df1c : decode_any W_4df1c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df20 : bv 32 := 0x00090513.
Lemma F_4df20 : fetch_word AsanUbsan.M.loaded_segments (0x4df20 : word) = Some W_4df20.
Proof. vm_refl. Qed.
Lemma D_4df20 : decode_any W_4df20 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df24 : bv 32 := 0x000580e7.
Lemma F_4df24 : fetch_word AsanUbsan.M.loaded_segments (0x4df24 : word) = Some W_4df24.
Proof. vm_refl. Qed.
Lemma D_4df24 : decode_any W_4df24 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df28 : bv 32 := 0x06048463.
Lemma F_4df28 : fetch_word AsanUbsan.M.loaded_segments (0x4df28 : word) = Some W_4df28.
Proof. vm_refl. Qed.
Lemma D_4df28 : decode_any W_4df28 = Some (Branch BC_EQ 9 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df2c : bv 32 := 0x00088597.
Lemma F_4df2c : fetch_word AsanUbsan.M.loaded_segments (0x4df2c : word) = Some W_4df2c.
Proof. vm_refl. Qed.
Lemma D_4df2c : decode_any W_4df2c = Some (Auipc 11 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df30 : bv 32 := 0x58c5b983.
Lemma F_4df30 : fetch_word AsanUbsan.M.loaded_segments (0x4df30 : word) = Some W_4df30.
Proof. vm_refl. Qed.
Lemma D_4df30 : decode_any W_4df30 = Some (Load SZ8 true 19 11 1420, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df34 : bv 32 := 0x0fb9c583.
Lemma F_4df34 : fetch_word AsanUbsan.M.loaded_segments (0x4df34 : word) = Some W_4df34.
Proof. vm_refl. Qed.
Lemma D_4df34 : decode_any W_4df34 = Some (Load SZ1 false 11 19 251, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df38 : bv 32 := 0x04058c63.
Lemma F_4df38 : fetch_word AsanUbsan.M.loaded_segments (0x4df38 : word) = Some W_4df38.
Proof. vm_refl. Qed.
Lemma D_4df38 : decode_any W_4df38 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df3c : bv 32 := 0x00150493.
Lemma F_4df3c : fetch_word AsanUbsan.M.loaded_segments (0x4df3c : word) = Some W_4df3c.
Proof. vm_refl. Qed.
Lemma D_4df3c : decode_any W_4df3c = Some (OpImm ALU_ADD 9 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df40 : bv 32 := 0xfff94593.
Lemma F_4df40 : fetch_word AsanUbsan.M.loaded_segments (0x4df40 : word) = Some W_4df40.
Proof. vm_refl. Qed.
Lemma D_4df40 : decode_any W_4df40 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df44 : bv 32 := 0x80040a13.
Lemma F_4df44 : fetch_word AsanUbsan.M.loaded_segments (0x4df44 : word) = Some W_4df44.
Proof. vm_refl. Qed.
Lemma D_4df44 : decode_any W_4df44 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df48 : bv 32 := 0xfa8a0a13.
Lemma F_4df48 : fetch_word AsanUbsan.M.loaded_segments (0x4df48 : word) = Some W_4df48.
Proof. vm_refl. Qed.
Lemma D_4df48 : decode_any W_4df48 = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df4c : bv 32 := 0x0a95e063.
Lemma F_4df4c : fetch_word AsanUbsan.M.loaded_segments (0x4df4c : word) = Some W_4df4c.
Proof. vm_refl. Qed.
Lemma D_4df4c : decode_any W_4df4c = Some (Branch BC_LTU 11 9 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df50 : bv 32 := 0x04000593.
Lemma F_4df50 : fetch_word AsanUbsan.M.loaded_segments (0x4df50 : word) = Some W_4df50.
Proof. vm_refl. Qed.
Lemma D_4df50 : decode_any W_4df50 = Some (OpImm ALU_ADD 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df54 : bv 32 := 0x10b57263.
Lemma F_4df54 : fetch_word AsanUbsan.M.loaded_segments (0x4df54 : word) = Some W_4df54.
Proof. vm_refl. Qed.
Lemma D_4df54 : decode_any W_4df54 = Some (Branch BC_GEU 10 11 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df58 : bv 32 := 0x00088597.
Lemma F_4df58 : fetch_word AsanUbsan.M.loaded_segments (0x4df58 : word) = Some W_4df58.
Proof. vm_refl. Qed.
Lemma D_4df58 : decode_any W_4df58 = Some (Auipc 11 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df5c : bv 32 := 0x5705b583.
Lemma F_4df5c : fetch_word AsanUbsan.M.loaded_segments (0x4df5c : word) = Some W_4df5c.
Proof. vm_refl. Qed.
Lemma D_4df5c : decode_any W_4df5c = Some (Load SZ8 true 11 11 1392, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df60 : bv 32 := 0x0005b603.
Lemma F_4df60 : fetch_word AsanUbsan.M.loaded_segments (0x4df60 : word) = Some W_4df60.
Proof. vm_refl. Qed.
Lemma D_4df60 : decode_any W_4df60 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df64 : bv 32 := 0x012506b3.
Lemma F_4df64 : fetch_word AsanUbsan.M.loaded_segments (0x4df64 : word) = Some W_4df64.
Proof. vm_refl. Qed.
Lemma D_4df64 : decode_any W_4df64 = Some (Op ALU_ADD 13 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df68 : bv 32 := 0x00395593.
Lemma F_4df68 : fetch_word AsanUbsan.M.loaded_segments (0x4df68 : word) = Some W_4df68.
Proof. vm_refl. Qed.
Lemma D_4df68 : decode_any W_4df68 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df6c : bv 32 := 0x0036d713.
Lemma F_4df6c : fetch_word AsanUbsan.M.loaded_segments (0x4df6c : word) = Some W_4df6c.
Proof. vm_refl. Qed.
Lemma D_4df6c : decode_any W_4df6c = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df70 : bv 32 := 0x00b605b3.
Lemma F_4df70 : fetch_word AsanUbsan.M.loaded_segments (0x4df70 : word) = Some W_4df70.
Proof. vm_refl. Qed.
Lemma D_4df70 : decode_any W_4df70 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df74 : bv 32 := 0x00e60633.
Lemma F_4df74 : fetch_word AsanUbsan.M.loaded_segments (0x4df74 : word) = Some W_4df74.
Proof. vm_refl. Qed.
Lemma D_4df74 : decode_any W_4df74 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df78 : bv 32 := 0xff85f713.
Lemma F_4df78 : fetch_word AsanUbsan.M.loaded_segments (0x4df78 : word) = Some W_4df78.
Proof. vm_refl. Qed.
Lemma D_4df78 : decode_any W_4df78 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df7c : bv 32 := 0xff867793.
Lemma F_4df7c : fetch_word AsanUbsan.M.loaded_segments (0x4df7c : word) = Some W_4df7c.
Proof. vm_refl. Qed.
Lemma D_4df7c : decode_any W_4df7c = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df80 : bv 32 := 0x00073703.
Lemma F_4df80 : fetch_word AsanUbsan.M.loaded_segments (0x4df80 : word) = Some W_4df80.
Proof. vm_refl. Qed.
Lemma D_4df80 : decode_any W_4df80 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df84 : bv 32 := 0x0007b783.
Lemma F_4df84 : fetch_word AsanUbsan.M.loaded_segments (0x4df84 : word) = Some W_4df84.
Proof. vm_refl. Qed.
Lemma D_4df84 : decode_any W_4df84 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df88 : bv 32 := 0x00e7e733.
Lemma F_4df88 : fetch_word AsanUbsan.M.loaded_segments (0x4df88 : word) = Some W_4df88.
Proof. vm_refl. Qed.
Lemma D_4df88 : decode_any W_4df88 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df8c : bv 32 := 0x0c071e63.
Lemma F_4df8c : fetch_word AsanUbsan.M.loaded_segments (0x4df8c : word) = Some W_4df8c.
Proof. vm_refl. Qed.
Lemma D_4df8c : decode_any W_4df8c = Some (Branch BC_NE 14 0 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df90 : bv 32 := 0x07010113.
Lemma F_4df90 : fetch_word AsanUbsan.M.loaded_segments (0x4df90 : word) = Some W_4df90.
Proof. vm_refl. Qed.
Lemma D_4df90 : decode_any W_4df90 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df94 : bv 32 := 0x7e813083.
Lemma F_4df94 : fetch_word AsanUbsan.M.loaded_segments (0x4df94 : word) = Some W_4df94.
Proof. vm_refl. Qed.
Lemma D_4df94 : decode_any W_4df94 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df98 : bv 32 := 0x7e013403.
Lemma F_4df98 : fetch_word AsanUbsan.M.loaded_segments (0x4df98 : word) = Some W_4df98.
Proof. vm_refl. Qed.
Lemma D_4df98 : decode_any W_4df98 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df9c : bv 32 := 0x7d813483.
Lemma F_4df9c : fetch_word AsanUbsan.M.loaded_segments (0x4df9c : word) = Some W_4df9c.
Proof. vm_refl. Qed.
Lemma D_4df9c : decode_any W_4df9c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfa0 : bv 32 := 0x7d013903.
Lemma F_4dfa0 : fetch_word AsanUbsan.M.loaded_segments (0x4dfa0 : word) = Some W_4dfa0.
Proof. vm_refl. Qed.
Lemma D_4dfa0 : decode_any W_4dfa0 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfa4 : bv 32 := 0x7c813983.
Lemma F_4dfa4 : fetch_word AsanUbsan.M.loaded_segments (0x4dfa4 : word) = Some W_4dfa4.
Proof. vm_refl. Qed.
Lemma D_4dfa4 : decode_any W_4dfa4 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfa8 : bv 32 := 0x7c013a03.
Lemma F_4dfa8 : fetch_word AsanUbsan.M.loaded_segments (0x4dfa8 : word) = Some W_4dfa8.
Proof. vm_refl. Qed.
Lemma D_4dfa8 : decode_any W_4dfa8 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfac : bv 32 := 0x7b813a83.
Lemma F_4dfac : fetch_word AsanUbsan.M.loaded_segments (0x4dfac : word) = Some W_4dfac.
Proof. vm_refl. Qed.
Lemma D_4dfac : decode_any W_4dfac = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfb0 : bv 32 := 0x7b013b03.
Lemma F_4dfb0 : fetch_word AsanUbsan.M.loaded_segments (0x4dfb0 : word) = Some W_4dfb0.
Proof. vm_refl. Qed.
Lemma D_4dfb0 : decode_any W_4dfb0 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfb4 : bv 32 := 0x7f010113.
Lemma F_4dfb4 : fetch_word AsanUbsan.M.loaded_segments (0x4dfb4 : word) = Some W_4dfb4.
Proof. vm_refl. Qed.
Lemma D_4dfb4 : decode_any W_4dfb4 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfb8 : bv 32 := 0x00008067.
Lemma F_4dfb8 : fetch_word AsanUbsan.M.loaded_segments (0x4dfb8 : word) = Some W_4dfb8.
Proof. vm_refl. Qed.
Lemma D_4dfb8 : decode_any W_4dfb8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfbc : bv 32 := 0x00090513.
Lemma F_4dfbc : fetch_word AsanUbsan.M.loaded_segments (0x4dfbc : word) = Some W_4dfbc.
Proof. vm_refl. Qed.
Lemma D_4dfbc : decode_any W_4dfbc = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfc0 : bv 32 := 0x07010113.
Lemma F_4dfc0 : fetch_word AsanUbsan.M.loaded_segments (0x4dfc0 : word) = Some W_4dfc0.
Proof. vm_refl. Qed.
Lemma D_4dfc0 : decode_any W_4dfc0 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfc4 : bv 32 := 0x7e813083.
Lemma F_4dfc4 : fetch_word AsanUbsan.M.loaded_segments (0x4dfc4 : word) = Some W_4dfc4.
Proof. vm_refl. Qed.
Lemma D_4dfc4 : decode_any W_4dfc4 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfc8 : bv 32 := 0x7e013403.
Lemma F_4dfc8 : fetch_word AsanUbsan.M.loaded_segments (0x4dfc8 : word) = Some W_4dfc8.
Proof. vm_refl. Qed.
Lemma D_4dfc8 : decode_any W_4dfc8 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfcc : bv 32 := 0x7d813483.
Lemma F_4dfcc : fetch_word AsanUbsan.M.loaded_segments (0x4dfcc : word) = Some W_4dfcc.
Proof. vm_refl. Qed.
Lemma D_4dfcc : decode_any W_4dfcc = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfd0 : bv 32 := 0x7d013903.
Lemma F_4dfd0 : fetch_word AsanUbsan.M.loaded_segments (0x4dfd0 : word) = Some W_4dfd0.
Proof. vm_refl. Qed.
Lemma D_4dfd0 : decode_any W_4dfd0 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfd4 : bv 32 := 0x7c813983.
Lemma F_4dfd4 : fetch_word AsanUbsan.M.loaded_segments (0x4dfd4 : word) = Some W_4dfd4.
Proof. vm_refl. Qed.
Lemma D_4dfd4 : decode_any W_4dfd4 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfd8 : bv 32 := 0x7c013a03.
Lemma F_4dfd8 : fetch_word AsanUbsan.M.loaded_segments (0x4dfd8 : word) = Some W_4dfd8.
Proof. vm_refl. Qed.
Lemma D_4dfd8 : decode_any W_4dfd8 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfdc : bv 32 := 0x7b813a83.
Lemma F_4dfdc : fetch_word AsanUbsan.M.loaded_segments (0x4dfdc : word) = Some W_4dfdc.
Proof. vm_refl. Qed.
Lemma D_4dfdc : decode_any W_4dfdc = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfe0 : bv 32 := 0x7b013b03.
Lemma F_4dfe0 : fetch_word AsanUbsan.M.loaded_segments (0x4dfe0 : word) = Some W_4dfe0.
Proof. vm_refl. Qed.
Lemma D_4dfe0 : decode_any W_4dfe0 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfe4 : bv 32 := 0x7f010113.
Lemma F_4dfe4 : fetch_word AsanUbsan.M.loaded_segments (0x4dfe4 : word) = Some W_4dfe4.
Proof. vm_refl. Qed.
Lemma D_4dfe4 : decode_any W_4dfe4 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfe8 : bv 32 := 0x74c2306f.
Lemma F_4dfe8 : fetch_word AsanUbsan.M.loaded_segments (0x4dfe8 : word) = Some W_4dfe8.
Proof. vm_refl. Qed.
Lemma D_4dfe8 : decode_any W_4dfe8 = Some (Jal 0 145228, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfec : bv 32 := 0x80040593.
Lemma F_4dfec : fetch_word AsanUbsan.M.loaded_segments (0x4dfec : word) = Some W_4dfec.
Proof. vm_refl. Qed.
Lemma D_4dfec : decode_any W_4dfec = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dff0 : bv 32 := 0xfb858593.
Lemma F_4dff0 : fetch_word AsanUbsan.M.loaded_segments (0x4dff0 : word) = Some W_4dff0.
Proof. vm_refl. Qed.
Lemma D_4dff0 : decode_any W_4dff0 = Some (OpImm ALU_ADD 11 11 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dff4 : bv 32 := 0x80040613.
Lemma F_4dff4 : fetch_word AsanUbsan.M.loaded_segments (0x4dff4 : word) = Some W_4dff4.
Proof. vm_refl. Qed.
Lemma D_4dff4 : decode_any W_4dff4 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dff8 : bv 32 := 0xfa860613.
Lemma F_4dff8 : fetch_word AsanUbsan.M.loaded_segments (0x4dff8 : word) = Some W_4dff8.
Proof. vm_refl. Qed.
Lemma D_4dff8 : decode_any W_4dff8 = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dffc : bv 32 := 0x7ff60b13.
Lemma F_4dffc : fetch_word AsanUbsan.M.loaded_segments (0x4dffc : word) = Some W_4dffc.
Proof. vm_refl. Qed.
Lemma D_4dffc : decode_any W_4dffc = Some (OpImm ALU_ADD 22 12 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e000 : bv 32 := 0x000b34a3.
Lemma F_4e000 : fetch_word AsanUbsan.M.loaded_segments (0x4e000 : word) = Some W_4e000.
Proof. vm_refl. Qed.
Lemma D_4e000 : decode_any W_4e000 = Some (Store SZ8 22 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e004 : bv 32 := 0x00ba3023.
Lemma F_4e004 : fetch_word AsanUbsan.M.loaded_segments (0x4e004 : word) = Some W_4e004.
Proof. vm_refl. Qed.
Lemma D_4e004 : decode_any W_4e004 = Some (Store SZ8 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e008 : bv 32 := 0x000a3423.
Lemma F_4e008 : fetch_word AsanUbsan.M.loaded_segments (0x4e008 : word) = Some W_4e008.
Proof. vm_refl. Qed.
Lemma D_4e008 : decode_any W_4e008 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e00c : bv 32 := 0x00050a93.
Lemma F_4e00c : fetch_word AsanUbsan.M.loaded_segments (0x4e00c : word) = Some W_4e00c.
Proof. vm_refl. Qed.
Lemma D_4e00c : decode_any W_4e00c = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e010 : bv 32 := 0x29d320ef.
Lemma F_4e010 : fetch_word AsanUbsan.M.loaded_segments (0x4e010 : word) = Some W_4e010.
Proof. vm_refl. Qed.
Lemma D_4e010 : decode_any W_4e010 = Some (Jal 1 207516, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e014 : bv 32 := 0x00050593.
Lemma F_4e014 : fetch_word AsanUbsan.M.loaded_segments (0x4e014 : word) = Some W_4e014.
Proof. vm_refl. Qed.
Lemma D_4e014 : decode_any W_4e014 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e018 : bv 32 := 0x0219c703.
Lemma F_4e018 : fetch_word AsanUbsan.M.loaded_segments (0x4e018 : word) = Some W_4e018.
Proof. vm_refl. Qed.
Lemma D_4e018 : decode_any W_4e018 = Some (Load SZ1 false 14 19 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e01c : bv 32 := 0x008b34a3.
Lemma F_4e01c : fetch_word AsanUbsan.M.loaded_segments (0x4e01c : word) = Some W_4e01c.
Proof. vm_refl. Qed.
Lemma D_4e01c : decode_any W_4e01c = Some (Store SZ8 22 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e020 : bv 32 := 0x80040513.
Lemma F_4e020 : fetch_word AsanUbsan.M.loaded_segments (0x4e020 : word) = Some W_4e020.
Proof. vm_refl. Qed.
Lemma D_4e020 : decode_any W_4e020 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e024 : bv 32 := 0xfa850513.
Lemma F_4e024 : fetch_word AsanUbsan.M.loaded_segments (0x4e024 : word) = Some W_4e024.
Proof. vm_refl. Qed.
Lemma D_4e024 : decode_any W_4e024 = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e028 : bv 32 := 0x0ff00793.
Lemma F_4e028 : fetch_word AsanUbsan.M.loaded_segments (0x4e028 : word) = Some W_4e028.
Proof. vm_refl. Qed.
Lemma D_4e028 : decode_any W_4e028 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e02c : bv 32 := 0x00040613.
Lemma F_4e02c : fetch_word AsanUbsan.M.loaded_segments (0x4e02c : word) = Some W_4e02c.
Proof. vm_refl. Qed.
Lemma D_4e02c : decode_any W_4e02c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e030 : bv 32 := 0x00000693.
Lemma F_4e030 : fetch_word AsanUbsan.M.loaded_segments (0x4e030 : word) = Some W_4e030.
Proof. vm_refl. Qed.
Lemma D_4e030 : decode_any W_4e030 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e034 : bv 32 := 0x7c9190ef.
Lemma F_4e034 : fetch_word AsanUbsan.M.loaded_segments (0x4e034 : word) = Some W_4e034.
Proof. vm_refl. Qed.
Lemma D_4e034 : decode_any W_4e034 = Some (Jal 1 106440, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e038 : bv 32 := 0x80040613.
Lemma F_4e038 : fetch_word AsanUbsan.M.loaded_segments (0x4e038 : word) = Some W_4e038.
Proof. vm_refl. Qed.
Lemma D_4e038 : decode_any W_4e038 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e03c : bv 32 := 0xfa860613.
Lemma F_4e03c : fetch_word AsanUbsan.M.loaded_segments (0x4e03c : word) = Some W_4e03c.
Proof. vm_refl. Qed.
Lemma D_4e03c : decode_any W_4e03c = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e040 : bv 32 := 0x00090513.
Lemma F_4e040 : fetch_word AsanUbsan.M.loaded_segments (0x4e040 : word) = Some W_4e040.
Proof. vm_refl. Qed.
Lemma D_4e040 : decode_any W_4e040 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e044 : bv 32 := 0x00048593.
Lemma F_4e044 : fetch_word AsanUbsan.M.loaded_segments (0x4e044 : word) = Some W_4e044.
Proof. vm_refl. Qed.
Lemma D_4e044 : decode_any W_4e044 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e048 : bv 32 := 0x56d160ef.
Lemma F_4e048 : fetch_word AsanUbsan.M.loaded_segments (0x4e048 : word) = Some W_4e048.
Proof. vm_refl. Qed.
Lemma D_4e048 : decode_any W_4e048 = Some (Jal 1 93548, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e04c : bv 32 := 0x000a8513.
Lemma F_4e04c : fetch_word AsanUbsan.M.loaded_segments (0x4e04c : word) = Some W_4e04c.
Proof. vm_refl. Qed.
Lemma D_4e04c : decode_any W_4e04c = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e050 : bv 32 := 0x04000593.
Lemma F_4e050 : fetch_word AsanUbsan.M.loaded_segments (0x4e050 : word) = Some W_4e050.
Proof. vm_refl. Qed.
Lemma D_4e050 : decode_any W_4e050 = Some (OpImm ALU_ADD 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e054 : bv 32 := 0xf0bae2e3.
Lemma F_4e054 : fetch_word AsanUbsan.M.loaded_segments (0x4e054 : word) = Some W_4e054.
Proof. vm_refl. Qed.
Lemma D_4e054 : decode_any W_4e054 = Some (Branch BC_LTU 21 11 7940, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e058 : bv 32 := 0x00050a93.
Lemma F_4e058 : fetch_word AsanUbsan.M.loaded_segments (0x4e058 : word) = Some W_4e058.
Proof. vm_refl. Qed.
Lemma D_4e058 : decode_any W_4e058 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e05c : bv 32 := 0x04049263.
Lemma F_4e05c : fetch_word AsanUbsan.M.loaded_segments (0x4e05c : word) = Some W_4e05c.
Proof. vm_refl. Qed.
Lemma D_4e05c : decode_any W_4e05c = Some (Branch BC_NE 9 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e060 : bv 32 := 0xfff00513.
Lemma F_4e060 : fetch_word AsanUbsan.M.loaded_segments (0x4e060 : word) = Some W_4e060.
Proof. vm_refl. Qed.
Lemma D_4e060 : decode_any W_4e060 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e064 : bv 32 := 0xf2dff06f.
Lemma F_4e064 : fetch_word AsanUbsan.M.loaded_segments (0x4e064 : word) = Some W_4e064.
Proof. vm_refl. Qed.
Lemma D_4e064 : decode_any W_4e064 = Some (Jal 0 2096940, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e068 : bv 32 := 0x00050a93.
Lemma F_4e068 : fetch_word AsanUbsan.M.loaded_segments (0x4e068 : word) = Some W_4e068.
Proof. vm_refl. Qed.
Lemma D_4e068 : decode_any W_4e068 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e06c : bv 32 := 0x00060503.
Lemma F_4e06c : fetch_word AsanUbsan.M.loaded_segments (0x4e06c : word) = Some W_4e06c.
Proof. vm_refl. Qed.
Lemma D_4e06c : decode_any W_4e06c = Some (Load SZ1 true 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e070 : bv 32 := 0x0076f693.
Lemma F_4e070 : fetch_word AsanUbsan.M.loaded_segments (0x4e070 : word) = Some W_4e070.
Proof. vm_refl. Qed.
Lemma D_4e070 : decode_any W_4e070 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e074 : bv 32 := 0x00a03733.
Lemma F_4e074 : fetch_word AsanUbsan.M.loaded_segments (0x4e074 : word) = Some W_4e074.
Proof. vm_refl. Qed.
Lemma D_4e074 : decode_any W_4e074 = Some (Op ALU_SLTU 14 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e078 : bv 32 := 0x00a6a533.
Lemma F_4e078 : fetch_word AsanUbsan.M.loaded_segments (0x4e078 : word) = Some W_4e078.
Proof. vm_refl. Qed.
Lemma D_4e078 : decode_any W_4e078 = Some (Op ALU_SLT 10 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e07c : bv 32 := 0x00154513.
Lemma F_4e07c : fetch_word AsanUbsan.M.loaded_segments (0x4e07c : word) = Some W_4e07c.
Proof. vm_refl. Qed.
Lemma D_4e07c : decode_any W_4e07c = Some (OpImm ALU_XOR 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e080 : bv 32 := 0x00a77533.
Lemma F_4e080 : fetch_word AsanUbsan.M.loaded_segments (0x4e080 : word) = Some W_4e080.
Proof. vm_refl. Qed.
Lemma D_4e080 : decode_any W_4e080 = Some (Op ALU_AND 10 14 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e084 : bv 32 := 0x00c5fa63.
Lemma F_4e084 : fetch_word AsanUbsan.M.loaded_segments (0x4e084 : word) = Some W_4e084.
Proof. vm_refl. Qed.
Lemma D_4e084 : decode_any W_4e084 = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e088 : bv 32 := 0x0005c683.
Lemma F_4e088 : fetch_word AsanUbsan.M.loaded_segments (0x4e088 : word) = Some W_4e088.
Proof. vm_refl. Qed.
Lemma D_4e088 : decode_any W_4e088 = Some (Load SZ1 false 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e08c : bv 32 := 0x00158593.
Lemma F_4e08c : fetch_word AsanUbsan.M.loaded_segments (0x4e08c : word) = Some W_4e08c.
Proof. vm_refl. Qed.
Lemma D_4e08c : decode_any W_4e08c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e090 : bv 32 := 0x00a6e533.
Lemma F_4e090 : fetch_word AsanUbsan.M.loaded_segments (0x4e090 : word) = Some W_4e090.
Proof. vm_refl. Qed.
Lemma D_4e090 : decode_any W_4e090 = Some (Op ALU_OR 10 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e094 : bv 32 := 0xfec59ae3.
Lemma F_4e094 : fetch_word AsanUbsan.M.loaded_segments (0x4e094 : word) = Some W_4e094.
Proof. vm_refl. Qed.
Lemma D_4e094 : decode_any W_4e094 = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e098 : bv 32 := 0x0ff57513.
Lemma F_4e098 : fetch_word AsanUbsan.M.loaded_segments (0x4e098 : word) = Some W_4e098.
Proof. vm_refl. Qed.
Lemma D_4e098 : decode_any W_4e098 = Some (OpImm ALU_AND 10 10 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e09c : bv 32 := 0x0c050463.
Lemma F_4e09c : fetch_word AsanUbsan.M.loaded_segments (0x4e09c : word) = Some W_4e09c.
Proof. vm_refl. Qed.
Lemma D_4e09c : decode_any W_4e09c = Some (Branch BC_EQ 10 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0a0 : bv 32 := 0x00090513.
Lemma F_4e0a0 : fetch_word AsanUbsan.M.loaded_segments (0x4e0a0 : word) = Some W_4e0a0.
Proof. vm_refl. Qed.
Lemma D_4e0a0 : decode_any W_4e0a0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0a4 : bv 32 := 0x00048593.
Lemma F_4e0a4 : fetch_word AsanUbsan.M.loaded_segments (0x4e0a4 : word) = Some W_4e0a4.
Proof. vm_refl. Qed.
Lemma D_4e0a4 : decode_any W_4e0a4 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0a8 : bv 32 := 0x2d9130ef.
Lemma F_4e0a8 : fetch_word AsanUbsan.M.loaded_segments (0x4e0a8 : word) = Some W_4e0a8.
Proof. vm_refl. Qed.
Lemma D_4e0a8 : decode_any W_4e0a8 = Some (Jal 1 80600, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0ac : bv 32 := 0x0a050c63.
Lemma F_4e0ac : fetch_word AsanUbsan.M.loaded_segments (0x4e0ac : word) = Some W_4e0ac.
Proof. vm_refl. Qed.
Lemma D_4e0ac : decode_any W_4e0ac = Some (Branch BC_EQ 10 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0b0 : bv 32 := 0x00050913.
Lemma F_4e0b0 : fetch_word AsanUbsan.M.loaded_segments (0x4e0b0 : word) = Some W_4e0b0.
Proof. vm_refl. Qed.
Lemma D_4e0b0 : decode_any W_4e0b0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0b4 : bv 32 := 0xfffc9517.
Lemma F_4e0b4 : fetch_word AsanUbsan.M.loaded_segments (0x4e0b4 : word) = Some W_4e0b4.
Proof. vm_refl. Qed.
Lemma D_4e0b4 : decode_any W_4e0b4 = Some (Auipc 10 1048521, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0b8 : bv 32 := 0x1c350513.
Lemma F_4e0b8 : fetch_word AsanUbsan.M.loaded_segments (0x4e0b8 : word) = Some W_4e0b8.
Proof. vm_refl. Qed.
Lemma D_4e0b8 : decode_any W_4e0b8 = Some (OpImm ALU_ADD 10 10 451, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0bc : bv 32 := 0x6ed1a0ef.
Lemma F_4e0bc : fetch_word AsanUbsan.M.loaded_segments (0x4e0bc : word) = Some W_4e0bc.
Proof. vm_refl. Qed.
Lemma D_4e0bc : decode_any W_4e0bc = Some (Jal 1 110316, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0c0 : bv 32 := 0x0a051263.
Lemma F_4e0c0 : fetch_word AsanUbsan.M.loaded_segments (0x4e0c0 : word) = Some W_4e0c0.
Proof. vm_refl. Qed.
Lemma D_4e0c0 : decode_any W_4e0c0 = Some (Branch BC_NE 10 0 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0c4 : bv 32 := 0x74d1a0ef.
Lemma F_4e0c4 : fetch_word AsanUbsan.M.loaded_segments (0x4e0c4 : word) = Some W_4e0c4.
Proof. vm_refl. Qed.
Lemma D_4e0c4 : decode_any W_4e0c4 = Some (Jal 1 110412, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0c8 : bv 32 := 0x06050263.
Lemma F_4e0c8 : fetch_word AsanUbsan.M.loaded_segments (0x4e0c8 : word) = Some W_4e0c8.
Proof. vm_refl. Qed.
Lemma D_4e0c8 : decode_any W_4e0c8 = Some (Branch BC_EQ 10 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0cc : bv 32 := 0x80040513.
Lemma F_4e0cc : fetch_word AsanUbsan.M.loaded_segments (0x4e0cc : word) = Some W_4e0cc.
Proof. vm_refl. Qed.
Lemma D_4e0cc : decode_any W_4e0cc = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0d0 : bv 32 := 0xfb850513.
Lemma F_4e0d0 : fetch_word AsanUbsan.M.loaded_segments (0x4e0d0 : word) = Some W_4e0d0.
Proof. vm_refl. Qed.
Lemma D_4e0d0 : decode_any W_4e0d0 = Some (OpImm ALU_ADD 10 10 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0d4 : bv 32 := 0x80040593.
Lemma F_4e0d4 : fetch_word AsanUbsan.M.loaded_segments (0x4e0d4 : word) = Some W_4e0d4.
Proof. vm_refl. Qed.
Lemma D_4e0d4 : decode_any W_4e0d4 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0d8 : bv 32 := 0xfa858593.
Lemma F_4e0d8 : fetch_word AsanUbsan.M.loaded_segments (0x4e0d8 : word) = Some W_4e0d8.
Proof. vm_refl. Qed.
Lemma D_4e0d8 : decode_any W_4e0d8 = Some (OpImm ALU_ADD 11 11 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0dc : bv 32 := 0x7ff58b13.
Lemma F_4e0dc : fetch_word AsanUbsan.M.loaded_segments (0x4e0dc : word) = Some W_4e0dc.
Proof. vm_refl. Qed.
Lemma D_4e0dc : decode_any W_4e0dc = Some (OpImm ALU_ADD 22 11 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0e0 : bv 32 := 0x000b34a3.
Lemma F_4e0e0 : fetch_word AsanUbsan.M.loaded_segments (0x4e0e0 : word) = Some W_4e0e0.
Proof. vm_refl. Qed.
Lemma D_4e0e0 : decode_any W_4e0e0 = Some (Store SZ8 22 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0e4 : bv 32 := 0x00aa3023.
Lemma F_4e0e4 : fetch_word AsanUbsan.M.loaded_segments (0x4e0e4 : word) = Some W_4e0e4.
Proof. vm_refl. Qed.
Lemma D_4e0e4 : decode_any W_4e0e4 = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0e8 : bv 32 := 0x000a3423.
Lemma F_4e0e8 : fetch_word AsanUbsan.M.loaded_segments (0x4e0e8 : word) = Some W_4e0e8.
Proof. vm_refl. Qed.
Lemma D_4e0e8 : decode_any W_4e0e8 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0ec : bv 32 := 0x1c1320ef.
Lemma F_4e0ec : fetch_word AsanUbsan.M.loaded_segments (0x4e0ec : word) = Some W_4e0ec.
Proof. vm_refl. Qed.
Lemma D_4e0ec : decode_any W_4e0ec = Some (Jal 1 207296, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0f0 : bv 32 := 0x00050593.
Lemma F_4e0f0 : fetch_word AsanUbsan.M.loaded_segments (0x4e0f0 : word) = Some W_4e0f0.
Proof. vm_refl. Qed.
Lemma D_4e0f0 : decode_any W_4e0f0 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0f4 : bv 32 := 0x0219c703.
Lemma F_4e0f4 : fetch_word AsanUbsan.M.loaded_segments (0x4e0f4 : word) = Some W_4e0f4.
Proof. vm_refl. Qed.
Lemma D_4e0f4 : decode_any W_4e0f4 = Some (Load SZ1 false 14 19 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0f8 : bv 32 := 0x008b34a3.
Lemma F_4e0f8 : fetch_word AsanUbsan.M.loaded_segments (0x4e0f8 : word) = Some W_4e0f8.
Proof. vm_refl. Qed.
Lemma D_4e0f8 : decode_any W_4e0f8 = Some (Store SZ8 22 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0fc : bv 32 := 0x80040513.
Lemma F_4e0fc : fetch_word AsanUbsan.M.loaded_segments (0x4e0fc : word) = Some W_4e0fc.
Proof. vm_refl. Qed.
Lemma D_4e0fc : decode_any W_4e0fc = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e100 : bv 32 := 0xfa850513.
Lemma F_4e100 : fetch_word AsanUbsan.M.loaded_segments (0x4e100 : word) = Some W_4e100.
Proof. vm_refl. Qed.
Lemma D_4e100 : decode_any W_4e100 = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e104 : bv 32 := 0x0ff00793.
Lemma F_4e104 : fetch_word AsanUbsan.M.loaded_segments (0x4e104 : word) = Some W_4e104.
Proof. vm_refl. Qed.
Lemma D_4e104 : decode_any W_4e104 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e108 : bv 32 := 0x00040613.
Lemma F_4e108 : fetch_word AsanUbsan.M.loaded_segments (0x4e108 : word) = Some W_4e108.
Proof. vm_refl. Qed.
Lemma D_4e108 : decode_any W_4e108 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e10c : bv 32 := 0x00000693.
Lemma F_4e10c : fetch_word AsanUbsan.M.loaded_segments (0x4e10c : word) = Some W_4e10c.
Proof. vm_refl. Qed.
Lemma D_4e10c : decode_any W_4e10c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e110 : bv 32 := 0x6ed190ef.
Lemma F_4e110 : fetch_word AsanUbsan.M.loaded_segments (0x4e110 : word) = Some W_4e110.
Proof. vm_refl. Qed.
Lemma D_4e110 : decode_any W_4e110 = Some (Jal 1 106220, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e114 : bv 32 := 0x80040513.
Lemma F_4e114 : fetch_word AsanUbsan.M.loaded_segments (0x4e114 : word) = Some W_4e114.
Proof. vm_refl. Qed.
Lemma D_4e114 : decode_any W_4e114 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e118 : bv 32 := 0xfa850513.
Lemma F_4e118 : fetch_word AsanUbsan.M.loaded_segments (0x4e118 : word) = Some W_4e118.
Proof. vm_refl. Qed.
Lemma D_4e118 : decode_any W_4e118 = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e11c : bv 32 := 0x1fc1b0ef.
Lemma F_4e11c : fetch_word AsanUbsan.M.loaded_segments (0x4e11c : word) = Some W_4e11c.
Proof. vm_refl. Qed.
Lemma D_4e11c : decode_any W_4e11c = Some (Jal 1 111100, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e120 : bv 32 := 0x00040993.
Lemma F_4e120 : fetch_word AsanUbsan.M.loaded_segments (0x4e120 : word) = Some W_4e120.
Proof. vm_refl. Qed.
Lemma D_4e120 : decode_any W_4e120 = Some (OpImm ALU_ADD 19 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e124 : bv 32 := 0x00050663.
Lemma F_4e124 : fetch_word AsanUbsan.M.loaded_segments (0x4e124 : word) = Some W_4e124.
Proof. vm_refl. Qed.
Lemma D_4e124 : decode_any W_4e124 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e128 : bv 32 := 0x03c0006f.
Lemma F_4e128 : fetch_word AsanUbsan.M.loaded_segments (0x4e128 : word) = Some W_4e128.
Proof. vm_refl. Qed.
Lemma D_4e128 : decode_any W_4e128 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e12c : bv 32 := 0x00040993.
Lemma F_4e12c : fetch_word AsanUbsan.M.loaded_segments (0x4e12c : word) = Some W_4e12c.
Proof. vm_refl. Qed.
Lemma D_4e12c : decode_any W_4e12c = Some (OpImm ALU_ADD 19 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e130 : bv 32 := 0x17d320ef.
Lemma F_4e130 : fetch_word AsanUbsan.M.loaded_segments (0x4e130 : word) = Some W_4e130.
Proof. vm_refl. Qed.
Lemma D_4e130 : decode_any W_4e130 = Some (Jal 1 207228, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e134 : bv 32 := 0xfffc2597.
Lemma F_4e134 : fetch_word AsanUbsan.M.loaded_segments (0x4e134 : word) = Some W_4e134.
Proof. vm_refl. Qed.
Lemma D_4e134 : decode_any W_4e134 = Some (Auipc 11 1048514, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e138 : bv 32 := 0x2d45b583.
Lemma F_4e138 : fetch_word AsanUbsan.M.loaded_segments (0x4e138 : word) = Some W_4e138.
Proof. vm_refl. Qed.
Lemma D_4e138 : decode_any W_4e138 = Some (Load SZ8 true 11 11 724, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e13c : bv 32 := 0x00ba3023.
Lemma F_4e13c : fetch_word AsanUbsan.M.loaded_segments (0x4e13c : word) = Some W_4e13c.
Proof. vm_refl. Qed.
Lemma D_4e13c : decode_any W_4e13c = Some (Store SZ8 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e140 : bv 32 := 0x80040613.
Lemma F_4e140 : fetch_word AsanUbsan.M.loaded_segments (0x4e140 : word) = Some W_4e140.
Proof. vm_refl. Qed.
Lemma D_4e140 : decode_any W_4e140 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e144 : bv 32 := 0xfa860613.
Lemma F_4e144 : fetch_word AsanUbsan.M.loaded_segments (0x4e144 : word) = Some W_4e144.
Proof. vm_refl. Qed.
Lemma D_4e144 : decode_any W_4e144 = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e148 : bv 32 := 0x00098593.
Lemma F_4e148 : fetch_word AsanUbsan.M.loaded_segments (0x4e148 : word) = Some W_4e148.
Proof. vm_refl. Qed.
Lemma D_4e148 : decode_any W_4e148 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e14c : bv 32 := 0x00090693.
Lemma F_4e14c : fetch_word AsanUbsan.M.loaded_segments (0x4e14c : word) = Some W_4e14c.
Proof. vm_refl. Qed.
Lemma D_4e14c : decode_any W_4e14c = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e150 : bv 32 := 0x00000713.
Lemma F_4e150 : fetch_word AsanUbsan.M.loaded_segments (0x4e150 : word) = Some W_4e150.
Proof. vm_refl. Qed.
Lemma D_4e150 : decode_any W_4e150 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e154 : bv 32 := 0x00048793.
Lemma F_4e154 : fetch_word AsanUbsan.M.loaded_segments (0x4e154 : word) = Some W_4e154.
Proof. vm_refl. Qed.
Lemma D_4e154 : decode_any W_4e154 = Some (OpImm ALU_ADD 15 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e158 : bv 32 := 0x00000813.
Lemma F_4e158 : fetch_word AsanUbsan.M.loaded_segments (0x4e158 : word) = Some W_4e158.
Proof. vm_refl. Qed.
Lemma D_4e158 : decode_any W_4e158 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e15c : bv 32 := 0x00000893.
Lemma F_4e15c : fetch_word AsanUbsan.M.loaded_segments (0x4e15c : word) = Some W_4e15c.
Proof. vm_refl. Qed.
Lemma D_4e15c : decode_any W_4e15c = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e160 : bv 32 := 0x1ac170ef.
Lemma F_4e160 : fetch_word AsanUbsan.M.loaded_segments (0x4e160 : word) = Some W_4e160.
Proof. vm_refl. Qed.
Lemma D_4e160 : decode_any W_4e160 = Some (Jal 1 94636, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e164 : bv 32 := 0x000a8513.
Lemma F_4e164 : fetch_word AsanUbsan.M.loaded_segments (0x4e164 : word) = Some W_4e164.
Proof. vm_refl. Qed.
Lemma D_4e164 : decode_any W_4e164 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e168 : bv 32 := 0xe29ff06f.
Lemma F_4e168 : fetch_word AsanUbsan.M.loaded_segments (0x4e168 : word) = Some W_4e168.
Proof. vm_refl. Qed.
Lemma D_4e168 : decode_any W_4e168 = Some (Jal 0 2096680, 4%Z).
Proof. vm_refl. Qed.
