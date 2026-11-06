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

Definition W_64890 : bv 32 := 0x06048a63.
Lemma F_64890 : fetch_word AsanUbsan.M.loaded_segments (0x648e0 : word) = Some W_64890.
Proof. vm_refl. Qed.
Lemma D_64890 : decode_any W_64890 = Some (Branch BC_EQ 9 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_64894 : bv 32 := 0x000d9597.
Lemma F_64894 : fetch_word AsanUbsan.M.loaded_segments (0x648e4 : word) = Some W_64894.
Proof. vm_refl. Qed.
Lemma D_64894 : decode_any W_64894 = Some (Auipc 11 217, 4%Z).
Proof. vm_refl. Qed.

Definition W_64898 : bv 32 := 0xfd45ba83.
Lemma F_64898 : fetch_word AsanUbsan.M.loaded_segments (0x648e8 : word) = Some W_64898.
Proof. vm_refl. Qed.
Lemma D_64898 : decode_any W_64898 = Some (Load SZ8 true 21 11 4052, 4%Z).
Proof. vm_refl. Qed.

Definition W_6489c : bv 32 := 0x0fbac583.
Lemma F_6489c : fetch_word AsanUbsan.M.loaded_segments (0x648ec : word) = Some W_6489c.
Proof. vm_refl. Qed.
Lemma D_6489c : decode_any W_6489c = Some (Load SZ1 false 11 21 251, 4%Z).
Proof. vm_refl. Qed.

Definition W_648a0 : bv 32 := 0x06058263.
Lemma F_648a0 : fetch_word AsanUbsan.M.loaded_segments (0x648f0 : word) = Some W_648a0.
Proof. vm_refl. Qed.
Lemma D_648a0 : decode_any W_648a0 = Some (Branch BC_EQ 11 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_648a4 : bv 32 := 0x00150493.
Lemma F_648a4 : fetch_word AsanUbsan.M.loaded_segments (0x648f4 : word) = Some W_648a4.
Proof. vm_refl. Qed.
Lemma D_648a4 : decode_any W_648a4 = Some (OpImm ALU_ADD 9 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_648a8 : bv 32 := 0x0934f463.
Lemma F_648a8 : fetch_word AsanUbsan.M.loaded_segments (0x648f8 : word) = Some W_648a8.
Proof. vm_refl. Qed.
Lemma D_648a8 : decode_any W_648a8 = Some (Branch BC_GEU 9 19 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_648ac : bv 32 := 0xfff94593.
Lemma F_648ac : fetch_word AsanUbsan.M.loaded_segments (0x648fc : word) = Some W_648ac.
Proof. vm_refl. Qed.
Lemma D_648ac : decode_any W_648ac = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_648b0 : bv 32 := 0x80040a13.
Lemma F_648b0 : fetch_word AsanUbsan.M.loaded_segments (0x64900 : word) = Some W_648b0.
Proof. vm_refl. Qed.
Lemma D_648b0 : decode_any W_648b0 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_648b4 : bv 32 := 0xfa8a0a13.
Lemma F_648b4 : fetch_word AsanUbsan.M.loaded_segments (0x64904 : word) = Some W_648b4.
Proof. vm_refl. Qed.
Lemma D_648b4 : decode_any W_648b4 = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_648b8 : bv 32 := 0x0895e663.
Lemma F_648b8 : fetch_word AsanUbsan.M.loaded_segments (0x64908 : word) = Some W_648b8.
Proof. vm_refl. Qed.
Lemma D_648b8 : decode_any W_648b8 = Some (Branch BC_LTU 11 9 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_648bc : bv 32 := 0xfbf48593.
Lemma F_648bc : fetch_word AsanUbsan.M.loaded_segments (0x6490c : word) = Some W_648bc.
Proof. vm_refl. Qed.
Lemma D_648bc : decode_any W_648bc = Some (OpImm ALU_ADD 11 9 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_648c0 : bv 32 := 0xfbf00613.
Lemma F_648c0 : fetch_word AsanUbsan.M.loaded_segments (0x64910 : word) = Some W_648c0.
Proof. vm_refl. Qed.
Lemma D_648c0 : decode_any W_648c0 = Some (OpImm ALU_ADD 12 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_648c4 : bv 32 := 0x0eb67863.
Lemma F_648c4 : fetch_word AsanUbsan.M.loaded_segments (0x64914 : word) = Some W_648c4.
Proof. vm_refl. Qed.
Lemma D_648c4 : decode_any W_648c4 = Some (Branch BC_GEU 12 11 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_648c8 : bv 32 := 0x000d9597.
Lemma F_648c8 : fetch_word AsanUbsan.M.loaded_segments (0x64918 : word) = Some W_648c8.
Proof. vm_refl. Qed.
Lemma D_648c8 : decode_any W_648c8 = Some (Auipc 11 217, 4%Z).
Proof. vm_refl. Qed.

Definition W_648cc : bv 32 := 0xfb05b583.
Lemma F_648cc : fetch_word AsanUbsan.M.loaded_segments (0x6491c : word) = Some W_648cc.
Proof. vm_refl. Qed.
Lemma D_648cc : decode_any W_648cc = Some (Load SZ8 true 11 11 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_648d0 : bv 32 := 0x009906b3.
Lemma F_648d0 : fetch_word AsanUbsan.M.loaded_segments (0x64920 : word) = Some W_648d0.
Proof. vm_refl. Qed.
Lemma D_648d0 : decode_any W_648d0 = Some (Op ALU_ADD 13 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_648d4 : bv 32 := 0x0005b603.
Lemma F_648d4 : fetch_word AsanUbsan.M.loaded_segments (0x64924 : word) = Some W_648d4.
Proof. vm_refl. Qed.
Lemma D_648d4 : decode_any W_648d4 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_648d8 : bv 32 := 0x00395593.
Lemma F_648d8 : fetch_word AsanUbsan.M.loaded_segments (0x64928 : word) = Some W_648d8.
Proof. vm_refl. Qed.
Lemma D_648d8 : decode_any W_648d8 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_648dc : bv 32 := 0xfff68693.
Lemma F_648dc : fetch_word AsanUbsan.M.loaded_segments (0x6492c : word) = Some W_648dc.
Proof. vm_refl. Qed.
Lemma D_648dc : decode_any W_648dc = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_648e0 : bv 32 := 0x0036d713.
Lemma F_648e0 : fetch_word AsanUbsan.M.loaded_segments (0x64930 : word) = Some W_648e0.
Proof. vm_refl. Qed.
Lemma D_648e0 : decode_any W_648e0 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_648e4 : bv 32 := 0x00b605b3.
Lemma F_648e4 : fetch_word AsanUbsan.M.loaded_segments (0x64934 : word) = Some W_648e4.
Proof. vm_refl. Qed.
Lemma D_648e4 : decode_any W_648e4 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_648e8 : bv 32 := 0x00e60633.
Lemma F_648e8 : fetch_word AsanUbsan.M.loaded_segments (0x64938 : word) = Some W_648e8.
Proof. vm_refl. Qed.
Lemma D_648e8 : decode_any W_648e8 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_648ec : bv 32 := 0xff85f713.
Lemma F_648ec : fetch_word AsanUbsan.M.loaded_segments (0x6493c : word) = Some W_648ec.
Proof. vm_refl. Qed.
Lemma D_648ec : decode_any W_648ec = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_648f0 : bv 32 := 0xff867793.
Lemma F_648f0 : fetch_word AsanUbsan.M.loaded_segments (0x64940 : word) = Some W_648f0.
Proof. vm_refl. Qed.
Lemma D_648f0 : decode_any W_648f0 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_648f4 : bv 32 := 0x00073703.
Lemma F_648f4 : fetch_word AsanUbsan.M.loaded_segments (0x64944 : word) = Some W_648f4.
Proof. vm_refl. Qed.
Lemma D_648f4 : decode_any W_648f4 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_648f8 : bv 32 := 0x0007b783.
Lemma F_648f8 : fetch_word AsanUbsan.M.loaded_segments (0x64948 : word) = Some W_648f8.
Proof. vm_refl. Qed.
Lemma D_648f8 : decode_any W_648f8 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_648fc : bv 32 := 0x00e7e733.
Lemma F_648fc : fetch_word AsanUbsan.M.loaded_segments (0x6494c : word) = Some W_648fc.
Proof. vm_refl. Qed.
Lemma D_648fc : decode_any W_648fc = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_64900 : bv 32 := 0x0a071e63.
Lemma F_64900 : fetch_word AsanUbsan.M.loaded_segments (0x64950 : word) = Some W_64900.
Proof. vm_refl. Qed.
Lemma D_64900 : decode_any W_64900 = Some (Branch BC_NE 14 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_649b4 : bv 32 := 0x02049e63.
Lemma F_649b4 : fetch_word AsanUbsan.M.loaded_segments (0x64a04 : word) = Some W_649b4.
Proof. vm_refl. Qed.
Lemma D_649b4 : decode_any W_649b4 = Some (Branch BC_NE 9 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_649f0 : bv 32 := 0x00050b13.
Lemma F_649f0 : fetch_word AsanUbsan.M.loaded_segments (0x64a40 : word) = Some W_649f0.
Proof. vm_refl. Qed.
Lemma D_649f0 : decode_any W_649f0 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_649f4 : bv 32 := 0x00090513.
Lemma F_649f4 : fetch_word AsanUbsan.M.loaded_segments (0x64a44 : word) = Some W_649f4.
Proof. vm_refl. Qed.
Lemma D_649f4 : decode_any W_649f4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_649f8 : bv 32 := 0x00048593.
Lemma F_649f8 : fetch_word AsanUbsan.M.loaded_segments (0x64a48 : word) = Some W_649f8.
Proof. vm_refl. Qed.
Lemma D_649f8 : decode_any W_649f8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_649fc : bv 32 := 0x421170ef.
Lemma F_649fc : fetch_word AsanUbsan.M.loaded_segments (0x64a4c : word) = Some W_649fc.
Proof. vm_refl. Qed.
Lemma D_649fc : decode_any W_649fc = Some (Jal 1 97312, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a00 : bv 32 := 0x00050913.
Lemma F_64a00 : fetch_word AsanUbsan.M.loaded_segments (0x64a50 : word) = Some W_64a00.
Proof. vm_refl. Qed.
Lemma D_64a00 : decode_any W_64a00 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a04 : bv 32 := 0x000b0513.
Lemma F_64a04 : fetch_word AsanUbsan.M.loaded_segments (0x64a54 : word) = Some W_64a04.
Proof. vm_refl. Qed.
Lemma D_64a04 : decode_any W_64a04 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a08 : bv 32 := 0xee090ee3.
Lemma F_64a08 : fetch_word AsanUbsan.M.loaded_segments (0x64a58 : word) = Some W_64a08.
Proof. vm_refl. Qed.
Lemma D_64a08 : decode_any W_64a08 = Some (Branch BC_EQ 18 0 7932, 4%Z).
Proof. vm_refl. Qed.
