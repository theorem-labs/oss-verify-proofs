(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.cjson.cjson_read_fuzzer.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_9a970 : bv 32 := 0x0035f693.
Lemma F_9a970 : fetch_word AsanUbsan.M.loaded_segments (0x9a970 : word) = Some W_9a970.
Proof. vm_refl. Qed.
Lemma D_9a970 : decode_any W_9a970 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a974 : bv 32 := 0x10068863.
Lemma F_9a974 : fetch_word AsanUbsan.M.loaded_segments (0x9a974 : word) = Some W_9a974.
Proof. vm_refl. Qed.
Lemma D_9a974 : decode_any W_9a974 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a978 : bv 32 := 0x02060e63.
Lemma F_9a978 : fetch_word AsanUbsan.M.loaded_segments (0x9a978 : word) = Some W_9a978.
Proof. vm_refl. Qed.
Lemma D_9a978 : decode_any W_9a978 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a97c : bv 32 := 0x00158713.
Lemma F_9a97c : fetch_word AsanUbsan.M.loaded_segments (0x9a97c : word) = Some W_9a97c.
Proof. vm_refl. Qed.
Lemma D_9a97c : decode_any W_9a97c = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a980 : bv 32 := 0x00100793.
Lemma F_9a980 : fetch_word AsanUbsan.M.loaded_segments (0x9a980 : word) = Some W_9a980.
Proof. vm_refl. Qed.
Lemma D_9a980 : decode_any W_9a980 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a984 : bv 32 := 0x00050693.
Lemma F_9a984 : fetch_word AsanUbsan.M.loaded_segments (0x9a984 : word) = Some W_9a984.
Proof. vm_refl. Qed.
Lemma D_9a984 : decode_any W_9a984 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a988 : bv 32 := 0x0005c883.
Lemma F_9a988 : fetch_word AsanUbsan.M.loaded_segments (0x9a988 : word) = Some W_9a988.
Proof. vm_refl. Qed.
Lemma D_9a988 : decode_any W_9a988 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a98c : bv 32 := 0x00060813.
Lemma F_9a98c : fetch_word AsanUbsan.M.loaded_segments (0x9a98c : word) = Some W_9a98c.
Proof. vm_refl. Qed.
Lemma D_9a98c : decode_any W_9a98c = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a990 : bv 32 := 0x00158593.
Lemma F_9a990 : fetch_word AsanUbsan.M.loaded_segments (0x9a990 : word) = Some W_9a990.
Proof. vm_refl. Qed.
Lemma D_9a990 : decode_any W_9a990 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a994 : bv 32 := 0x00377293.
Lemma F_9a994 : fetch_word AsanUbsan.M.loaded_segments (0x9a994 : word) = Some W_9a994.
Proof. vm_refl. Qed.
Lemma D_9a994 : decode_any W_9a994 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a998 : bv 32 := 0x01168023.
Lemma F_9a998 : fetch_word AsanUbsan.M.loaded_segments (0x9a998 : word) = Some W_9a998.
Proof. vm_refl. Qed.
Lemma D_9a998 : decode_any W_9a998 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a99c : bv 32 := 0x00168693.
Lemma F_9a99c : fetch_word AsanUbsan.M.loaded_segments (0x9a99c : word) = Some W_9a99c.
Proof. vm_refl. Qed.
Lemma D_9a99c : decode_any W_9a99c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a9a0 : bv 32 := 0xfff60613.
Lemma F_9a9a0 : fetch_word AsanUbsan.M.loaded_segments (0x9a9a0 : word) = Some W_9a9a0.
Proof. vm_refl. Qed.
Lemma D_9a9a0 : decode_any W_9a9a0 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a9a4 : bv 32 := 0x00028a63.
Lemma F_9a9a4 : fetch_word AsanUbsan.M.loaded_segments (0x9a9a4 : word) = Some W_9a9a4.
Proof. vm_refl. Qed.
Lemma D_9a9a4 : decode_any W_9a9a4 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a9a8 : bv 32 := 0x00170713.
Lemma F_9a9a8 : fetch_word AsanUbsan.M.loaded_segments (0x9a9a8 : word) = Some W_9a9a8.
Proof. vm_refl. Qed.
Lemma D_9a9a8 : decode_any W_9a9a8 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a9ac : bv 32 := 0xfcf81ee3.
Lemma F_9a9ac : fetch_word AsanUbsan.M.loaded_segments (0x9a9ac : word) = Some W_9a9ac.
Proof. vm_refl. Qed.
Lemma D_9a9ac : decode_any W_9a9ac = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a9b0 : bv 32 := 0x0080006f.
Lemma F_9a9b0 : fetch_word AsanUbsan.M.loaded_segments (0x9a9b0 : word) = Some W_9a9b0.
Proof. vm_refl. Qed.
Lemma D_9a9b0 : decode_any W_9a9b0 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a9b4 : bv 32 := 0x00050693.
Lemma F_9a9b4 : fetch_word AsanUbsan.M.loaded_segments (0x9a9b4 : word) = Some W_9a9b4.
Proof. vm_refl. Qed.
Lemma D_9a9b4 : decode_any W_9a9b4 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a9b8 : bv 32 := 0x0036f793.
Lemma F_9a9b8 : fetch_word AsanUbsan.M.loaded_segments (0x9a9b8 : word) = Some W_9a9b8.
Proof. vm_refl. Qed.
Lemma D_9a9b8 : decode_any W_9a9b8 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a9bc : bv 32 := 0x0c078a63.
Lemma F_9a9bc : fetch_word AsanUbsan.M.loaded_segments (0x9a9bc : word) = Some W_9a9bc.
Proof. vm_refl. Qed.
Lemma D_9a9bc : decode_any W_9a9bc = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a9c0 : bv 32 := 0x02000713.
Lemma F_9a9c0 : fetch_word AsanUbsan.M.loaded_segments (0x9a9c0 : word) = Some W_9a9c0.
Proof. vm_refl. Qed.
Lemma D_9a9c0 : decode_any W_9a9c0 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a9c4 : bv 32 := 0x02e67063.
Lemma F_9a9c4 : fetch_word AsanUbsan.M.loaded_segments (0x9a9c4 : word) = Some W_9a9c4.
Proof. vm_refl. Qed.
Lemma D_9a9c4 : decode_any W_9a9c4 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a9c8 : bv 32 := 0x01000713.
Lemma F_9a9c8 : fetch_word AsanUbsan.M.loaded_segments (0x9a9c8 : word) = Some W_9a9c8.
Proof. vm_refl. Qed.
Lemma D_9a9c8 : decode_any W_9a9c8 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a9cc : bv 32 := 0x24e67863.
Lemma F_9a9cc : fetch_word AsanUbsan.M.loaded_segments (0x9a9cc : word) = Some W_9a9cc.
Proof. vm_refl. Qed.
Lemma D_9a9cc : decode_any W_9a9cc = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a9d0 : bv 32 := 0x00867713.
Lemma F_9a9d0 : fetch_word AsanUbsan.M.loaded_segments (0x9a9d0 : word) = Some W_9a9d0.
Proof. vm_refl. Qed.
Lemma D_9a9d0 : decode_any W_9a9d0 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a9d4 : bv 32 := 0x2c071e63.
Lemma F_9a9d4 : fetch_word AsanUbsan.M.loaded_segments (0x9a9d4 : word) = Some W_9a9d4.
Proof. vm_refl. Qed.
Lemma D_9a9d4 : decode_any W_9a9d4 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a9d8 : bv 32 := 0x00467713.
Lemma F_9a9d8 : fetch_word AsanUbsan.M.loaded_segments (0x9a9d8 : word) = Some W_9a9d8.
Proof. vm_refl. Qed.
Lemma D_9a9d8 : decode_any W_9a9d8 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a9dc : bv 32 := 0x32071463.
Lemma F_9a9dc : fetch_word AsanUbsan.M.loaded_segments (0x9a9dc : word) = Some W_9a9dc.
Proof. vm_refl. Qed.
Lemma D_9a9dc : decode_any W_9a9dc = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a9e0 : bv 32 := 0x3500006f.
Lemma F_9a9e0 : fetch_word AsanUbsan.M.loaded_segments (0x9a9e0 : word) = Some W_9a9e0.
Proof. vm_refl. Qed.
Lemma D_9a9e0 : decode_any W_9a9e0 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a9e4 : bv 32 := 0x0005a703.
Lemma F_9a9e4 : fetch_word AsanUbsan.M.loaded_segments (0x9a9e4 : word) = Some W_9a9e4.
Proof. vm_refl. Qed.
Lemma D_9a9e4 : decode_any W_9a9e4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a9e8 : bv 32 := 0x00300813.
Lemma F_9a9e8 : fetch_word AsanUbsan.M.loaded_segments (0x9a9e8 : word) = Some W_9a9e8.
Proof. vm_refl. Qed.
Lemma D_9a9e8 : decode_any W_9a9e8 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a9ec : bv 32 := 0x11078e63.
Lemma F_9a9ec : fetch_word AsanUbsan.M.loaded_segments (0x9a9ec : word) = Some W_9a9ec.
Proof. vm_refl. Qed.
Lemma D_9a9ec : decode_any W_9a9ec = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a9f0 : bv 32 := 0x00200813.
Lemma F_9a9f0 : fetch_word AsanUbsan.M.loaded_segments (0x9a9f0 : word) = Some W_9a9f0.
Proof. vm_refl. Qed.
Lemma D_9a9f0 : decode_any W_9a9f0 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a9f4 : bv 32 := 0x19079c63.
Lemma F_9a9f4 : fetch_word AsanUbsan.M.loaded_segments (0x9a9f4 : word) = Some W_9a9f4.
Proof. vm_refl. Qed.
Lemma D_9a9f4 : decode_any W_9a9f4 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a9f8 : bv 32 := 0x00875793.
Lemma F_9a9f8 : fetch_word AsanUbsan.M.loaded_segments (0x9a9f8 : word) = Some W_9a9f8.
Proof. vm_refl. Qed.
Lemma D_9a9f8 : decode_any W_9a9f8 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a9fc : bv 32 := 0xffe60613.
Lemma F_9a9fc : fetch_word AsanUbsan.M.loaded_segments (0x9a9fc : word) = Some W_9a9fc.
Proof. vm_refl. Qed.
Lemma D_9a9fc : decode_any W_9a9fc = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa00 : bv 32 := 0x00e68023.
Lemma F_9aa00 : fetch_word AsanUbsan.M.loaded_segments (0x9aa00 : word) = Some W_9aa00.
Proof. vm_refl. Qed.
Lemma D_9aa00 : decode_any W_9aa00 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa04 : bv 32 := 0x00f680a3.
Lemma F_9aa04 : fetch_word AsanUbsan.M.loaded_segments (0x9aa04 : word) = Some W_9aa04.
Proof. vm_refl. Qed.
Lemma D_9aa04 : decode_any W_9aa04 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa08 : bv 32 := 0x00268693.
Lemma F_9aa08 : fetch_word AsanUbsan.M.loaded_segments (0x9aa08 : word) = Some W_9aa08.
Proof. vm_refl. Qed.
Lemma D_9aa08 : decode_any W_9aa08 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa0c : bv 32 := 0x01058593.
Lemma F_9aa0c : fetch_word AsanUbsan.M.loaded_segments (0x9aa0c : word) = Some W_9aa0c.
Proof. vm_refl. Qed.
Lemma D_9aa0c : decode_any W_9aa0c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa10 : bv 32 := 0x01100793.
Lemma F_9aa10 : fetch_word AsanUbsan.M.loaded_segments (0x9aa10 : word) = Some W_9aa10.
Proof. vm_refl. Qed.
Lemma D_9aa10 : decode_any W_9aa10 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa14 : bv 32 := 0x0107581b.
Lemma F_9aa14 : fetch_word AsanUbsan.M.loaded_segments (0x9aa14 : word) = Some W_9aa14.
Proof. vm_refl. Qed.
Lemma D_9aa14 : decode_any W_9aa14 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa18 : bv 32 := 0xff45a883.
Lemma F_9aa18 : fetch_word AsanUbsan.M.loaded_segments (0x9aa18 : word) = Some W_9aa18.
Proof. vm_refl. Qed.
Lemma D_9aa18 : decode_any W_9aa18 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa1c : bv 32 := 0xff85a283.
Lemma F_9aa1c : fetch_word AsanUbsan.M.loaded_segments (0x9aa1c : word) = Some W_9aa1c.
Proof. vm_refl. Qed.
Lemma D_9aa1c : decode_any W_9aa1c = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa20 : bv 32 := 0xffc5a303.
Lemma F_9aa20 : fetch_word AsanUbsan.M.loaded_segments (0x9aa20 : word) = Some W_9aa20.
Proof. vm_refl. Qed.
Lemma D_9aa20 : decode_any W_9aa20 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa24 : bv 32 := 0x0005a703.
Lemma F_9aa24 : fetch_word AsanUbsan.M.loaded_segments (0x9aa24 : word) = Some W_9aa24.
Proof. vm_refl. Qed.
Lemma D_9aa24 : decode_any W_9aa24 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa28 : bv 32 := 0x01089393.
Lemma F_9aa28 : fetch_word AsanUbsan.M.loaded_segments (0x9aa28 : word) = Some W_9aa28.
Proof. vm_refl. Qed.
Lemma D_9aa28 : decode_any W_9aa28 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa2c : bv 32 := 0x0108d89b.
Lemma F_9aa2c : fetch_word AsanUbsan.M.loaded_segments (0x9aa2c : word) = Some W_9aa2c.
Proof. vm_refl. Qed.
Lemma D_9aa2c : decode_any W_9aa2c = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa30 : bv 32 := 0x0103e833.
Lemma F_9aa30 : fetch_word AsanUbsan.M.loaded_segments (0x9aa30 : word) = Some W_9aa30.
Proof. vm_refl. Qed.
Lemma D_9aa30 : decode_any W_9aa30 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa34 : bv 32 := 0x01029393.
Lemma F_9aa34 : fetch_word AsanUbsan.M.loaded_segments (0x9aa34 : word) = Some W_9aa34.
Proof. vm_refl. Qed.
Lemma D_9aa34 : decode_any W_9aa34 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa38 : bv 32 := 0x0102d29b.
Lemma F_9aa38 : fetch_word AsanUbsan.M.loaded_segments (0x9aa38 : word) = Some W_9aa38.
Proof. vm_refl. Qed.
Lemma D_9aa38 : decode_any W_9aa38 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa3c : bv 32 := 0x0113e8b3.
Lemma F_9aa3c : fetch_word AsanUbsan.M.loaded_segments (0x9aa3c : word) = Some W_9aa3c.
Proof. vm_refl. Qed.
Lemma D_9aa3c : decode_any W_9aa3c = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa40 : bv 32 := 0x01031393.
Lemma F_9aa40 : fetch_word AsanUbsan.M.loaded_segments (0x9aa40 : word) = Some W_9aa40.
Proof. vm_refl. Qed.
Lemma D_9aa40 : decode_any W_9aa40 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa44 : bv 32 := 0x0103531b.
Lemma F_9aa44 : fetch_word AsanUbsan.M.loaded_segments (0x9aa44 : word) = Some W_9aa44.
Proof. vm_refl. Qed.
Lemma D_9aa44 : decode_any W_9aa44 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa48 : bv 32 := 0x0053e2b3.
Lemma F_9aa48 : fetch_word AsanUbsan.M.loaded_segments (0x9aa48 : word) = Some W_9aa48.
Proof. vm_refl. Qed.
Lemma D_9aa48 : decode_any W_9aa48 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa4c : bv 32 := 0x01071393.
Lemma F_9aa4c : fetch_word AsanUbsan.M.loaded_segments (0x9aa4c : word) = Some W_9aa4c.
Proof. vm_refl. Qed.
Lemma D_9aa4c : decode_any W_9aa4c = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa50 : bv 32 := 0x0063e333.
Lemma F_9aa50 : fetch_word AsanUbsan.M.loaded_segments (0x9aa50 : word) = Some W_9aa50.
Proof. vm_refl. Qed.
Lemma D_9aa50 : decode_any W_9aa50 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa54 : bv 32 := 0xff060613.
Lemma F_9aa54 : fetch_word AsanUbsan.M.loaded_segments (0x9aa54 : word) = Some W_9aa54.
Proof. vm_refl. Qed.
Lemma D_9aa54 : decode_any W_9aa54 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa58 : bv 32 := 0x0106a023.
Lemma F_9aa58 : fetch_word AsanUbsan.M.loaded_segments (0x9aa58 : word) = Some W_9aa58.
Proof. vm_refl. Qed.
Lemma D_9aa58 : decode_any W_9aa58 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa5c : bv 32 := 0x0116a223.
Lemma F_9aa5c : fetch_word AsanUbsan.M.loaded_segments (0x9aa5c : word) = Some W_9aa5c.
Proof. vm_refl. Qed.
Lemma D_9aa5c : decode_any W_9aa5c = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa60 : bv 32 := 0x0056a423.
Lemma F_9aa60 : fetch_word AsanUbsan.M.loaded_segments (0x9aa60 : word) = Some W_9aa60.
Proof. vm_refl. Qed.
Lemma D_9aa60 : decode_any W_9aa60 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa64 : bv 32 := 0x0066a623.
Lemma F_9aa64 : fetch_word AsanUbsan.M.loaded_segments (0x9aa64 : word) = Some W_9aa64.
Proof. vm_refl. Qed.
Lemma D_9aa64 : decode_any W_9aa64 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa68 : bv 32 := 0x01068693.
Lemma F_9aa68 : fetch_word AsanUbsan.M.loaded_segments (0x9aa68 : word) = Some W_9aa68.
Proof. vm_refl. Qed.
Lemma D_9aa68 : decode_any W_9aa68 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa6c : bv 32 := 0x01058593.
Lemma F_9aa6c : fetch_word AsanUbsan.M.loaded_segments (0x9aa6c : word) = Some W_9aa6c.
Proof. vm_refl. Qed.
Lemma D_9aa6c : decode_any W_9aa6c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa70 : bv 32 := 0xfac7e2e3.
Lemma F_9aa70 : fetch_word AsanUbsan.M.loaded_segments (0x9aa70 : word) = Some W_9aa70.
Proof. vm_refl. Qed.
Lemma D_9aa70 : decode_any W_9aa70 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa74 : bv 32 := 0xff258593.
Lemma F_9aa74 : fetch_word AsanUbsan.M.loaded_segments (0x9aa74 : word) = Some W_9aa74.
Proof. vm_refl. Qed.
Lemma D_9aa74 : decode_any W_9aa74 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa78 : bv 32 := 0x01000713.
Lemma F_9aa78 : fetch_word AsanUbsan.M.loaded_segments (0x9aa78 : word) = Some W_9aa78.
Proof. vm_refl. Qed.
Lemma D_9aa78 : decode_any W_9aa78 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa7c : bv 32 := 0xf4e66ae3.
Lemma F_9aa7c : fetch_word AsanUbsan.M.loaded_segments (0x9aa7c : word) = Some W_9aa7c.
Proof. vm_refl. Qed.
Lemma D_9aa7c : decode_any W_9aa7c = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa80 : bv 32 := 0x19c0006f.
Lemma F_9aa80 : fetch_word AsanUbsan.M.loaded_segments (0x9aa80 : word) = Some W_9aa80.
Proof. vm_refl. Qed.
Lemma D_9aa80 : decode_any W_9aa80 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa84 : bv 32 := 0x00050693.
Lemma F_9aa84 : fetch_word AsanUbsan.M.loaded_segments (0x9aa84 : word) = Some W_9aa84.
Proof. vm_refl. Qed.
Lemma D_9aa84 : decode_any W_9aa84 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa88 : bv 32 := 0x00357793.
Lemma F_9aa88 : fetch_word AsanUbsan.M.loaded_segments (0x9aa88 : word) = Some W_9aa88.
Proof. vm_refl. Qed.
Lemma D_9aa88 : decode_any W_9aa88 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa8c : bv 32 := 0xf2079ae3.
Lemma F_9aa8c : fetch_word AsanUbsan.M.loaded_segments (0x9aa8c : word) = Some W_9aa8c.
Proof. vm_refl. Qed.
Lemma D_9aa8c : decode_any W_9aa8c = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa90 : bv 32 := 0x01000713.
Lemma F_9aa90 : fetch_word AsanUbsan.M.loaded_segments (0x9aa90 : word) = Some W_9aa90.
Proof. vm_refl. Qed.
Lemma D_9aa90 : decode_any W_9aa90 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa94 : bv 32 := 0x02e66c63.
Lemma F_9aa94 : fetch_word AsanUbsan.M.loaded_segments (0x9aa94 : word) = Some W_9aa94.
Proof. vm_refl. Qed.
Lemma D_9aa94 : decode_any W_9aa94 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa98 : bv 32 := 0x00f00713.
Lemma F_9aa98 : fetch_word AsanUbsan.M.loaded_segments (0x9aa98 : word) = Some W_9aa98.
Proof. vm_refl. Qed.
Lemma D_9aa98 : decode_any W_9aa98 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aa9c : bv 32 := 0x0005a783.
Lemma F_9aa9c : fetch_word AsanUbsan.M.loaded_segments (0x9aa9c : word) = Some W_9aa9c.
Proof. vm_refl. Qed.
Lemma D_9aa9c : decode_any W_9aa9c = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aaa0 : bv 32 := 0x0045a803.
Lemma F_9aaa0 : fetch_word AsanUbsan.M.loaded_segments (0x9aaa0 : word) = Some W_9aaa0.
Proof. vm_refl. Qed.
Lemma D_9aaa0 : decode_any W_9aaa0 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aaa4 : bv 32 := 0x0085a883.
Lemma F_9aaa4 : fetch_word AsanUbsan.M.loaded_segments (0x9aaa4 : word) = Some W_9aaa4.
Proof. vm_refl. Qed.
Lemma D_9aaa4 : decode_any W_9aaa4 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aaa8 : bv 32 := 0x00c5a283.
Lemma F_9aaa8 : fetch_word AsanUbsan.M.loaded_segments (0x9aaa8 : word) = Some W_9aaa8.
Proof. vm_refl. Qed.
Lemma D_9aaa8 : decode_any W_9aaa8 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aaac : bv 32 := 0x01058593.
Lemma F_9aaac : fetch_word AsanUbsan.M.loaded_segments (0x9aaac : word) = Some W_9aaac.
Proof. vm_refl. Qed.
Lemma D_9aaac : decode_any W_9aaac = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aab0 : bv 32 := 0xff060613.
Lemma F_9aab0 : fetch_word AsanUbsan.M.loaded_segments (0x9aab0 : word) = Some W_9aab0.
Proof. vm_refl. Qed.
Lemma D_9aab0 : decode_any W_9aab0 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aab4 : bv 32 := 0x00f6a023.
Lemma F_9aab4 : fetch_word AsanUbsan.M.loaded_segments (0x9aab4 : word) = Some W_9aab4.
Proof. vm_refl. Qed.
Lemma D_9aab4 : decode_any W_9aab4 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aab8 : bv 32 := 0x0106a223.
Lemma F_9aab8 : fetch_word AsanUbsan.M.loaded_segments (0x9aab8 : word) = Some W_9aab8.
Proof. vm_refl. Qed.
Lemma D_9aab8 : decode_any W_9aab8 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aabc : bv 32 := 0x0116a423.
Lemma F_9aabc : fetch_word AsanUbsan.M.loaded_segments (0x9aabc : word) = Some W_9aabc.
Proof. vm_refl. Qed.
Lemma D_9aabc : decode_any W_9aabc = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aac0 : bv 32 := 0x0056a623.
Lemma F_9aac0 : fetch_word AsanUbsan.M.loaded_segments (0x9aac0 : word) = Some W_9aac0.
Proof. vm_refl. Qed.
Lemma D_9aac0 : decode_any W_9aac0 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aac4 : bv 32 := 0x01068693.
Lemma F_9aac4 : fetch_word AsanUbsan.M.loaded_segments (0x9aac4 : word) = Some W_9aac4.
Proof. vm_refl. Qed.
Lemma D_9aac4 : decode_any W_9aac4 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aac8 : bv 32 := 0xfcc76ae3.
Lemma F_9aac8 : fetch_word AsanUbsan.M.loaded_segments (0x9aac8 : word) = Some W_9aac8.
Proof. vm_refl. Qed.
Lemma D_9aac8 : decode_any W_9aac8 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aacc : bv 32 := 0x00800713.
Lemma F_9aacc : fetch_word AsanUbsan.M.loaded_segments (0x9aacc : word) = Some W_9aacc.
Proof. vm_refl. Qed.
Lemma D_9aacc : decode_any W_9aacc = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aad0 : bv 32 := 0x00e66e63.
Lemma F_9aad0 : fetch_word AsanUbsan.M.loaded_segments (0x9aad0 : word) = Some W_9aad0.
Proof. vm_refl. Qed.
Lemma D_9aad0 : decode_any W_9aad0 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aad4 : bv 32 := 0x0005a703.
Lemma F_9aad4 : fetch_word AsanUbsan.M.loaded_segments (0x9aad4 : word) = Some W_9aad4.
Proof. vm_refl. Qed.
Lemma D_9aad4 : decode_any W_9aad4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aad8 : bv 32 := 0x0045a783.
Lemma F_9aad8 : fetch_word AsanUbsan.M.loaded_segments (0x9aad8 : word) = Some W_9aad8.
Proof. vm_refl. Qed.
Lemma D_9aad8 : decode_any W_9aad8 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aadc : bv 32 := 0x00e6a023.
Lemma F_9aadc : fetch_word AsanUbsan.M.loaded_segments (0x9aadc : word) = Some W_9aadc.
Proof. vm_refl. Qed.
Lemma D_9aadc : decode_any W_9aadc = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aae0 : bv 32 := 0x00f6a223.
Lemma F_9aae0 : fetch_word AsanUbsan.M.loaded_segments (0x9aae0 : word) = Some W_9aae0.
Proof. vm_refl. Qed.
Lemma D_9aae0 : decode_any W_9aae0 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aae4 : bv 32 := 0x00868693.
Lemma F_9aae4 : fetch_word AsanUbsan.M.loaded_segments (0x9aae4 : word) = Some W_9aae4.
Proof. vm_refl. Qed.
Lemma D_9aae4 : decode_any W_9aae4 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aae8 : bv 32 := 0x00858593.
Lemma F_9aae8 : fetch_word AsanUbsan.M.loaded_segments (0x9aae8 : word) = Some W_9aae8.
Proof. vm_refl. Qed.
Lemma D_9aae8 : decode_any W_9aae8 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aaec : bv 32 := 0x00467713.
Lemma F_9aaec : fetch_word AsanUbsan.M.loaded_segments (0x9aaec : word) = Some W_9aaec.
Proof. vm_refl. Qed.
Lemma D_9aaec : decode_any W_9aaec = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aaf0 : bv 32 := 0x24070063.
Lemma F_9aaf0 : fetch_word AsanUbsan.M.loaded_segments (0x9aaf0 : word) = Some W_9aaf0.
Proof. vm_refl. Qed.
Lemma D_9aaf0 : decode_any W_9aaf0 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aaf4 : bv 32 := 0x0005a703.
Lemma F_9aaf4 : fetch_word AsanUbsan.M.loaded_segments (0x9aaf4 : word) = Some W_9aaf4.
Proof. vm_refl. Qed.
Lemma D_9aaf4 : decode_any W_9aaf4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aaf8 : bv 32 := 0x00458593.
Lemma F_9aaf8 : fetch_word AsanUbsan.M.loaded_segments (0x9aaf8 : word) = Some W_9aaf8.
Proof. vm_refl. Qed.
Lemma D_9aaf8 : decode_any W_9aaf8 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aafc : bv 32 := 0x00e6a023.
Lemma F_9aafc : fetch_word AsanUbsan.M.loaded_segments (0x9aafc : word) = Some W_9aafc.
Proof. vm_refl. Qed.
Lemma D_9aafc : decode_any W_9aafc = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab00 : bv 32 := 0x00468693.
Lemma F_9ab00 : fetch_word AsanUbsan.M.loaded_segments (0x9ab00 : word) = Some W_9ab00.
Proof. vm_refl. Qed.
Lemma D_9ab00 : decode_any W_9ab00 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab04 : bv 32 := 0x22c0006f.
Lemma F_9ab04 : fetch_word AsanUbsan.M.loaded_segments (0x9ab04 : word) = Some W_9ab04.
Proof. vm_refl. Qed.
Lemma D_9ab04 : decode_any W_9ab04 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab08 : bv 32 := 0x00e68023.
Lemma F_9ab08 : fetch_word AsanUbsan.M.loaded_segments (0x9ab08 : word) = Some W_9ab08.
Proof. vm_refl. Qed.
Lemma D_9ab08 : decode_any W_9ab08 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab0c : bv 32 := 0x00168693.
Lemma F_9ab0c : fetch_word AsanUbsan.M.loaded_segments (0x9ab0c : word) = Some W_9ab0c.
Proof. vm_refl. Qed.
Lemma D_9ab0c : decode_any W_9ab0c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab10 : bv 32 := 0xfff60613.
Lemma F_9ab10 : fetch_word AsanUbsan.M.loaded_segments (0x9ab10 : word) = Some W_9ab10.
Proof. vm_refl. Qed.
Lemma D_9ab10 : decode_any W_9ab10 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab14 : bv 32 := 0x01058593.
Lemma F_9ab14 : fetch_word AsanUbsan.M.loaded_segments (0x9ab14 : word) = Some W_9ab14.
Proof. vm_refl. Qed.
Lemma D_9ab14 : decode_any W_9ab14 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab18 : bv 32 := 0x01200793.
Lemma F_9ab18 : fetch_word AsanUbsan.M.loaded_segments (0x9ab18 : word) = Some W_9ab18.
Proof. vm_refl. Qed.
Lemma D_9ab18 : decode_any W_9ab18 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab1c : bv 32 := 0x0087581b.
Lemma F_9ab1c : fetch_word AsanUbsan.M.loaded_segments (0x9ab1c : word) = Some W_9ab1c.
Proof. vm_refl. Qed.
Lemma D_9ab1c : decode_any W_9ab1c = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab20 : bv 32 := 0xff45a883.
Lemma F_9ab20 : fetch_word AsanUbsan.M.loaded_segments (0x9ab20 : word) = Some W_9ab20.
Proof. vm_refl. Qed.
Lemma D_9ab20 : decode_any W_9ab20 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab24 : bv 32 := 0xff85a283.
Lemma F_9ab24 : fetch_word AsanUbsan.M.loaded_segments (0x9ab24 : word) = Some W_9ab24.
Proof. vm_refl. Qed.
Lemma D_9ab24 : decode_any W_9ab24 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab28 : bv 32 := 0xffc5a303.
Lemma F_9ab28 : fetch_word AsanUbsan.M.loaded_segments (0x9ab28 : word) = Some W_9ab28.
Proof. vm_refl. Qed.
Lemma D_9ab28 : decode_any W_9ab28 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab2c : bv 32 := 0x0005a703.
Lemma F_9ab2c : fetch_word AsanUbsan.M.loaded_segments (0x9ab2c : word) = Some W_9ab2c.
Proof. vm_refl. Qed.
Lemma D_9ab2c : decode_any W_9ab2c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab30 : bv 32 := 0x01889393.
Lemma F_9ab30 : fetch_word AsanUbsan.M.loaded_segments (0x9ab30 : word) = Some W_9ab30.
Proof. vm_refl. Qed.
Lemma D_9ab30 : decode_any W_9ab30 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab34 : bv 32 := 0x0088d89b.
Lemma F_9ab34 : fetch_word AsanUbsan.M.loaded_segments (0x9ab34 : word) = Some W_9ab34.
Proof. vm_refl. Qed.
Lemma D_9ab34 : decode_any W_9ab34 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab38 : bv 32 := 0x0103e833.
Lemma F_9ab38 : fetch_word AsanUbsan.M.loaded_segments (0x9ab38 : word) = Some W_9ab38.
Proof. vm_refl. Qed.
Lemma D_9ab38 : decode_any W_9ab38 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab3c : bv 32 := 0x01829393.
Lemma F_9ab3c : fetch_word AsanUbsan.M.loaded_segments (0x9ab3c : word) = Some W_9ab3c.
Proof. vm_refl. Qed.
Lemma D_9ab3c : decode_any W_9ab3c = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab40 : bv 32 := 0x0082d29b.
Lemma F_9ab40 : fetch_word AsanUbsan.M.loaded_segments (0x9ab40 : word) = Some W_9ab40.
Proof. vm_refl. Qed.
Lemma D_9ab40 : decode_any W_9ab40 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab44 : bv 32 := 0x0113e8b3.
Lemma F_9ab44 : fetch_word AsanUbsan.M.loaded_segments (0x9ab44 : word) = Some W_9ab44.
Proof. vm_refl. Qed.
Lemma D_9ab44 : decode_any W_9ab44 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab48 : bv 32 := 0x01831393.
Lemma F_9ab48 : fetch_word AsanUbsan.M.loaded_segments (0x9ab48 : word) = Some W_9ab48.
Proof. vm_refl. Qed.
Lemma D_9ab48 : decode_any W_9ab48 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab4c : bv 32 := 0x0083531b.
Lemma F_9ab4c : fetch_word AsanUbsan.M.loaded_segments (0x9ab4c : word) = Some W_9ab4c.
Proof. vm_refl. Qed.
Lemma D_9ab4c : decode_any W_9ab4c = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab50 : bv 32 := 0x0053e2b3.
Lemma F_9ab50 : fetch_word AsanUbsan.M.loaded_segments (0x9ab50 : word) = Some W_9ab50.
Proof. vm_refl. Qed.
Lemma D_9ab50 : decode_any W_9ab50 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab54 : bv 32 := 0x01871393.
Lemma F_9ab54 : fetch_word AsanUbsan.M.loaded_segments (0x9ab54 : word) = Some W_9ab54.
Proof. vm_refl. Qed.
Lemma D_9ab54 : decode_any W_9ab54 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab58 : bv 32 := 0x0063e333.
Lemma F_9ab58 : fetch_word AsanUbsan.M.loaded_segments (0x9ab58 : word) = Some W_9ab58.
Proof. vm_refl. Qed.
Lemma D_9ab58 : decode_any W_9ab58 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab5c : bv 32 := 0xff060613.
Lemma F_9ab5c : fetch_word AsanUbsan.M.loaded_segments (0x9ab5c : word) = Some W_9ab5c.
Proof. vm_refl. Qed.
Lemma D_9ab5c : decode_any W_9ab5c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab60 : bv 32 := 0x0106a023.
Lemma F_9ab60 : fetch_word AsanUbsan.M.loaded_segments (0x9ab60 : word) = Some W_9ab60.
Proof. vm_refl. Qed.
Lemma D_9ab60 : decode_any W_9ab60 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab64 : bv 32 := 0x0116a223.
Lemma F_9ab64 : fetch_word AsanUbsan.M.loaded_segments (0x9ab64 : word) = Some W_9ab64.
Proof. vm_refl. Qed.
Lemma D_9ab64 : decode_any W_9ab64 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab68 : bv 32 := 0x0056a423.
Lemma F_9ab68 : fetch_word AsanUbsan.M.loaded_segments (0x9ab68 : word) = Some W_9ab68.
Proof. vm_refl. Qed.
Lemma D_9ab68 : decode_any W_9ab68 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab6c : bv 32 := 0x0066a623.
Lemma F_9ab6c : fetch_word AsanUbsan.M.loaded_segments (0x9ab6c : word) = Some W_9ab6c.
Proof. vm_refl. Qed.
Lemma D_9ab6c : decode_any W_9ab6c = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab70 : bv 32 := 0x01068693.
Lemma F_9ab70 : fetch_word AsanUbsan.M.loaded_segments (0x9ab70 : word) = Some W_9ab70.
Proof. vm_refl. Qed.
Lemma D_9ab70 : decode_any W_9ab70 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab74 : bv 32 := 0x01058593.
Lemma F_9ab74 : fetch_word AsanUbsan.M.loaded_segments (0x9ab74 : word) = Some W_9ab74.
Proof. vm_refl. Qed.
Lemma D_9ab74 : decode_any W_9ab74 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab78 : bv 32 := 0xfac7e2e3.
Lemma F_9ab78 : fetch_word AsanUbsan.M.loaded_segments (0x9ab78 : word) = Some W_9ab78.
Proof. vm_refl. Qed.
Lemma D_9ab78 : decode_any W_9ab78 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab7c : bv 32 := 0xff158593.
Lemma F_9ab7c : fetch_word AsanUbsan.M.loaded_segments (0x9ab7c : word) = Some W_9ab7c.
Proof. vm_refl. Qed.
Lemma D_9ab7c : decode_any W_9ab7c = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab80 : bv 32 := 0x01000713.
Lemma F_9ab80 : fetch_word AsanUbsan.M.loaded_segments (0x9ab80 : word) = Some W_9ab80.
Proof. vm_refl. Qed.
Lemma D_9ab80 : decode_any W_9ab80 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab84 : bv 32 := 0xe4e666e3.
Lemma F_9ab84 : fetch_word AsanUbsan.M.loaded_segments (0x9ab84 : word) = Some W_9ab84.
Proof. vm_refl. Qed.
Lemma D_9ab84 : decode_any W_9ab84 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab88 : bv 32 := 0x0940006f.
Lemma F_9ab88 : fetch_word AsanUbsan.M.loaded_segments (0x9ab88 : word) = Some W_9ab88.
Proof. vm_refl. Qed.
Lemma D_9ab88 : decode_any W_9ab88 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab8c : bv 32 := 0x00875793.
Lemma F_9ab8c : fetch_word AsanUbsan.M.loaded_segments (0x9ab8c : word) = Some W_9ab8c.
Proof. vm_refl. Qed.
Lemma D_9ab8c : decode_any W_9ab8c = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab90 : bv 32 := 0x01075813.
Lemma F_9ab90 : fetch_word AsanUbsan.M.loaded_segments (0x9ab90 : word) = Some W_9ab90.
Proof. vm_refl. Qed.
Lemma D_9ab90 : decode_any W_9ab90 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab94 : bv 32 := 0xffd60613.
Lemma F_9ab94 : fetch_word AsanUbsan.M.loaded_segments (0x9ab94 : word) = Some W_9ab94.
Proof. vm_refl. Qed.
Lemma D_9ab94 : decode_any W_9ab94 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab98 : bv 32 := 0x00e68023.
Lemma F_9ab98 : fetch_word AsanUbsan.M.loaded_segments (0x9ab98 : word) = Some W_9ab98.
Proof. vm_refl. Qed.
Lemma D_9ab98 : decode_any W_9ab98 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ab9c : bv 32 := 0x00f680a3.
Lemma F_9ab9c : fetch_word AsanUbsan.M.loaded_segments (0x9ab9c : word) = Some W_9ab9c.
Proof. vm_refl. Qed.
Lemma D_9ab9c : decode_any W_9ab9c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aba0 : bv 32 := 0x01068123.
Lemma F_9aba0 : fetch_word AsanUbsan.M.loaded_segments (0x9aba0 : word) = Some W_9aba0.
Proof. vm_refl. Qed.
Lemma D_9aba0 : decode_any W_9aba0 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aba4 : bv 32 := 0x00368693.
Lemma F_9aba4 : fetch_word AsanUbsan.M.loaded_segments (0x9aba4 : word) = Some W_9aba4.
Proof. vm_refl. Qed.
Lemma D_9aba4 : decode_any W_9aba4 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aba8 : bv 32 := 0x01058593.
Lemma F_9aba8 : fetch_word AsanUbsan.M.loaded_segments (0x9aba8 : word) = Some W_9aba8.
Proof. vm_refl. Qed.
Lemma D_9aba8 : decode_any W_9aba8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abac : bv 32 := 0x01000793.
Lemma F_9abac : fetch_word AsanUbsan.M.loaded_segments (0x9abac : word) = Some W_9abac.
Proof. vm_refl. Qed.
Lemma D_9abac : decode_any W_9abac = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abb0 : bv 32 := 0x0187581b.
Lemma F_9abb0 : fetch_word AsanUbsan.M.loaded_segments (0x9abb0 : word) = Some W_9abb0.
Proof. vm_refl. Qed.
Lemma D_9abb0 : decode_any W_9abb0 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abb4 : bv 32 := 0xff45a883.
Lemma F_9abb4 : fetch_word AsanUbsan.M.loaded_segments (0x9abb4 : word) = Some W_9abb4.
Proof. vm_refl. Qed.
Lemma D_9abb4 : decode_any W_9abb4 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abb8 : bv 32 := 0xff85a283.
Lemma F_9abb8 : fetch_word AsanUbsan.M.loaded_segments (0x9abb8 : word) = Some W_9abb8.
Proof. vm_refl. Qed.
Lemma D_9abb8 : decode_any W_9abb8 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abbc : bv 32 := 0xffc5a303.
Lemma F_9abbc : fetch_word AsanUbsan.M.loaded_segments (0x9abbc : word) = Some W_9abbc.
Proof. vm_refl. Qed.
Lemma D_9abbc : decode_any W_9abbc = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abc0 : bv 32 := 0x0005a703.
Lemma F_9abc0 : fetch_word AsanUbsan.M.loaded_segments (0x9abc0 : word) = Some W_9abc0.
Proof. vm_refl. Qed.
Lemma D_9abc0 : decode_any W_9abc0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abc4 : bv 32 := 0x00889393.
Lemma F_9abc4 : fetch_word AsanUbsan.M.loaded_segments (0x9abc4 : word) = Some W_9abc4.
Proof. vm_refl. Qed.
Lemma D_9abc4 : decode_any W_9abc4 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abc8 : bv 32 := 0x0188d89b.
Lemma F_9abc8 : fetch_word AsanUbsan.M.loaded_segments (0x9abc8 : word) = Some W_9abc8.
Proof. vm_refl. Qed.
Lemma D_9abc8 : decode_any W_9abc8 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abcc : bv 32 := 0x0103e833.
Lemma F_9abcc : fetch_word AsanUbsan.M.loaded_segments (0x9abcc : word) = Some W_9abcc.
Proof. vm_refl. Qed.
Lemma D_9abcc : decode_any W_9abcc = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abd0 : bv 32 := 0x00829393.
Lemma F_9abd0 : fetch_word AsanUbsan.M.loaded_segments (0x9abd0 : word) = Some W_9abd0.
Proof. vm_refl. Qed.
Lemma D_9abd0 : decode_any W_9abd0 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abd4 : bv 32 := 0x0182d29b.
Lemma F_9abd4 : fetch_word AsanUbsan.M.loaded_segments (0x9abd4 : word) = Some W_9abd4.
Proof. vm_refl. Qed.
Lemma D_9abd4 : decode_any W_9abd4 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abd8 : bv 32 := 0x0113e8b3.
Lemma F_9abd8 : fetch_word AsanUbsan.M.loaded_segments (0x9abd8 : word) = Some W_9abd8.
Proof. vm_refl. Qed.
Lemma D_9abd8 : decode_any W_9abd8 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abdc : bv 32 := 0x00831393.
Lemma F_9abdc : fetch_word AsanUbsan.M.loaded_segments (0x9abdc : word) = Some W_9abdc.
Proof. vm_refl. Qed.
Lemma D_9abdc : decode_any W_9abdc = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abe0 : bv 32 := 0x0183531b.
Lemma F_9abe0 : fetch_word AsanUbsan.M.loaded_segments (0x9abe0 : word) = Some W_9abe0.
Proof. vm_refl. Qed.
Lemma D_9abe0 : decode_any W_9abe0 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abe4 : bv 32 := 0x0053e2b3.
Lemma F_9abe4 : fetch_word AsanUbsan.M.loaded_segments (0x9abe4 : word) = Some W_9abe4.
Proof. vm_refl. Qed.
Lemma D_9abe4 : decode_any W_9abe4 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abe8 : bv 32 := 0x00871393.
Lemma F_9abe8 : fetch_word AsanUbsan.M.loaded_segments (0x9abe8 : word) = Some W_9abe8.
Proof. vm_refl. Qed.
Lemma D_9abe8 : decode_any W_9abe8 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abec : bv 32 := 0x0063e333.
Lemma F_9abec : fetch_word AsanUbsan.M.loaded_segments (0x9abec : word) = Some W_9abec.
Proof. vm_refl. Qed.
Lemma D_9abec : decode_any W_9abec = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abf0 : bv 32 := 0xff060613.
Lemma F_9abf0 : fetch_word AsanUbsan.M.loaded_segments (0x9abf0 : word) = Some W_9abf0.
Proof. vm_refl. Qed.
Lemma D_9abf0 : decode_any W_9abf0 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abf4 : bv 32 := 0x0106a023.
Lemma F_9abf4 : fetch_word AsanUbsan.M.loaded_segments (0x9abf4 : word) = Some W_9abf4.
Proof. vm_refl. Qed.
Lemma D_9abf4 : decode_any W_9abf4 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abf8 : bv 32 := 0x0116a223.
Lemma F_9abf8 : fetch_word AsanUbsan.M.loaded_segments (0x9abf8 : word) = Some W_9abf8.
Proof. vm_refl. Qed.
Lemma D_9abf8 : decode_any W_9abf8 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9abfc : bv 32 := 0x0056a423.
Lemma F_9abfc : fetch_word AsanUbsan.M.loaded_segments (0x9abfc : word) = Some W_9abfc.
Proof. vm_refl. Qed.
Lemma D_9abfc : decode_any W_9abfc = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac00 : bv 32 := 0x0066a623.
Lemma F_9ac00 : fetch_word AsanUbsan.M.loaded_segments (0x9ac00 : word) = Some W_9ac00.
Proof. vm_refl. Qed.
Lemma D_9ac00 : decode_any W_9ac00 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac04 : bv 32 := 0x01068693.
Lemma F_9ac04 : fetch_word AsanUbsan.M.loaded_segments (0x9ac04 : word) = Some W_9ac04.
Proof. vm_refl. Qed.
Lemma D_9ac04 : decode_any W_9ac04 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac08 : bv 32 := 0x01058593.
Lemma F_9ac08 : fetch_word AsanUbsan.M.loaded_segments (0x9ac08 : word) = Some W_9ac08.
Proof. vm_refl. Qed.
Lemma D_9ac08 : decode_any W_9ac08 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac0c : bv 32 := 0xfac7e2e3.
Lemma F_9ac0c : fetch_word AsanUbsan.M.loaded_segments (0x9ac0c : word) = Some W_9ac0c.
Proof. vm_refl. Qed.
Lemma D_9ac0c : decode_any W_9ac0c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac10 : bv 32 := 0xff358593.
Lemma F_9ac10 : fetch_word AsanUbsan.M.loaded_segments (0x9ac10 : word) = Some W_9ac10.
Proof. vm_refl. Qed.
Lemma D_9ac10 : decode_any W_9ac10 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac14 : bv 32 := 0x01000713.
Lemma F_9ac14 : fetch_word AsanUbsan.M.loaded_segments (0x9ac14 : word) = Some W_9ac14.
Proof. vm_refl. Qed.
Lemma D_9ac14 : decode_any W_9ac14 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac18 : bv 32 := 0xdae66ce3.
Lemma F_9ac18 : fetch_word AsanUbsan.M.loaded_segments (0x9ac18 : word) = Some W_9ac18.
Proof. vm_refl. Qed.
Lemma D_9ac18 : decode_any W_9ac18 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac1c : bv 32 := 0x0005c703.
Lemma F_9ac1c : fetch_word AsanUbsan.M.loaded_segments (0x9ac1c : word) = Some W_9ac1c.
Proof. vm_refl. Qed.
Lemma D_9ac1c : decode_any W_9ac1c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac20 : bv 32 := 0x0015c783.
Lemma F_9ac20 : fetch_word AsanUbsan.M.loaded_segments (0x9ac20 : word) = Some W_9ac20.
Proof. vm_refl. Qed.
Lemma D_9ac20 : decode_any W_9ac20 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac24 : bv 32 := 0x0025c803.
Lemma F_9ac24 : fetch_word AsanUbsan.M.loaded_segments (0x9ac24 : word) = Some W_9ac24.
Proof. vm_refl. Qed.
Lemma D_9ac24 : decode_any W_9ac24 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac28 : bv 32 := 0x0035c883.
Lemma F_9ac28 : fetch_word AsanUbsan.M.loaded_segments (0x9ac28 : word) = Some W_9ac28.
Proof. vm_refl. Qed.
Lemma D_9ac28 : decode_any W_9ac28 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac2c : bv 32 := 0x0045c283.
Lemma F_9ac2c : fetch_word AsanUbsan.M.loaded_segments (0x9ac2c : word) = Some W_9ac2c.
Proof. vm_refl. Qed.
Lemma D_9ac2c : decode_any W_9ac2c = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac30 : bv 32 := 0x0055c303.
Lemma F_9ac30 : fetch_word AsanUbsan.M.loaded_segments (0x9ac30 : word) = Some W_9ac30.
Proof. vm_refl. Qed.
Lemma D_9ac30 : decode_any W_9ac30 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac34 : bv 32 := 0x0065c383.
Lemma F_9ac34 : fetch_word AsanUbsan.M.loaded_segments (0x9ac34 : word) = Some W_9ac34.
Proof. vm_refl. Qed.
Lemma D_9ac34 : decode_any W_9ac34 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac38 : bv 32 := 0x0075ce03.
Lemma F_9ac38 : fetch_word AsanUbsan.M.loaded_segments (0x9ac38 : word) = Some W_9ac38.
Proof. vm_refl. Qed.
Lemma D_9ac38 : decode_any W_9ac38 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac3c : bv 32 := 0x00e68023.
Lemma F_9ac3c : fetch_word AsanUbsan.M.loaded_segments (0x9ac3c : word) = Some W_9ac3c.
Proof. vm_refl. Qed.
Lemma D_9ac3c : decode_any W_9ac3c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac40 : bv 32 := 0x00f680a3.
Lemma F_9ac40 : fetch_word AsanUbsan.M.loaded_segments (0x9ac40 : word) = Some W_9ac40.
Proof. vm_refl. Qed.
Lemma D_9ac40 : decode_any W_9ac40 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac44 : bv 32 := 0x01068123.
Lemma F_9ac44 : fetch_word AsanUbsan.M.loaded_segments (0x9ac44 : word) = Some W_9ac44.
Proof. vm_refl. Qed.
Lemma D_9ac44 : decode_any W_9ac44 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac48 : bv 32 := 0x011681a3.
Lemma F_9ac48 : fetch_word AsanUbsan.M.loaded_segments (0x9ac48 : word) = Some W_9ac48.
Proof. vm_refl. Qed.
Lemma D_9ac48 : decode_any W_9ac48 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac4c : bv 32 := 0x0085c703.
Lemma F_9ac4c : fetch_word AsanUbsan.M.loaded_segments (0x9ac4c : word) = Some W_9ac4c.
Proof. vm_refl. Qed.
Lemma D_9ac4c : decode_any W_9ac4c = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac50 : bv 32 := 0x0095c783.
Lemma F_9ac50 : fetch_word AsanUbsan.M.loaded_segments (0x9ac50 : word) = Some W_9ac50.
Proof. vm_refl. Qed.
Lemma D_9ac50 : decode_any W_9ac50 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac54 : bv 32 := 0x00a5c803.
Lemma F_9ac54 : fetch_word AsanUbsan.M.loaded_segments (0x9ac54 : word) = Some W_9ac54.
Proof. vm_refl. Qed.
Lemma D_9ac54 : decode_any W_9ac54 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac58 : bv 32 := 0x00b5c883.
Lemma F_9ac58 : fetch_word AsanUbsan.M.loaded_segments (0x9ac58 : word) = Some W_9ac58.
Proof. vm_refl. Qed.
Lemma D_9ac58 : decode_any W_9ac58 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac5c : bv 32 := 0x00568223.
Lemma F_9ac5c : fetch_word AsanUbsan.M.loaded_segments (0x9ac5c : word) = Some W_9ac5c.
Proof. vm_refl. Qed.
Lemma D_9ac5c : decode_any W_9ac5c = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac60 : bv 32 := 0x006682a3.
Lemma F_9ac60 : fetch_word AsanUbsan.M.loaded_segments (0x9ac60 : word) = Some W_9ac60.
Proof. vm_refl. Qed.
Lemma D_9ac60 : decode_any W_9ac60 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac64 : bv 32 := 0x00768323.
Lemma F_9ac64 : fetch_word AsanUbsan.M.loaded_segments (0x9ac64 : word) = Some W_9ac64.
Proof. vm_refl. Qed.
Lemma D_9ac64 : decode_any W_9ac64 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac68 : bv 32 := 0x01c683a3.
Lemma F_9ac68 : fetch_word AsanUbsan.M.loaded_segments (0x9ac68 : word) = Some W_9ac68.
Proof. vm_refl. Qed.
Lemma D_9ac68 : decode_any W_9ac68 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac6c : bv 32 := 0x00c5c283.
Lemma F_9ac6c : fetch_word AsanUbsan.M.loaded_segments (0x9ac6c : word) = Some W_9ac6c.
Proof. vm_refl. Qed.
Lemma D_9ac6c : decode_any W_9ac6c = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac70 : bv 32 := 0x00d5c303.
Lemma F_9ac70 : fetch_word AsanUbsan.M.loaded_segments (0x9ac70 : word) = Some W_9ac70.
Proof. vm_refl. Qed.
Lemma D_9ac70 : decode_any W_9ac70 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac74 : bv 32 := 0x00e5c383.
Lemma F_9ac74 : fetch_word AsanUbsan.M.loaded_segments (0x9ac74 : word) = Some W_9ac74.
Proof. vm_refl. Qed.
Lemma D_9ac74 : decode_any W_9ac74 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac78 : bv 32 := 0x00f5ce03.
Lemma F_9ac78 : fetch_word AsanUbsan.M.loaded_segments (0x9ac78 : word) = Some W_9ac78.
Proof. vm_refl. Qed.
Lemma D_9ac78 : decode_any W_9ac78 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac7c : bv 32 := 0x01058593.
Lemma F_9ac7c : fetch_word AsanUbsan.M.loaded_segments (0x9ac7c : word) = Some W_9ac7c.
Proof. vm_refl. Qed.
Lemma D_9ac7c : decode_any W_9ac7c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac80 : bv 32 := 0x00e68423.
Lemma F_9ac80 : fetch_word AsanUbsan.M.loaded_segments (0x9ac80 : word) = Some W_9ac80.
Proof. vm_refl. Qed.
Lemma D_9ac80 : decode_any W_9ac80 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac84 : bv 32 := 0x00f684a3.
Lemma F_9ac84 : fetch_word AsanUbsan.M.loaded_segments (0x9ac84 : word) = Some W_9ac84.
Proof. vm_refl. Qed.
Lemma D_9ac84 : decode_any W_9ac84 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac88 : bv 32 := 0x01068523.
Lemma F_9ac88 : fetch_word AsanUbsan.M.loaded_segments (0x9ac88 : word) = Some W_9ac88.
Proof. vm_refl. Qed.
Lemma D_9ac88 : decode_any W_9ac88 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac8c : bv 32 := 0x011685a3.
Lemma F_9ac8c : fetch_word AsanUbsan.M.loaded_segments (0x9ac8c : word) = Some W_9ac8c.
Proof. vm_refl. Qed.
Lemma D_9ac8c : decode_any W_9ac8c = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac90 : bv 32 := 0x01068713.
Lemma F_9ac90 : fetch_word AsanUbsan.M.loaded_segments (0x9ac90 : word) = Some W_9ac90.
Proof. vm_refl. Qed.
Lemma D_9ac90 : decode_any W_9ac90 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac94 : bv 32 := 0x00568623.
Lemma F_9ac94 : fetch_word AsanUbsan.M.loaded_segments (0x9ac94 : word) = Some W_9ac94.
Proof. vm_refl. Qed.
Lemma D_9ac94 : decode_any W_9ac94 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac98 : bv 32 := 0x006686a3.
Lemma F_9ac98 : fetch_word AsanUbsan.M.loaded_segments (0x9ac98 : word) = Some W_9ac98.
Proof. vm_refl. Qed.
Lemma D_9ac98 : decode_any W_9ac98 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac9c : bv 32 := 0x00768723.
Lemma F_9ac9c : fetch_word AsanUbsan.M.loaded_segments (0x9ac9c : word) = Some W_9ac9c.
Proof. vm_refl. Qed.
Lemma D_9ac9c : decode_any W_9ac9c = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aca0 : bv 32 := 0x01c687a3.
Lemma F_9aca0 : fetch_word AsanUbsan.M.loaded_segments (0x9aca0 : word) = Some W_9aca0.
Proof. vm_refl. Qed.
Lemma D_9aca0 : decode_any W_9aca0 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aca4 : bv 32 := 0x00070693.
Lemma F_9aca4 : fetch_word AsanUbsan.M.loaded_segments (0x9aca4 : word) = Some W_9aca4.
Proof. vm_refl. Qed.
Lemma D_9aca4 : decode_any W_9aca4 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9aca8 : bv 32 := 0x00867713.
Lemma F_9aca8 : fetch_word AsanUbsan.M.loaded_segments (0x9aca8 : word) = Some W_9aca8.
Proof. vm_refl. Qed.
Lemma D_9aca8 : decode_any W_9aca8 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9acac : bv 32 := 0xd20706e3.
Lemma F_9acac : fetch_word AsanUbsan.M.loaded_segments (0x9acac : word) = Some W_9acac.
Proof. vm_refl. Qed.
Lemma D_9acac : decode_any W_9acac = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9acb0 : bv 32 := 0x0005c703.
Lemma F_9acb0 : fetch_word AsanUbsan.M.loaded_segments (0x9acb0 : word) = Some W_9acb0.
Proof. vm_refl. Qed.
Lemma D_9acb0 : decode_any W_9acb0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9acb4 : bv 32 := 0x0015c783.
Lemma F_9acb4 : fetch_word AsanUbsan.M.loaded_segments (0x9acb4 : word) = Some W_9acb4.
Proof. vm_refl. Qed.
Lemma D_9acb4 : decode_any W_9acb4 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9acb8 : bv 32 := 0x0025c803.
Lemma F_9acb8 : fetch_word AsanUbsan.M.loaded_segments (0x9acb8 : word) = Some W_9acb8.
Proof. vm_refl. Qed.
Lemma D_9acb8 : decode_any W_9acb8 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9acbc : bv 32 := 0x0035c883.
Lemma F_9acbc : fetch_word AsanUbsan.M.loaded_segments (0x9acbc : word) = Some W_9acbc.
Proof. vm_refl. Qed.
Lemma D_9acbc : decode_any W_9acbc = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9acc0 : bv 32 := 0x0045c283.
Lemma F_9acc0 : fetch_word AsanUbsan.M.loaded_segments (0x9acc0 : word) = Some W_9acc0.
Proof. vm_refl. Qed.
Lemma D_9acc0 : decode_any W_9acc0 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9acc4 : bv 32 := 0x0055c303.
Lemma F_9acc4 : fetch_word AsanUbsan.M.loaded_segments (0x9acc4 : word) = Some W_9acc4.
Proof. vm_refl. Qed.
Lemma D_9acc4 : decode_any W_9acc4 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9acc8 : bv 32 := 0x0065c383.
Lemma F_9acc8 : fetch_word AsanUbsan.M.loaded_segments (0x9acc8 : word) = Some W_9acc8.
Proof. vm_refl. Qed.
Lemma D_9acc8 : decode_any W_9acc8 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9accc : bv 32 := 0x0075ce03.
Lemma F_9accc : fetch_word AsanUbsan.M.loaded_segments (0x9accc : word) = Some W_9accc.
Proof. vm_refl. Qed.
Lemma D_9accc : decode_any W_9accc = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9acd0 : bv 32 := 0x00858593.
Lemma F_9acd0 : fetch_word AsanUbsan.M.loaded_segments (0x9acd0 : word) = Some W_9acd0.
Proof. vm_refl. Qed.
Lemma D_9acd0 : decode_any W_9acd0 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9acd4 : bv 32 := 0x00e68023.
Lemma F_9acd4 : fetch_word AsanUbsan.M.loaded_segments (0x9acd4 : word) = Some W_9acd4.
Proof. vm_refl. Qed.
Lemma D_9acd4 : decode_any W_9acd4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9acd8 : bv 32 := 0x00f680a3.
Lemma F_9acd8 : fetch_word AsanUbsan.M.loaded_segments (0x9acd8 : word) = Some W_9acd8.
Proof. vm_refl. Qed.
Lemma D_9acd8 : decode_any W_9acd8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9acdc : bv 32 := 0x01068123.
Lemma F_9acdc : fetch_word AsanUbsan.M.loaded_segments (0x9acdc : word) = Some W_9acdc.
Proof. vm_refl. Qed.
Lemma D_9acdc : decode_any W_9acdc = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ace0 : bv 32 := 0x011681a3.
Lemma F_9ace0 : fetch_word AsanUbsan.M.loaded_segments (0x9ace0 : word) = Some W_9ace0.
Proof. vm_refl. Qed.
Lemma D_9ace0 : decode_any W_9ace0 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ace4 : bv 32 := 0x00868713.
Lemma F_9ace4 : fetch_word AsanUbsan.M.loaded_segments (0x9ace4 : word) = Some W_9ace4.
Proof. vm_refl. Qed.
Lemma D_9ace4 : decode_any W_9ace4 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ace8 : bv 32 := 0x00568223.
Lemma F_9ace8 : fetch_word AsanUbsan.M.loaded_segments (0x9ace8 : word) = Some W_9ace8.
Proof. vm_refl. Qed.
Lemma D_9ace8 : decode_any W_9ace8 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9acec : bv 32 := 0x006682a3.
Lemma F_9acec : fetch_word AsanUbsan.M.loaded_segments (0x9acec : word) = Some W_9acec.
Proof. vm_refl. Qed.
Lemma D_9acec : decode_any W_9acec = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9acf0 : bv 32 := 0x00768323.
Lemma F_9acf0 : fetch_word AsanUbsan.M.loaded_segments (0x9acf0 : word) = Some W_9acf0.
Proof. vm_refl. Qed.
Lemma D_9acf0 : decode_any W_9acf0 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9acf4 : bv 32 := 0x01c683a3.
Lemma F_9acf4 : fetch_word AsanUbsan.M.loaded_segments (0x9acf4 : word) = Some W_9acf4.
Proof. vm_refl. Qed.
Lemma D_9acf4 : decode_any W_9acf4 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9acf8 : bv 32 := 0x00070693.
Lemma F_9acf8 : fetch_word AsanUbsan.M.loaded_segments (0x9acf8 : word) = Some W_9acf8.
Proof. vm_refl. Qed.
Lemma D_9acf8 : decode_any W_9acf8 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9acfc : bv 32 := 0x00467713.
Lemma F_9acfc : fetch_word AsanUbsan.M.loaded_segments (0x9acfc : word) = Some W_9acfc.
Proof. vm_refl. Qed.
Lemma D_9acfc : decode_any W_9acfc = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad00 : bv 32 := 0x02070863.
Lemma F_9ad00 : fetch_word AsanUbsan.M.loaded_segments (0x9ad00 : word) = Some W_9ad00.
Proof. vm_refl. Qed.
Lemma D_9ad00 : decode_any W_9ad00 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad04 : bv 32 := 0x0005c703.
Lemma F_9ad04 : fetch_word AsanUbsan.M.loaded_segments (0x9ad04 : word) = Some W_9ad04.
Proof. vm_refl. Qed.
Lemma D_9ad04 : decode_any W_9ad04 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad08 : bv 32 := 0x0015c783.
Lemma F_9ad08 : fetch_word AsanUbsan.M.loaded_segments (0x9ad08 : word) = Some W_9ad08.
Proof. vm_refl. Qed.
Lemma D_9ad08 : decode_any W_9ad08 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad0c : bv 32 := 0x0025c803.
Lemma F_9ad0c : fetch_word AsanUbsan.M.loaded_segments (0x9ad0c : word) = Some W_9ad0c.
Proof. vm_refl. Qed.
Lemma D_9ad0c : decode_any W_9ad0c = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad10 : bv 32 := 0x0035c883.
Lemma F_9ad10 : fetch_word AsanUbsan.M.loaded_segments (0x9ad10 : word) = Some W_9ad10.
Proof. vm_refl. Qed.
Lemma D_9ad10 : decode_any W_9ad10 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad14 : bv 32 := 0x00458593.
Lemma F_9ad14 : fetch_word AsanUbsan.M.loaded_segments (0x9ad14 : word) = Some W_9ad14.
Proof. vm_refl. Qed.
Lemma D_9ad14 : decode_any W_9ad14 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad18 : bv 32 := 0x00468293.
Lemma F_9ad18 : fetch_word AsanUbsan.M.loaded_segments (0x9ad18 : word) = Some W_9ad18.
Proof. vm_refl. Qed.
Lemma D_9ad18 : decode_any W_9ad18 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad1c : bv 32 := 0x00e68023.
Lemma F_9ad1c : fetch_word AsanUbsan.M.loaded_segments (0x9ad1c : word) = Some W_9ad1c.
Proof. vm_refl. Qed.
Lemma D_9ad1c : decode_any W_9ad1c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad20 : bv 32 := 0x00f680a3.
Lemma F_9ad20 : fetch_word AsanUbsan.M.loaded_segments (0x9ad20 : word) = Some W_9ad20.
Proof. vm_refl. Qed.
Lemma D_9ad20 : decode_any W_9ad20 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad24 : bv 32 := 0x01068123.
Lemma F_9ad24 : fetch_word AsanUbsan.M.loaded_segments (0x9ad24 : word) = Some W_9ad24.
Proof. vm_refl. Qed.
Lemma D_9ad24 : decode_any W_9ad24 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad28 : bv 32 := 0x011681a3.
Lemma F_9ad28 : fetch_word AsanUbsan.M.loaded_segments (0x9ad28 : word) = Some W_9ad28.
Proof. vm_refl. Qed.
Lemma D_9ad28 : decode_any W_9ad28 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad2c : bv 32 := 0x00028693.
Lemma F_9ad2c : fetch_word AsanUbsan.M.loaded_segments (0x9ad2c : word) = Some W_9ad2c.
Proof. vm_refl. Qed.
Lemma D_9ad2c : decode_any W_9ad2c = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad30 : bv 32 := 0x00267713.
Lemma F_9ad30 : fetch_word AsanUbsan.M.loaded_segments (0x9ad30 : word) = Some W_9ad30.
Proof. vm_refl. Qed.
Lemma D_9ad30 : decode_any W_9ad30 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad34 : bv 32 := 0x00071863.
Lemma F_9ad34 : fetch_word AsanUbsan.M.loaded_segments (0x9ad34 : word) = Some W_9ad34.
Proof. vm_refl. Qed.
Lemma D_9ad34 : decode_any W_9ad34 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad38 : bv 32 := 0x00167613.
Lemma F_9ad38 : fetch_word AsanUbsan.M.loaded_segments (0x9ad38 : word) = Some W_9ad38.
Proof. vm_refl. Qed.
Lemma D_9ad38 : decode_any W_9ad38 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad3c : bv 32 := 0x02061663.
Lemma F_9ad3c : fetch_word AsanUbsan.M.loaded_segments (0x9ad3c : word) = Some W_9ad3c.
Proof. vm_refl. Qed.
Lemma D_9ad3c : decode_any W_9ad3c = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad40 : bv 32 := 0x00008067.
Lemma F_9ad40 : fetch_word AsanUbsan.M.loaded_segments (0x9ad40 : word) = Some W_9ad40.
Proof. vm_refl. Qed.
Lemma D_9ad40 : decode_any W_9ad40 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad44 : bv 32 := 0x0005c703.
Lemma F_9ad44 : fetch_word AsanUbsan.M.loaded_segments (0x9ad44 : word) = Some W_9ad44.
Proof. vm_refl. Qed.
Lemma D_9ad44 : decode_any W_9ad44 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad48 : bv 32 := 0x0015c783.
Lemma F_9ad48 : fetch_word AsanUbsan.M.loaded_segments (0x9ad48 : word) = Some W_9ad48.
Proof. vm_refl. Qed.
Lemma D_9ad48 : decode_any W_9ad48 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad4c : bv 32 := 0x00258593.
Lemma F_9ad4c : fetch_word AsanUbsan.M.loaded_segments (0x9ad4c : word) = Some W_9ad4c.
Proof. vm_refl. Qed.
Lemma D_9ad4c : decode_any W_9ad4c = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad50 : bv 32 := 0x00268813.
Lemma F_9ad50 : fetch_word AsanUbsan.M.loaded_segments (0x9ad50 : word) = Some W_9ad50.
Proof. vm_refl. Qed.
Lemma D_9ad50 : decode_any W_9ad50 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad54 : bv 32 := 0x00e68023.
Lemma F_9ad54 : fetch_word AsanUbsan.M.loaded_segments (0x9ad54 : word) = Some W_9ad54.
Proof. vm_refl. Qed.
Lemma D_9ad54 : decode_any W_9ad54 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad58 : bv 32 := 0x00f680a3.
Lemma F_9ad58 : fetch_word AsanUbsan.M.loaded_segments (0x9ad58 : word) = Some W_9ad58.
Proof. vm_refl. Qed.
Lemma D_9ad58 : decode_any W_9ad58 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad5c : bv 32 := 0x00080693.
Lemma F_9ad5c : fetch_word AsanUbsan.M.loaded_segments (0x9ad5c : word) = Some W_9ad5c.
Proof. vm_refl. Qed.
Lemma D_9ad5c : decode_any W_9ad5c = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad60 : bv 32 := 0x00167613.
Lemma F_9ad60 : fetch_word AsanUbsan.M.loaded_segments (0x9ad60 : word) = Some W_9ad60.
Proof. vm_refl. Qed.
Lemma D_9ad60 : decode_any W_9ad60 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad64 : bv 32 := 0xfc060ee3.
Lemma F_9ad64 : fetch_word AsanUbsan.M.loaded_segments (0x9ad64 : word) = Some W_9ad64.
Proof. vm_refl. Qed.
Lemma D_9ad64 : decode_any W_9ad64 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad68 : bv 32 := 0x0005c583.
Lemma F_9ad68 : fetch_word AsanUbsan.M.loaded_segments (0x9ad68 : word) = Some W_9ad68.
Proof. vm_refl. Qed.
Lemma D_9ad68 : decode_any W_9ad68 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad6c : bv 32 := 0x00b68023.
Lemma F_9ad6c : fetch_word AsanUbsan.M.loaded_segments (0x9ad6c : word) = Some W_9ad6c.
Proof. vm_refl. Qed.
Lemma D_9ad6c : decode_any W_9ad6c = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad70 : bv 32 := 0x00008067.
Lemma F_9ad70 : fetch_word AsanUbsan.M.loaded_segments (0x9ad70 : word) = Some W_9ad70.
Proof. vm_refl. Qed.
Lemma D_9ad70 : decode_any W_9ad70 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
