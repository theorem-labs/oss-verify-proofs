(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_7b0a8 : bv 32 := 0xfc010113.
Lemma F_7b0a8 : fetch_word AsanUbsan.M.loaded_segments (0x7b4c0 : word) = Some W_7b0a8.
Proof. vm_refl. Qed.
Lemma D_7b0a8 : decode_any W_7b0a8 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0ac : bv 32 := 0x02113c23.
Lemma F_7b0ac : fetch_word AsanUbsan.M.loaded_segments (0x7b4c4 : word) = Some W_7b0ac.
Proof. vm_refl. Qed.
Lemma D_7b0ac : decode_any W_7b0ac = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0b0 : bv 32 := 0x02813823.
Lemma F_7b0b0 : fetch_word AsanUbsan.M.loaded_segments (0x7b4c8 : word) = Some W_7b0b0.
Proof. vm_refl. Qed.
Lemma D_7b0b0 : decode_any W_7b0b0 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0b4 : bv 32 := 0x02913423.
Lemma F_7b0b4 : fetch_word AsanUbsan.M.loaded_segments (0x7b4cc : word) = Some W_7b0b4.
Proof. vm_refl. Qed.
Lemma D_7b0b4 : decode_any W_7b0b4 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0b8 : bv 32 := 0x03213023.
Lemma F_7b0b8 : fetch_word AsanUbsan.M.loaded_segments (0x7b4d0 : word) = Some W_7b0b8.
Proof. vm_refl. Qed.
Lemma D_7b0b8 : decode_any W_7b0b8 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0bc : bv 32 := 0x01313c23.
Lemma F_7b0bc : fetch_word AsanUbsan.M.loaded_segments (0x7b4d4 : word) = Some W_7b0bc.
Proof. vm_refl. Qed.
Lemma D_7b0bc : decode_any W_7b0bc = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0c0 : bv 32 := 0x01413823.
Lemma F_7b0c0 : fetch_word AsanUbsan.M.loaded_segments (0x7b4d8 : word) = Some W_7b0c0.
Proof. vm_refl. Qed.
Lemma D_7b0c0 : decode_any W_7b0c0 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0c4 : bv 32 := 0x01513423.
Lemma F_7b0c4 : fetch_word AsanUbsan.M.loaded_segments (0x7b4dc : word) = Some W_7b0c4.
Proof. vm_refl. Qed.
Lemma D_7b0c4 : decode_any W_7b0c4 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0c8 : bv 32 := 0x14058c63.
Lemma F_7b0c8 : fetch_word AsanUbsan.M.loaded_segments (0x7b4e0 : word) = Some W_7b0c8.
Proof. vm_refl. Qed.
Lemma D_7b0c8 : decode_any W_7b0c8 = Some (Branch BC_EQ 11 0 344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0cc : bv 32 := 0x00058493.
Lemma F_7b0cc : fetch_word AsanUbsan.M.loaded_segments (0x7b4e4 : word) = Some W_7b0cc.
Proof. vm_refl. Qed.
Lemma D_7b0cc : decode_any W_7b0cc = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0d0 : bv 32 := 0x00050413.
Lemma F_7b0d0 : fetch_word AsanUbsan.M.loaded_segments (0x7b4e8 : word) = Some W_7b0d0.
Proof. vm_refl. Qed.
Lemma D_7b0d0 : decode_any W_7b0d0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0d4 : bv 32 := 0x000bc517.
Lemma F_7b0d4 : fetch_word AsanUbsan.M.loaded_segments (0x7b4ec : word) = Some W_7b0d4.
Proof. vm_refl. Qed.
Lemma D_7b0d4 : decode_any W_7b0d4 = Some (Auipc 10 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0d8 : bv 32 := 0xfd453a83.
Lemma F_7b0d8 : fetch_word AsanUbsan.M.loaded_segments (0x7b4f0 : word) = Some W_7b0d8.
Proof. vm_refl. Qed.
Lemma D_7b0d8 : decode_any W_7b0d8 = Some (Load SZ8 true 21 10 4052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0dc : bv 32 := 0x000ab583.
Lemma F_7b0dc : fetch_word AsanUbsan.M.loaded_segments (0x7b4f4 : word) = Some W_7b0dc.
Proof. vm_refl. Qed.
Lemma D_7b0dc : decode_any W_7b0dc = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0e0 : bv 32 := 0xfff58513.
Lemma F_7b0e0 : fetch_word AsanUbsan.M.loaded_segments (0x7b4f8 : word) = Some W_7b0e0.
Proof. vm_refl. Qed.
Lemma D_7b0e0 : decode_any W_7b0e0 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0e4 : bv 32 := 0x00a5b633.
Lemma F_7b0e4 : fetch_word AsanUbsan.M.loaded_segments (0x7b4fc : word) = Some W_7b0e4.
Proof. vm_refl. Qed.
Lemma D_7b0e4 : decode_any W_7b0e4 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0e8 : bv 32 := 0xfff60613.
Lemma F_7b0e8 : fetch_word AsanUbsan.M.loaded_segments (0x7b500 : word) = Some W_7b0e8.
Proof. vm_refl. Qed.
Lemma D_7b0e8 : decode_any W_7b0e8 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0ec : bv 32 := 0x00a67633.
Lemma F_7b0ec : fetch_word AsanUbsan.M.loaded_segments (0x7b504 : word) = Some W_7b0ec.
Proof. vm_refl. Qed.
Lemma D_7b0ec : decode_any W_7b0ec = Some (Op ALU_AND 12 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0f0 : bv 32 := 0x04867263.
Lemma F_7b0f0 : fetch_word AsanUbsan.M.loaded_segments (0x7b508 : word) = Some W_7b0f0.
Proof. vm_refl. Qed.
Lemma D_7b0f0 : decode_any W_7b0f0 = Some (Branch BC_GEU 12 8 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0f4 : bv 32 := 0x000bc697.
Lemma F_7b0f4 : fetch_word AsanUbsan.M.loaded_segments (0x7b50c : word) = Some W_7b0f4.
Proof. vm_refl. Qed.
Lemma D_7b0f4 : decode_any W_7b0f4 = Some (Auipc 13 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0f8 : bv 32 := 0xfbc6b683.
Lemma F_7b0f8 : fetch_word AsanUbsan.M.loaded_segments (0x7b510 : word) = Some W_7b0f8.
Proof. vm_refl. Qed.
Lemma D_7b0f8 : decode_any W_7b0f8 = Some (Load SZ8 true 13 13 4028, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0fc : bv 32 := 0x000bc717.
Lemma F_7b0fc : fetch_word AsanUbsan.M.loaded_segments (0x7b514 : word) = Some W_7b0fc.
Proof. vm_refl. Qed.
Lemma D_7b0fc : decode_any W_7b0fc = Some (Auipc 14 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b100 : bv 32 := 0xfbc73703.
Lemma F_7b100 : fetch_word AsanUbsan.M.loaded_segments (0x7b518 : word) = Some W_7b100.
Proof. vm_refl. Qed.
Lemma D_7b100 : decode_any W_7b100 = Some (Load SZ8 true 14 14 4028, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b104 : bv 32 := 0x0006b803.
Lemma F_7b104 : fetch_word AsanUbsan.M.loaded_segments (0x7b51c : word) = Some W_7b104.
Proof. vm_refl. Qed.
Lemma D_7b104 : decode_any W_7b104 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b108 : bv 32 := 0x00073683.
Lemma F_7b108 : fetch_word AsanUbsan.M.loaded_segments (0x7b520 : word) = Some W_7b108.
Proof. vm_refl. Qed.
Lemma D_7b108 : decode_any W_7b108 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b10c : bv 32 := 0xfff80793.
Lemma F_7b10c : fetch_word AsanUbsan.M.loaded_segments (0x7b524 : word) = Some W_7b10c.
Proof. vm_refl. Qed.
Lemma D_7b10c : decode_any W_7b10c = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b110 : bv 32 := 0x0087f463.
Lemma F_7b110 : fetch_word AsanUbsan.M.loaded_segments (0x7b528 : word) = Some W_7b110.
Proof. vm_refl. Qed.
Lemma D_7b110 : decode_any W_7b110 = Some (Branch BC_GEU 15 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b118 : bv 32 := 0x000bc717.
Lemma F_7b118 : fetch_word AsanUbsan.M.loaded_segments (0x7b530 : word) = Some W_7b118.
Proof. vm_refl. Qed.
Lemma D_7b118 : decode_any W_7b118 = Some (Auipc 14 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b11c : bv 32 := 0xfa873703.
Lemma F_7b11c : fetch_word AsanUbsan.M.loaded_segments (0x7b534 : word) = Some W_7b11c.
Proof. vm_refl. Qed.
Lemma D_7b11c : decode_any W_7b11c = Some (Load SZ8 true 14 14 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b120 : bv 32 := 0x00073283.
Lemma F_7b120 : fetch_word AsanUbsan.M.loaded_segments (0x7b538 : word) = Some W_7b120.
Proof. vm_refl. Qed.
Lemma D_7b120 : decode_any W_7b120 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b124 : bv 32 := 0x0032d713.
Lemma F_7b124 : fetch_word AsanUbsan.M.loaded_segments (0x7b53c : word) = Some W_7b124.
Proof. vm_refl. Qed.
Lemma D_7b124 : decode_any W_7b124 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b128 : bv 32 := 0x00b708b3.
Lemma F_7b128 : fetch_word AsanUbsan.M.loaded_segments (0x7b540 : word) = Some W_7b128.
Proof. vm_refl. Qed.
Lemma D_7b128 : decode_any W_7b128 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b12c : bv 32 := 0x1282e063.
Lemma F_7b12c : fetch_word AsanUbsan.M.loaded_segments (0x7b544 : word) = Some W_7b12c.
Proof. vm_refl. Qed.
Lemma D_7b12c : decode_any W_7b12c = Some (Branch BC_LTU 5 8 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b130 : bv 32 := 0x1088fe63.
Lemma F_7b130 : fetch_word AsanUbsan.M.loaded_segments (0x7b548 : word) = Some W_7b130.
Proof. vm_refl. Qed.
Lemma D_7b130 : decode_any W_7b130 = Some (Branch BC_GEU 17 8 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b134 : bv 32 := 0x00848933.
Lemma F_7b134 : fetch_word AsanUbsan.M.loaded_segments (0x7b54c : word) = Some W_7b134.
Proof. vm_refl. Qed.
Lemma D_7b134 : decode_any W_7b134 = Some (Op ALU_ADD 18 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b138 : bv 32 := 0x05267263.
Lemma F_7b138 : fetch_word AsanUbsan.M.loaded_segments (0x7b550 : word) = Some W_7b138.
Proof. vm_refl. Qed.
Lemma D_7b138 : decode_any W_7b138 = Some (Branch BC_GEU 12 18 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b13c : bv 32 := 0x000bc617.
Lemma F_7b13c : fetch_word AsanUbsan.M.loaded_segments (0x7b554 : word) = Some W_7b13c.
Proof. vm_refl. Qed.
Lemma D_7b13c : decode_any W_7b13c = Some (Auipc 12 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b140 : bv 32 := 0xf7463603.
Lemma F_7b140 : fetch_word AsanUbsan.M.loaded_segments (0x7b558 : word) = Some W_7b140.
Proof. vm_refl. Qed.
Lemma D_7b140 : decode_any W_7b140 = Some (Load SZ8 true 12 12 3956, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b144 : bv 32 := 0x000bc697.
Lemma F_7b144 : fetch_word AsanUbsan.M.loaded_segments (0x7b55c : word) = Some W_7b144.
Proof. vm_refl. Qed.
Lemma D_7b144 : decode_any W_7b144 = Some (Auipc 13 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b148 : bv 32 := 0xf746b683.
Lemma F_7b148 : fetch_word AsanUbsan.M.loaded_segments (0x7b560 : word) = Some W_7b148.
Proof. vm_refl. Qed.
Lemma D_7b148 : decode_any W_7b148 = Some (Load SZ8 true 13 13 3956, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b14c : bv 32 := 0x00063783.
Lemma F_7b14c : fetch_word AsanUbsan.M.loaded_segments (0x7b564 : word) = Some W_7b14c.
Proof. vm_refl. Qed.
Lemma D_7b14c : decode_any W_7b14c = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b150 : bv 32 := 0x0006b603.
Lemma F_7b150 : fetch_word AsanUbsan.M.loaded_segments (0x7b568 : word) = Some W_7b150.
Proof. vm_refl. Qed.
Lemma D_7b150 : decode_any W_7b150 = Some (Load SZ8 true 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b154 : bv 32 := 0xfff78713.
Lemma F_7b154 : fetch_word AsanUbsan.M.loaded_segments (0x7b56c : word) = Some W_7b154.
Proof. vm_refl. Qed.
Lemma D_7b154 : decode_any W_7b154 = Some (OpImm ALU_ADD 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b158 : bv 32 := 0x01277463.
Lemma F_7b158 : fetch_word AsanUbsan.M.loaded_segments (0x7b570 : word) = Some W_7b158.
Proof. vm_refl. Qed.
Lemma D_7b158 : decode_any W_7b158 = Some (Branch BC_GEU 14 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b160 : bv 32 := 0x000bc697.
Lemma F_7b160 : fetch_word AsanUbsan.M.loaded_segments (0x7b578 : word) = Some W_7b160.
Proof. vm_refl. Qed.
Lemma D_7b160 : decode_any W_7b160 = Some (Auipc 13 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b164 : bv 32 := 0xf606b683.
Lemma F_7b164 : fetch_word AsanUbsan.M.loaded_segments (0x7b57c : word) = Some W_7b164.
Proof. vm_refl. Qed.
Lemma D_7b164 : decode_any W_7b164 = Some (Load SZ8 true 13 13 3936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b168 : bv 32 := 0x0006b883.
Lemma F_7b168 : fetch_word AsanUbsan.M.loaded_segments (0x7b580 : word) = Some W_7b168.
Proof. vm_refl. Qed.
Lemma D_7b168 : decode_any W_7b168 = Some (Load SZ8 true 17 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b16c : bv 32 := 0x0038d693.
Lemma F_7b16c : fetch_word AsanUbsan.M.loaded_segments (0x7b584 : word) = Some W_7b16c.
Proof. vm_refl. Qed.
Lemma D_7b16c : decode_any W_7b16c = Some (ShiftImm ALU_SRL 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b170 : bv 32 := 0x00b68833.
Lemma F_7b170 : fetch_word AsanUbsan.M.loaded_segments (0x7b588 : word) = Some W_7b170.
Proof. vm_refl. Qed.
Lemma D_7b170 : decode_any W_7b170 = Some (Op ALU_ADD 16 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b174 : bv 32 := 0x1328e463.
Lemma F_7b174 : fetch_word AsanUbsan.M.loaded_segments (0x7b58c : word) = Some W_7b174.
Proof. vm_refl. Qed.
Lemma D_7b174 : decode_any W_7b174 = Some (Branch BC_LTU 17 18 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b178 : bv 32 := 0x13287263.
Lemma F_7b178 : fetch_word AsanUbsan.M.loaded_segments (0x7b590 : word) = Some W_7b178.
Proof. vm_refl. Qed.
Lemma D_7b178 : decode_any W_7b178 = Some (Branch BC_GEU 16 18 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b17c : bv 32 := 0x23247863.
Lemma F_7b17c : fetch_word AsanUbsan.M.loaded_segments (0x7b594 : word) = Some W_7b17c.
Proof. vm_refl. Qed.
Lemma D_7b17c : decode_any W_7b17c = Some (Branch BC_GEU 8 18 560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b180 : bv 32 := 0x00740513.
Lemma F_7b180 : fetch_word AsanUbsan.M.loaded_segments (0x7b598 : word) = Some W_7b180.
Proof. vm_refl. Qed.
Lemma D_7b180 : decode_any W_7b180 = Some (OpImm ALU_ADD 10 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b184 : bv 32 := 0xff857513.
Lemma F_7b184 : fetch_word AsanUbsan.M.loaded_segments (0x7b59c : word) = Some W_7b184.
Proof. vm_refl. Qed.
Lemma D_7b184 : decode_any W_7b184 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b188 : bv 32 := 0xff897a13.
Lemma F_7b188 : fetch_word AsanUbsan.M.loaded_segments (0x7b5a0 : word) = Some W_7b188.
Proof. vm_refl. Qed.
Lemma D_7b188 : decode_any W_7b188 = Some (OpImm ALU_AND 20 18 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b18c : bv 32 := 0xa91ff0ef.
Lemma F_7b18c : fetch_word AsanUbsan.M.loaded_segments (0x7b5a4 : word) = Some W_7b18c.
Proof. vm_refl. Qed.
Lemma D_7b18c : decode_any W_7b18c = Some (Jal 1 2095760, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b190 : bv 32 := 0x00050993.
Lemma F_7b190 : fetch_word AsanUbsan.M.loaded_segments (0x7b5a8 : word) = Some W_7b190.
Proof. vm_refl. Qed.
Lemma D_7b190 : decode_any W_7b190 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b194 : bv 32 := 0x000a0513.
Lemma F_7b194 : fetch_word AsanUbsan.M.loaded_segments (0x7b5ac : word) = Some W_7b194.
Proof. vm_refl. Qed.
Lemma D_7b194 : decode_any W_7b194 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b198 : bv 32 := 0xa85ff0ef.
Lemma F_7b198 : fetch_word AsanUbsan.M.loaded_segments (0x7b5b0 : word) = Some W_7b198.
Proof. vm_refl. Qed.
Lemma D_7b198 : decode_any W_7b198 = Some (Jal 1 2095748, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b19c : bv 32 := 0x000ab583.
Lemma F_7b19c : fetch_word AsanUbsan.M.loaded_segments (0x7b5b4 : word) = Some W_7b19c.
Proof. vm_refl. Qed.
Lemma D_7b19c : decode_any W_7b19c = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b1a0 : bv 32 := 0x00345613.
Lemma F_7b1a0 : fetch_word AsanUbsan.M.loaded_segments (0x7b5b8 : word) = Some W_7b1a0.
Proof. vm_refl. Qed.
Lemma D_7b1a0 : decode_any W_7b1a0 = Some (ShiftImm ALU_SRL 12 8 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b1a4 : bv 32 := 0x00c58633.
Lemma F_7b1a4 : fetch_word AsanUbsan.M.loaded_segments (0x7b5bc : word) = Some W_7b1a4.
Proof. vm_refl. Qed.
Lemma D_7b1a4 : decode_any W_7b1a4 = Some (Op ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b1a8 : bv 32 := 0x00060603.
Lemma F_7b1a8 : fetch_word AsanUbsan.M.loaded_segments (0x7b5c0 : word) = Some W_7b1a8.
Proof. vm_refl. Qed.
Lemma D_7b1a8 : decode_any W_7b1a8 = Some (Load SZ1 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b1ac : bv 32 := 0x00060663.
Lemma F_7b1ac : fetch_word AsanUbsan.M.loaded_segments (0x7b5c4 : word) = Some W_7b1ac.
Proof. vm_refl. Qed.
Lemma D_7b1ac : decode_any W_7b1ac = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b1b0 : bv 32 := 0x00747693.
Lemma F_7b1b0 : fetch_word AsanUbsan.M.loaded_segments (0x7b5c8 : word) = Some W_7b1b0.
Proof. vm_refl. Qed.
Lemma D_7b1b0 : decode_any W_7b1b0 = Some (OpImm ALU_AND 13 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b1b4 : bv 32 := 0x02c6d063.
Lemma F_7b1b4 : fetch_word AsanUbsan.M.loaded_segments (0x7b5cc : word) = Some W_7b1b4.
Proof. vm_refl. Qed.
Lemma D_7b1b4 : decode_any W_7b1b4 = Some (Branch BC_GE 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b1b8 : bv 32 := 0xfff90913.
Lemma F_7b1b8 : fetch_word AsanUbsan.M.loaded_segments (0x7b5d0 : word) = Some W_7b1b8.
Proof. vm_refl. Qed.
Lemma D_7b1b8 : decode_any W_7b1b8 = Some (OpImm ALU_ADD 18 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b1bc : bv 32 := 0x00395613.
Lemma F_7b1bc : fetch_word AsanUbsan.M.loaded_segments (0x7b5d4 : word) = Some W_7b1bc.
Proof. vm_refl. Qed.
Lemma D_7b1bc : decode_any W_7b1bc = Some (ShiftImm ALU_SRL 12 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b1c0 : bv 32 := 0x00c585b3.
Lemma F_7b1c0 : fetch_word AsanUbsan.M.loaded_segments (0x7b5d8 : word) = Some W_7b1c0.
Proof. vm_refl. Qed.
Lemma D_7b1c0 : decode_any W_7b1c0 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b1c4 : bv 32 := 0x00058583.
Lemma F_7b1c4 : fetch_word AsanUbsan.M.loaded_segments (0x7b5dc : word) = Some W_7b1c4.
Proof. vm_refl. Qed.
Lemma D_7b1c4 : decode_any W_7b1c4 = Some (Load SZ1 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b1c8 : bv 32 := 0x04058263.
Lemma F_7b1c8 : fetch_word AsanUbsan.M.loaded_segments (0x7b5e0 : word) = Some W_7b1c8.
Proof. vm_refl. Qed.
Lemma D_7b1c8 : decode_any W_7b1c8 = Some (Branch BC_EQ 11 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b1cc : bv 32 := 0x00797613.
Lemma F_7b1cc : fetch_word AsanUbsan.M.loaded_segments (0x7b5e4 : word) = Some W_7b1cc.
Proof. vm_refl. Qed.
Lemma D_7b1cc : decode_any W_7b1cc = Some (OpImm ALU_AND 12 18 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b1d0 : bv 32 := 0x02b64e63.
Lemma F_7b1d0 : fetch_word AsanUbsan.M.loaded_segments (0x7b5e8 : word) = Some W_7b1d0.
Proof. vm_refl. Qed.
Lemma D_7b1d0 : decode_any W_7b1d0 = Some (Branch BC_LT 12 11 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b20c : bv 32 := 0x00a9fa63.
Lemma F_7b20c : fetch_word AsanUbsan.M.loaded_segments (0x7b624 : word) = Some W_7b20c.
Proof. vm_refl. Qed.
Lemma D_7b20c : decode_any W_7b20c = Some (Branch BC_GEU 19 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b210 : bv 32 := 0x413505b3.
Lemma F_7b210 : fetch_word AsanUbsan.M.loaded_segments (0x7b628 : word) = Some W_7b210.
Proof. vm_refl. Qed.
Lemma D_7b210 : decode_any W_7b210 = Some (Op ALU_SUB 11 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b214 : bv 32 := 0x00098513.
Lemma F_7b214 : fetch_word AsanUbsan.M.loaded_segments (0x7b62c : word) = Some W_7b214.
Proof. vm_refl. Qed.
Lemma D_7b214 : decode_any W_7b214 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b218 : bv 32 := 0x37c100ef.
Lemma F_7b218 : fetch_word AsanUbsan.M.loaded_segments (0x7b630 : word) = Some W_7b218.
Proof. vm_refl. Qed.
Lemma D_7b218 : decode_any W_7b218 = Some (Jal 1 66428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b21c : bv 32 := 0xfa050ce3.
Lemma F_7b21c : fetch_word AsanUbsan.M.loaded_segments (0x7b634 : word) = Some W_7b21c.
Proof. vm_refl. Qed.
Lemma D_7b21c : decode_any W_7b21c = Some (Branch BC_EQ 10 0 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b220 : bv 32 := 0x00000413.
Lemma F_7b220 : fetch_word AsanUbsan.M.loaded_segments (0x7b638 : word) = Some W_7b220.
Proof. vm_refl. Qed.
Lemma D_7b220 : decode_any W_7b220 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b224 : bv 32 := 0x00040513.
Lemma F_7b224 : fetch_word AsanUbsan.M.loaded_segments (0x7b63c : word) = Some W_7b224.
Proof. vm_refl. Qed.
Lemma D_7b224 : decode_any W_7b224 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b228 : bv 32 := 0x03813083.
Lemma F_7b228 : fetch_word AsanUbsan.M.loaded_segments (0x7b640 : word) = Some W_7b228.
Proof. vm_refl. Qed.
Lemma D_7b228 : decode_any W_7b228 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b22c : bv 32 := 0x03013403.
Lemma F_7b22c : fetch_word AsanUbsan.M.loaded_segments (0x7b644 : word) = Some W_7b22c.
Proof. vm_refl. Qed.
Lemma D_7b22c : decode_any W_7b22c = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b230 : bv 32 := 0x02813483.
Lemma F_7b230 : fetch_word AsanUbsan.M.loaded_segments (0x7b648 : word) = Some W_7b230.
Proof. vm_refl. Qed.
Lemma D_7b230 : decode_any W_7b230 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b234 : bv 32 := 0x02013903.
Lemma F_7b234 : fetch_word AsanUbsan.M.loaded_segments (0x7b64c : word) = Some W_7b234.
Proof. vm_refl. Qed.
Lemma D_7b234 : decode_any W_7b234 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b238 : bv 32 := 0x01813983.
Lemma F_7b238 : fetch_word AsanUbsan.M.loaded_segments (0x7b650 : word) = Some W_7b238.
Proof. vm_refl. Qed.
Lemma D_7b238 : decode_any W_7b238 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b23c : bv 32 := 0x01013a03.
Lemma F_7b23c : fetch_word AsanUbsan.M.loaded_segments (0x7b654 : word) = Some W_7b23c.
Proof. vm_refl. Qed.
Lemma D_7b23c : decode_any W_7b23c = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b240 : bv 32 := 0x00813a83.
Lemma F_7b240 : fetch_word AsanUbsan.M.loaded_segments (0x7b658 : word) = Some W_7b240.
Proof. vm_refl. Qed.
Lemma D_7b240 : decode_any W_7b240 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b244 : bv 32 := 0x04010113.
Lemma F_7b244 : fetch_word AsanUbsan.M.loaded_segments (0x7b65c : word) = Some W_7b244.
Proof. vm_refl. Qed.
Lemma D_7b244 : decode_any W_7b244 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b248 : bv 32 := 0x00008067.
Lemma F_7b248 : fetch_word AsanUbsan.M.loaded_segments (0x7b660 : word) = Some W_7b248.
Proof. vm_refl. Qed.
Lemma D_7b248 : decode_any W_7b248 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
