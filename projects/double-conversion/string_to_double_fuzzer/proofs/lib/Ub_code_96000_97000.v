(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation USEGS := ImgU.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_960fc : bv 32 := 0xfd010113.
Lemma F_960fc : fetch_word USEGS (0x960fc : word) = Some W_960fc.
Proof. vm_refl. Qed.
Lemma D_960fc : decode_any W_960fc = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96100 : bv 32 := 0x02113423.
Lemma F_96100 : fetch_word USEGS (0x96100 : word) = Some W_96100.
Proof. vm_refl. Qed.
Lemma D_96100 : decode_any W_96100 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96104 : bv 32 := 0x02813023.
Lemma F_96104 : fetch_word USEGS (0x96104 : word) = Some W_96104.
Proof. vm_refl. Qed.
Lemma D_96104 : decode_any W_96104 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96108 : bv 32 := 0x00913c23.
Lemma F_96108 : fetch_word USEGS (0x96108 : word) = Some W_96108.
Proof. vm_refl. Qed.
Lemma D_96108 : decode_any W_96108 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9610c : bv 32 := 0x01213823.
Lemma F_9610c : fetch_word USEGS (0x9610c : word) = Some W_9610c.
Proof. vm_refl. Qed.
Lemma D_9610c : decode_any W_9610c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96110 : bv 32 := 0x01313423.
Lemma F_96110 : fetch_word USEGS (0x96110 : word) = Some W_96110.
Proof. vm_refl. Qed.
Lemma D_96110 : decode_any W_96110 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96114 : bv 32 := 0x00060413.
Lemma F_96114 : fetch_word USEGS (0x96114 : word) = Some W_96114.
Proof. vm_refl. Qed.
Lemma D_96114 : decode_any W_96114 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96118 : bv 32 := 0x00058493.
Lemma F_96118 : fetch_word USEGS (0x96118 : word) = Some W_96118.
Proof. vm_refl. Qed.
Lemma D_96118 : decode_any W_96118 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9611c : bv 32 := 0x00050913.
Lemma F_9611c : fetch_word USEGS (0x9611c : word) = Some W_9611c.
Proof. vm_refl. Qed.
Lemma D_9611c : decode_any W_9611c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96120 : bv 32 := 0x00359513.
Lemma F_96120 : fetch_word USEGS (0x96120 : word) = Some W_96120.
Proof. vm_refl. Qed.
Lemma D_96120 : decode_any W_96120 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96124 : bv 32 := 0x00a60533.
Lemma F_96124 : fetch_word USEGS (0x96124 : word) = Some W_96124.
Proof. vm_refl. Qed.
Lemma D_96124 : decode_any W_96124 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96128 : bv 32 := 0x00850993.
Lemma F_96128 : fetch_word USEGS (0x96128 : word) = Some W_96128.
Proof. vm_refl. Qed.
Lemma D_96128 : decode_any W_96128 = Some (OpImm ALU_ADD 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9612c : bv 32 := 0xf25ff0ef.
Lemma F_9612c : fetch_word USEGS (0x9612c : word) = Some W_9612c.
Proof. vm_refl. Qed.
Lemma D_9612c : decode_any W_9612c = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96130 : bv 32 := 0x00048513.
Lemma F_96130 : fetch_word USEGS (0x96130 : word) = Some W_96130.
Proof. vm_refl. Qed.
Lemma D_96130 : decode_any W_96130 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96134 : bv 32 := 0x00040593.
Lemma F_96134 : fetch_word USEGS (0x96134 : word) = Some W_96134.
Proof. vm_refl. Qed.
Lemma D_96134 : decode_any W_96134 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96138 : bv 32 := 0x00098613.
Lemma F_96138 : fetch_word USEGS (0x96138 : word) = Some W_96138.
Proof. vm_refl. Qed.
Lemma D_96138 : decode_any W_96138 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9613c : bv 32 := 0x000900e7.
Lemma F_9613c : fetch_word USEGS (0x9613c : word) = Some W_9613c.
Proof. vm_refl. Qed.
Lemma D_9613c : decode_any W_9613c = Some (Jalr 1 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96140 : bv 32 := 0x64c000ef.
Lemma F_96140 : fetch_word USEGS (0x96140 : word) = Some W_96140.
Proof. vm_refl. Qed.
Lemma D_96140 : decode_any W_96140 = Some (Jal 1 1612, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96144 : bv 32 := 0xfc010113.
Lemma F_96144 : fetch_word USEGS (0x96144 : word) = Some W_96144.
Proof. vm_refl. Qed.
Lemma D_96144 : decode_any W_96144 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96148 : bv 32 := 0x02113c23.
Lemma F_96148 : fetch_word USEGS (0x96148 : word) = Some W_96148.
Proof. vm_refl. Qed.
Lemma D_96148 : decode_any W_96148 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9614c : bv 32 := 0x02813823.
Lemma F_9614c : fetch_word USEGS (0x9614c : word) = Some W_9614c.
Proof. vm_refl. Qed.
Lemma D_9614c : decode_any W_9614c = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96150 : bv 32 := 0x02913423.
Lemma F_96150 : fetch_word USEGS (0x96150 : word) = Some W_96150.
Proof. vm_refl. Qed.
Lemma D_96150 : decode_any W_96150 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96154 : bv 32 := 0x03213023.
Lemma F_96154 : fetch_word USEGS (0x96154 : word) = Some W_96154.
Proof. vm_refl. Qed.
Lemma D_96154 : decode_any W_96154 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96158 : bv 32 := 0x01313c23.
Lemma F_96158 : fetch_word USEGS (0x96158 : word) = Some W_96158.
Proof. vm_refl. Qed.
Lemma D_96158 : decode_any W_96158 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9615c : bv 32 := 0x01413823.
Lemma F_9615c : fetch_word USEGS (0x9615c : word) = Some W_9615c.
Proof. vm_refl. Qed.
Lemma D_9615c : decode_any W_9615c = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96160 : bv 32 := 0x01513423.
Lemma F_96160 : fetch_word USEGS (0x96160 : word) = Some W_96160.
Proof. vm_refl. Qed.
Lemma D_96160 : decode_any W_96160 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96164 : bv 32 := 0x02853683.
Lemma F_96164 : fetch_word USEGS (0x96164 : word) = Some W_96164.
Proof. vm_refl. Qed.
Lemma D_96164 : decode_any W_96164 = Some (Load SZ8 true 13 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96168 : bv 32 := 0x0004f597.
Lemma F_96168 : fetch_word USEGS (0x96168 : word) = Some W_96168.
Proof. vm_refl. Qed.
Lemma D_96168 : decode_any W_96168 = Some (Auipc 11 79, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_96178 : bv 32 := 0x0c068e63.
Lemma F_96178 : fetch_word USEGS (0x96178 : word) = Some W_96178.
Proof. vm_refl. Qed.
Lemma D_96178 : decode_any W_96178 = Some (Branch BC_EQ 13 0 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_96180 : bv 32 := 0x00000893.
Lemma F_96180 : fetch_word USEGS (0x96180 : word) = Some W_96180.
Proof. vm_refl. Qed.
Lemma D_96180 : decode_any W_96180 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96184 : bv 32 := 0x0001d717.
Lemma F_96184 : fetch_word USEGS (0x96184 : word) = Some W_96184.
Proof. vm_refl. Qed.
Lemma D_96184 : decode_any W_96184 = Some (Auipc 14 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96188 : bv 32 := 0x01853783.
Lemma F_96188 : fetch_word USEGS (0x96188 : word) = Some W_96188.
Proof. vm_refl. Qed.
Lemma D_96188 : decode_any W_96188 = Some (Load SZ8 true 15 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9618c : bv 32 := 0x02053503.
Lemma F_9618c : fetch_word USEGS (0x9618c : word) = Some W_9618c.
Proof. vm_refl. Qed.
Lemma D_9618c : decode_any W_9618c = Some (Load SZ8 true 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96190 : bv 32 := 0x00600813.
Lemma F_96190 : fetch_word USEGS (0x96190 : word) = Some W_96190.
Proof. vm_refl. Qed.
Lemma D_96190 : decode_any W_96190 = Some (OpImm ALU_ADD 16 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96194 : bv 32 := 0x0001c297.
Lemma F_96194 : fetch_word USEGS (0x96194 : word) = Some W_96194.
Proof. vm_refl. Qed.
Lemma D_96194 : decode_any W_96194 = Some (Auipc 5 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96198 : bv 32 := 0x3f476f03.
Lemma F_96198 : fetch_word USEGS (0x96198 : word) = Some W_96198.
Proof. vm_refl. Qed.
Lemma D_96198 : decode_any W_96198 = Some (Load SZ4 false 30 14 1012, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9619c : bv 32 := 0xfac2b283.
Lemma F_9619c : fetch_word USEGS (0x9619c : word) = Some W_9619c.
Proof. vm_refl. Qed.
Lemma D_9619c : decode_any W_9619c = Some (Load SZ8 true 5 5 4012, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961a0 : bv 32 := 0x00200313.
Lemma F_961a0 : fetch_word USEGS (0x961a0 : word) = Some W_961a0.
Proof. vm_refl. Qed.
Lemma D_961a0 : decode_any W_961a0 = Some (OpImm ALU_ADD 6 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961a4 : bv 32 := 0x00700393.
Lemma F_961a4 : fetch_word USEGS (0x961a4 : word) = Some W_961a4.
Proof. vm_refl. Qed.
Lemma D_961a4 : decode_any W_961a4 = Some (OpImm ALU_ADD 7 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961a8 : bv 32 := 0x6474ee37.
Lemma F_961a8 : fetch_word USEGS (0x961a8 : word) = Some W_961a8.
Proof. vm_refl. Qed.
Lemma D_961a8 : decode_any W_961a8 = Some (Lui 28 411470, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961ac : bv 32 := 0x551e0e1b.
Lemma F_961ac : fetch_word USEGS (0x961ac : word) = Some W_961ac.
Proof. vm_refl. Qed.
Lemma D_961ac : decode_any W_961ac = Some (OpImm32 28 28 1361, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961b0 : bv 32 := 0x00078e93.
Lemma F_961b0 : fetch_word USEGS (0x961b0 : word) = Some W_961b0.
Proof. vm_refl. Qed.
Lemma D_961b0 : decode_any W_961b0 = Some (OpImm ALU_ADD 29 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961b4 : bv 32 := 0x0180006f.
Lemma F_961b4 : fetch_word USEGS (0x961b4 : word) = Some W_961b4.
Proof. vm_refl. Qed.
Lemma D_961b4 : decode_any W_961b4 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_961c0 : bv 32 := 0xfff68693.
Lemma F_961c0 : fetch_word USEGS (0x961c0 : word) = Some W_961c0.
Proof. vm_refl. Qed.
Lemma D_961c0 : decode_any W_961c0 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961c4 : bv 32 := 0x00ae8eb3.
Lemma F_961c4 : fetch_word USEGS (0x961c4 : word) = Some W_961c4.
Proof. vm_refl. Qed.
Lemma D_961c4 : decode_any W_961c4 = Some (Op ALU_ADD 29 29 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961c8 : bv 32 := 0x04068a63.
Lemma F_961c8 : fetch_word USEGS (0x961c8 : word) = Some W_961c8.
Proof. vm_refl. Qed.
Lemma D_961c8 : decode_any W_961c8 = Some (Branch BC_EQ 13 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961cc : bv 32 := 0x000ea403.
Lemma F_961cc : fetch_word USEGS (0x961cc : word) = Some W_961cc.
Proof. vm_refl. Qed.
Lemma D_961cc : decode_any W_961cc = Some (Load SZ4 true 8 29 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961d0 : bv 32 := 0xff0404e3.
Lemma F_961d0 : fetch_word USEGS (0x961d0 : word) = Some W_961d0.
Proof. vm_refl. Qed.
Lemma D_961d0 : decode_any W_961d0 = Some (Branch BC_EQ 8 16 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961d4 : bv 32 := 0x00028a63.
Lemma F_961d4 : fetch_word USEGS (0x961d4 : word) = Some W_961d4.
Proof. vm_refl. Qed.
Lemma D_961d4 : decode_any W_961d4 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961e8 : bv 32 := 0x000e8f93.
Lemma F_961e8 : fetch_word USEGS (0x961e8 : word) = Some W_961e8.
Proof. vm_refl. Qed.
Lemma D_961e8 : decode_any W_961e8 = Some (OpImm ALU_ADD 31 29 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961ec : bv 32 := 0x00740463.
Lemma F_961ec : fetch_word USEGS (0x961ec : word) = Some W_961ec.
Proof. vm_refl. Qed.
Lemma D_961ec : decode_any W_961ec = Some (Branch BC_EQ 8 7 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961f0 : bv 32 := 0x00088f93.
Lemma F_961f0 : fetch_word USEGS (0x961f0 : word) = Some W_961f0.
Proof. vm_refl. Qed.
Lemma D_961f0 : decode_any W_961f0 = Some (OpImm ALU_ADD 31 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961f4 : bv 32 := 0x03c41063.
Lemma F_961f4 : fetch_word USEGS (0x961f4 : word) = Some W_961f4.
Proof. vm_refl. Qed.
Lemma D_961f4 : decode_any W_961f4 = Some (Branch BC_NE 8 28 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961f8 : bv 32 := 0x028eb883.
Lemma F_961f8 : fetch_word USEGS (0x961f8 : word) = Some W_961f8.
Proof. vm_refl. Qed.
Lemma D_961f8 : decode_any W_961f8 = Some (Load SZ8 true 17 29 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961fc : bv 32 := 0x011f7c63.
Lemma F_961fc : fetch_word USEGS (0x961fc : word) = Some W_961fc.
Proof. vm_refl. Qed.
Lemma D_961fc : decode_any W_961fc = Some (Branch BC_GEU 30 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96214 : bv 32 := 0x000f8893.
Lemma F_96214 : fetch_word USEGS (0x96214 : word) = Some W_96214.
Proof. vm_refl. Qed.
Lemma D_96214 : decode_any W_96214 = Some (OpImm ALU_ADD 17 31 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96218 : bv 32 := 0xfa9ff06f.
Lemma F_96218 : fetch_word USEGS (0x96218 : word) = Some W_96218.
Proof. vm_refl. Qed.
Lemma D_96218 : decode_any W_96218 = Some (Jal 0 2097064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9621c : bv 32 := 0x02088c63.
Lemma F_9621c : fetch_word USEGS (0x9621c : word) = Some W_9621c.
Proof. vm_refl. Qed.
Lemma D_9621c : decode_any W_9621c = Some (Branch BC_EQ 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_96264 : bv 32 := 0xfff50793.
Lemma F_96264 : fetch_word USEGS (0x96264 : word) = Some W_96264.
Proof. vm_refl. Qed.
Lemma D_96264 : decode_any W_96264 = Some (OpImm ALU_ADD 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96268 : bv 32 := 0x40e00733.
Lemma F_96268 : fetch_word USEGS (0x96268 : word) = Some W_96268.
Proof. vm_refl. Qed.
Lemma D_96268 : decode_any W_96268 = Some (Op ALU_SUB 14 0 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_96270 : bv 32 := 0x00e7f733.
Lemma F_96270 : fetch_word USEGS (0x96270 : word) = Some W_96270.
Proof. vm_refl. Qed.
Lemma D_96270 : decode_any W_96270 = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96274 : bv 32 := 0x00700793.
Lemma F_96274 : fetch_word USEGS (0x96274 : word) = Some W_96274.
Proof. vm_refl. Qed.
Lemma D_96274 : decode_any W_96274 = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96278 : bv 32 := 0x00d706b3.
Lemma F_96278 : fetch_word USEGS (0x96278 : word) = Some W_96278.
Proof. vm_refl. Qed.
Lemma D_96278 : decode_any W_96278 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_96284 : bv 32 := 0x00a7e663.
Lemma F_96284 : fetch_word USEGS (0x96284 : word) = Some W_96284.
Proof. vm_refl. Qed.
Lemma D_96284 : decode_any W_96284 = Some (Branch BC_LTU 15 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96288 : bv 32 := 0x00800513.
Lemma F_96288 : fetch_word USEGS (0x96288 : word) = Some W_96288.
Proof. vm_refl. Qed.
Lemma D_96288 : decode_any W_96288 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_962a4 : bv 32 := 0xff85f593.
Lemma F_962a4 : fetch_word USEGS (0x962a4 : word) = Some W_962a4.
Proof. vm_refl. Qed.
Lemma D_962a4 : decode_any W_962a4 = Some (OpImm ALU_AND 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_962a8 : bv 32 := 0x00b4bc23.
Lemma F_962a8 : fetch_word USEGS (0x962a8 : word) = Some W_962a8.
Proof. vm_refl. Qed.
Lemma D_962a8 : decode_any W_962a8 = Some (Store SZ8 9 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_962ac : bv 32 := 0x02a4b023.
Lemma F_962ac : fetch_word USEGS (0x962ac : word) = Some W_962ac.
Proof. vm_refl. Qed.
Lemma D_962ac : decode_any W_962ac = Some (Store SZ8 9 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_962b0 : bv 32 := 0x02d5ea63.
Lemma F_962b0 : fetch_word USEGS (0x962b0 : word) = Some W_962b0.
Proof. vm_refl. Qed.
Lemma D_962b0 : decode_any W_962b0 = Some (Branch BC_LTU 11 13 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_962ec : bv 32 := 0x0284b603.
Lemma F_962ec : fetch_word USEGS (0x962ec : word) = Some W_962ec.
Proof. vm_refl. Qed.
Lemma D_962ec : decode_any W_962ec = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_96318 : bv 32 := 0x0c890413.
Lemma F_96318 : fetch_word USEGS (0x96318 : word) = Some W_96318.
Proof. vm_refl. Qed.
Lemma D_96318 : decode_any W_96318 = Some (OpImm ALU_ADD 8 18 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_9636c : bv 32 := 0x01293023.
Lemma F_9636c : fetch_word USEGS (0x9636c : word) = Some W_9636c.
Proof. vm_refl. Qed.
Lemma D_9636c : decode_any W_9636c = Some (Store SZ8 18 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96370 : bv 32 := 0x00040513.
Lemma F_96370 : fetch_word USEGS (0x96370 : word) = Some W_96370.
Proof. vm_refl. Qed.
Lemma D_96370 : decode_any W_96370 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96374 : bv 32 := 0x0d4130ef.
Lemma F_96374 : fetch_word USEGS (0x96374 : word) = Some W_96374.
Proof. vm_refl. Qed.
Lemma D_96374 : decode_any W_96374 = Some (Jal 1 78036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96378 : bv 32 := 0x04054a63.
Lemma F_96378 : fetch_word USEGS (0x96378 : word) = Some W_96378.
Proof. vm_refl. Qed.
Lemma D_96378 : decode_any W_96378 = Some (Branch BC_LT 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9637c : bv 32 := 0x00051663.
Lemma F_9637c : fetch_word USEGS (0x9637c : word) = Some W_9637c.
Proof. vm_refl. Qed.
Lemma D_9637c : decode_any W_9637c = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96380 : bv 32 := 0x00100513.
Lemma F_96380 : fetch_word USEGS (0x96380 : word) = Some W_96380.
Proof. vm_refl. Qed.
Lemma D_96380 : decode_any W_96380 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96384 : bv 32 := 0x00a48023.
Lemma F_96384 : fetch_word USEGS (0x96384 : word) = Some W_96384.
Proof. vm_refl. Qed.
Lemma D_96384 : decode_any W_96384 = Some (Store SZ1 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96388 : bv 32 := 0x00200513.
Lemma F_96388 : fetch_word USEGS (0x96388 : word) = Some W_96388.
Proof. vm_refl. Qed.
Lemma D_96388 : decode_any W_96388 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9638c : bv 32 := 0x0004f597.
Lemma F_9638c : fetch_word USEGS (0x9638c : word) = Some W_9638c.
Proof. vm_refl. Qed.
Lemma D_9638c : decode_any W_9638c = Some (Auipc 11 79, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96390 : bv 32 := 0x02a92423.
Lemma F_96390 : fetch_word USEGS (0x96390 : word) = Some W_96390.
Proof. vm_refl. Qed.
Lemma D_96390 : decode_any W_96390 = Some (Store SZ4 18 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96394 : bv 32 := 0x06000893.
Lemma F_96394 : fetch_word USEGS (0x96394 : word) = Some W_96394.
Proof. vm_refl. Qed.
Lemma D_96394 : decode_any W_96394 = Some (OpImm ALU_ADD 17 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96398 : bv 32 := 0xc9458513.
Lemma F_96398 : fetch_word USEGS (0x96398 : word) = Some W_96398.
Proof. vm_refl. Qed.
Lemma D_96398 : decode_any W_96398 = Some (OpImm ALU_ADD 10 11 3220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9639c : bv 32 := 0x03848593.
Lemma F_9639c : fetch_word USEGS (0x9639c : word) = Some W_9639c.
Proof. vm_refl. Qed.
Lemma D_9639c : decode_any W_9639c = Some (OpImm ALU_ADD 11 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963a0 : bv 32 := 0x00000073.
Lemma F_963a0 : fetch_word USEGS (0x963a0 : word) = Some W_963a0.
Proof. vm_refl. Qed.
Lemma D_963a0 : decode_any W_963a0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_963a0 : is_ecall W_963a0 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_963a4 : bv 32 := 0x07890613.
Lemma F_963a4 : fetch_word USEGS (0x963a4 : word) = Some W_963a4.
Proof. vm_refl. Qed.
Lemma D_963a4 : decode_any W_963a4 = Some (OpImm ALU_ADD 12 18 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963a8 : bv 32 := 0x02a92023.
Lemma F_963a8 : fetch_word USEGS (0x963a8 : word) = Some W_963a8.
Proof. vm_refl. Qed.
Lemma D_963a8 : decode_any W_963a8 = Some (Store SZ4 18 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963ac : bv 32 := 0x08b93c23.
Lemma F_963ac : fetch_word USEGS (0x963ac : word) = Some W_963ac.
Proof. vm_refl. Qed.
Lemma D_963ac : decode_any W_963ac = Some (Store SZ8 18 11 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963b0 : bv 32 := 0x06c93c23.
Lemma F_963b0 : fetch_word USEGS (0x963b0 : word) = Some W_963b0.
Proof. vm_refl. Qed.
Lemma D_963b0 : decode_any W_963b0 = Some (Store SZ8 18 12 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963b4 : bv 32 := 0x0004f517.
Lemma F_963b4 : fetch_word USEGS (0x963b4 : word) = Some W_963b4.
Proof. vm_refl. Qed.
Lemma D_963b4 : decode_any W_963b4 = Some (Auipc 10 79, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963b8 : bv 32 := 0xedc53503.
Lemma F_963b8 : fetch_word USEGS (0x963b8 : word) = Some W_963b8.
Proof. vm_refl. Qed.
Lemma D_963b8 : decode_any W_963b8 = Some (Load SZ8 true 10 10 3804, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963bc : bv 32 := 0x01293423.
Lemma F_963bc : fetch_word USEGS (0x963bc : word) = Some W_963bc.
Proof. vm_refl. Qed.
Lemma D_963bc : decode_any W_963bc = Some (Store SZ8 18 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963c0 : bv 32 := 0x01293823.
Lemma F_963c0 : fetch_word USEGS (0x963c0 : word) = Some W_963c0.
Proof. vm_refl. Qed.
Lemma D_963c0 : decode_any W_963c0 = Some (Store SZ8 18 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963c4 : bv 32 := 0x00a93c23.
Lemma F_963c4 : fetch_word USEGS (0x963c4 : word) = Some W_963c4.
Proof. vm_refl. Qed.
Lemma D_963c4 : decode_any W_963c4 = Some (Store SZ8 18 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963c8 : bv 32 := 0x0080006f.
Lemma F_963c8 : fetch_word USEGS (0x963c8 : word) = Some W_963c8.
Proof. vm_refl. Qed.
Lemma D_963c8 : decode_any W_963c8 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963d0 : bv 32 := 0x03813083.
Lemma F_963d0 : fetch_word USEGS (0x963d0 : word) = Some W_963d0.
Proof. vm_refl. Qed.
Lemma D_963d0 : decode_any W_963d0 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963d4 : bv 32 := 0x03013403.
Lemma F_963d4 : fetch_word USEGS (0x963d4 : word) = Some W_963d4.
Proof. vm_refl. Qed.
Lemma D_963d4 : decode_any W_963d4 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963d8 : bv 32 := 0x02813483.
Lemma F_963d8 : fetch_word USEGS (0x963d8 : word) = Some W_963d8.
Proof. vm_refl. Qed.
Lemma D_963d8 : decode_any W_963d8 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963dc : bv 32 := 0x02013903.
Lemma F_963dc : fetch_word USEGS (0x963dc : word) = Some W_963dc.
Proof. vm_refl. Qed.
Lemma D_963dc : decode_any W_963dc = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963e0 : bv 32 := 0x01813983.
Lemma F_963e0 : fetch_word USEGS (0x963e0 : word) = Some W_963e0.
Proof. vm_refl. Qed.
Lemma D_963e0 : decode_any W_963e0 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963e4 : bv 32 := 0x01013a03.
Lemma F_963e4 : fetch_word USEGS (0x963e4 : word) = Some W_963e4.
Proof. vm_refl. Qed.
Lemma D_963e4 : decode_any W_963e4 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963e8 : bv 32 := 0x00813a83.
Lemma F_963e8 : fetch_word USEGS (0x963e8 : word) = Some W_963e8.
Proof. vm_refl. Qed.
Lemma D_963e8 : decode_any W_963e8 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963ec : bv 32 := 0x04010113.
Lemma F_963ec : fetch_word USEGS (0x963ec : word) = Some W_963ec.
Proof. vm_refl. Qed.
Lemma D_963ec : decode_any W_963ec = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963f0 : bv 32 := 0x00008067.
Lemma F_963f0 : fetch_word USEGS (0x963f0 : word) = Some W_963f0.
Proof. vm_refl. Qed.
Lemma D_963f0 : decode_any W_963f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96494 : bv 32 := 0x00050593.
Lemma F_96494 : fetch_word USEGS (0x96494 : word) = Some W_96494.
Proof. vm_refl. Qed.
Lemma D_96494 : decode_any W_96494 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96498 : bv 32 := 0x05e00893.
Lemma F_96498 : fetch_word USEGS (0x96498 : word) = Some W_96498.
Proof. vm_refl. Qed.
Lemma D_96498 : decode_any W_96498 = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9649c : bv 32 := 0x00000073.
Lemma F_9649c : fetch_word USEGS (0x9649c : word) = Some W_9649c.
Proof. vm_refl. Qed.
Lemma D_9649c : decode_any W_9649c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_9649c : is_ecall W_9649c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_964e0 : bv 32 := 0xfd010113.
Lemma F_964e0 : fetch_word USEGS (0x964e0 : word) = Some W_964e0.
Proof. vm_refl. Qed.
Lemma D_964e0 : decode_any W_964e0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_964e4 : bv 32 := 0x02113423.
Lemma F_964e4 : fetch_word USEGS (0x964e4 : word) = Some W_964e4.
Proof. vm_refl. Qed.
Lemma D_964e4 : decode_any W_964e4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_964e8 : bv 32 := 0x02813023.
Lemma F_964e8 : fetch_word USEGS (0x964e8 : word) = Some W_964e8.
Proof. vm_refl. Qed.
Lemma D_964e8 : decode_any W_964e8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_964ec : bv 32 := 0x00913c23.
Lemma F_964ec : fetch_word USEGS (0x964ec : word) = Some W_964ec.
Proof. vm_refl. Qed.
Lemma D_964ec : decode_any W_964ec = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_964f0 : bv 32 := 0x01213823.
Lemma F_964f0 : fetch_word USEGS (0x964f0 : word) = Some W_964f0.
Proof. vm_refl. Qed.
Lemma D_964f0 : decode_any W_964f0 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_964f4 : bv 32 := 0x01313423.
Lemma F_964f4 : fetch_word USEGS (0x964f4 : word) = Some W_964f4.
Proof. vm_refl. Qed.
Lemma D_964f4 : decode_any W_964f4 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_964f8 : bv 32 := 0x0004f517.
Lemma F_964f8 : fetch_word USEGS (0x964f8 : word) = Some W_964f8.
Proof. vm_refl. Qed.
Lemma D_964f8 : decode_any W_964f8 = Some (Auipc 10 79, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_964fc : bv 32 := 0xb6850913.
Lemma F_964fc : fetch_word USEGS (0x964fc : word) = Some W_964fc.
Proof. vm_refl. Qed.
Lemma D_964fc : decode_any W_964fc = Some (OpImm ALU_ADD 18 10 2920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96500 : bv 32 := 0x00490413.
Lemma F_96500 : fetch_word USEGS (0x96500 : word) = Some W_96500.
Proof. vm_refl. Qed.
Lemma D_96500 : decode_any W_96500 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96504 : bv 32 := 0x00040513.
Lemma F_96504 : fetch_word USEGS (0x96504 : word) = Some W_96504.
Proof. vm_refl. Qed.
Lemma D_96504 : decode_any W_96504 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96508 : bv 32 := 0x510110ef.
Lemma F_96508 : fetch_word USEGS (0x96508 : word) = Some W_96508.
Proof. vm_refl. Qed.
Lemma D_96508 : decode_any W_96508 = Some (Jal 1 70928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9650c : bv 32 := 0x01093503.
Lemma F_9650c : fetch_word USEGS (0x9650c : word) = Some W_9650c.
Proof. vm_refl. Qed.
Lemma D_9650c : decode_any W_9650c = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96510 : bv 32 := 0x06050863.
Lemma F_96510 : fetch_word USEGS (0x96510 : word) = Some W_96510.
Proof. vm_refl. Qed.
Lemma D_96510 : decode_any W_96510 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96580 : bv 32 := 0x00100513.
Lemma F_96580 : fetch_word USEGS (0x96580 : word) = Some W_96580.
Proof. vm_refl. Qed.
Lemma D_96580 : decode_any W_96580 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96584 : bv 32 := 0x00a90023.
Lemma F_96584 : fetch_word USEGS (0x96584 : word) = Some W_96584.
Proof. vm_refl. Qed.
Lemma D_96584 : decode_any W_96584 = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96588 : bv 32 := 0x00040513.
Lemma F_96588 : fetch_word USEGS (0x96588 : word) = Some W_96588.
Proof. vm_refl. Qed.
Lemma D_96588 : decode_any W_96588 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9658c : bv 32 := 0x02813083.
Lemma F_9658c : fetch_word USEGS (0x9658c : word) = Some W_9658c.
Proof. vm_refl. Qed.
Lemma D_9658c : decode_any W_9658c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96590 : bv 32 := 0x02013403.
Lemma F_96590 : fetch_word USEGS (0x96590 : word) = Some W_96590.
Proof. vm_refl. Qed.
Lemma D_96590 : decode_any W_96590 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96594 : bv 32 := 0x01813483.
Lemma F_96594 : fetch_word USEGS (0x96594 : word) = Some W_96594.
Proof. vm_refl. Qed.
Lemma D_96594 : decode_any W_96594 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96598 : bv 32 := 0x01013903.
Lemma F_96598 : fetch_word USEGS (0x96598 : word) = Some W_96598.
Proof. vm_refl. Qed.
Lemma D_96598 : decode_any W_96598 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9659c : bv 32 := 0x00813983.
Lemma F_9659c : fetch_word USEGS (0x9659c : word) = Some W_9659c.
Proof. vm_refl. Qed.
Lemma D_9659c : decode_any W_9659c = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_965a0 : bv 32 := 0x03010113.
Lemma F_965a0 : fetch_word USEGS (0x965a0 : word) = Some W_965a0.
Proof. vm_refl. Qed.
Lemma D_965a0 : decode_any W_965a0 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_965a4 : bv 32 := 0x6fc1106f.
Lemma F_965a4 : fetch_word USEGS (0x965a4 : word) = Some W_965a4.
Proof. vm_refl. Qed.
Lemma D_965a4 : decode_any W_965a4 = Some (Jal 0 71420, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_965a8 : bv 32 := 0x00008067.
Lemma F_965a8 : fetch_word USEGS (0x965a8 : word) = Some W_965a8.
Proof. vm_refl. Qed.
Lemma D_965a8 : decode_any W_965a8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9673c : bv 32 := 0x00008067.
Lemma F_9673c : fetch_word USEGS (0x9673c : word) = Some W_9673c.
Proof. vm_refl. Qed.
Lemma D_9673c : decode_any W_9673c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96740 : bv 32 := 0xfe010113.
Lemma F_96740 : fetch_word USEGS (0x96740 : word) = Some W_96740.
Proof. vm_refl. Qed.
Lemma D_96740 : decode_any W_96740 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96744 : bv 32 := 0x00113c23.
Lemma F_96744 : fetch_word USEGS (0x96744 : word) = Some W_96744.
Proof. vm_refl. Qed.
Lemma D_96744 : decode_any W_96744 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96748 : bv 32 := 0x00813823.
Lemma F_96748 : fetch_word USEGS (0x96748 : word) = Some W_96748.
Proof. vm_refl. Qed.
Lemma D_96748 : decode_any W_96748 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9674c : bv 32 := 0x00913423.
Lemma F_9674c : fetch_word USEGS (0x9674c : word) = Some W_9674c.
Proof. vm_refl. Qed.
Lemma D_9674c : decode_any W_9674c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96750 : bv 32 := 0x0001c517.
Lemma F_96750 : fetch_word USEGS (0x96750 : word) = Some W_96750.
Proof. vm_refl. Qed.
Lemma D_96750 : decode_any W_96750 = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96754 : bv 32 := 0x0001c597.
Lemma F_96754 : fetch_word USEGS (0x96754 : word) = Some W_96754.
Proof. vm_refl. Qed.
Lemma D_96754 : decode_any W_96754 = Some (Auipc 11 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96758 : bv 32 := 0xb6053503.
Lemma F_96758 : fetch_word USEGS (0x96758 : word) = Some W_96758.
Proof. vm_refl. Qed.
Lemma D_96758 : decode_any W_96758 = Some (Load SZ8 true 10 10 2912, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9675c : bv 32 := 0xb645b403.
Lemma F_9675c : fetch_word USEGS (0x9675c : word) = Some W_9675c.
Proof. vm_refl. Qed.
Lemma D_9675c : decode_any W_9675c = Some (Load SZ8 true 8 11 2916, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96760 : bv 32 := 0x00a47c63.
Lemma F_96760 : fetch_word USEGS (0x96760 : word) = Some W_96760.
Proof. vm_refl. Qed.
Lemma D_96760 : decode_any W_96760 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96764 : bv 32 := 0xff853583.
Lemma F_96764 : fetch_word USEGS (0x96764 : word) = Some W_96764.
Proof. vm_refl. Qed.
Lemma D_96764 : decode_any W_96764 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96768 : bv 32 := 0xff850493.
Lemma F_96768 : fetch_word USEGS (0x96768 : word) = Some W_96768.
Proof. vm_refl. Qed.
Lemma D_96768 : decode_any W_96768 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9676c : bv 32 := 0x000580e7.
Lemma F_9676c : fetch_word USEGS (0x9676c : word) = Some W_9676c.
Proof. vm_refl. Qed.
Lemma D_9676c : decode_any W_9676c = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96770 : bv 32 := 0x00048513.
Lemma F_96770 : fetch_word USEGS (0x96770 : word) = Some W_96770.
Proof. vm_refl. Qed.
Lemma D_96770 : decode_any W_96770 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96774 : bv 32 := 0xfe9468e3.
Lemma F_96774 : fetch_word USEGS (0x96774 : word) = Some W_96774.
Proof. vm_refl. Qed.
Lemma D_96774 : decode_any W_96774 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96778 : bv 32 := 0x01813083.
Lemma F_96778 : fetch_word USEGS (0x96778 : word) = Some W_96778.
Proof. vm_refl. Qed.
Lemma D_96778 : decode_any W_96778 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9677c : bv 32 := 0x01013403.
Lemma F_9677c : fetch_word USEGS (0x9677c : word) = Some W_9677c.
Proof. vm_refl. Qed.
Lemma D_9677c : decode_any W_9677c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96780 : bv 32 := 0x00813483.
Lemma F_96780 : fetch_word USEGS (0x96780 : word) = Some W_96780.
Proof. vm_refl. Qed.
Lemma D_96780 : decode_any W_96780 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96784 : bv 32 := 0x02010113.
Lemma F_96784 : fetch_word USEGS (0x96784 : word) = Some W_96784.
Proof. vm_refl. Qed.
Lemma D_96784 : decode_any W_96784 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96788 : bv 32 := 0xfb5ff06f.
Lemma F_96788 : fetch_word USEGS (0x96788 : word) = Some W_96788.
Proof. vm_refl. Qed.
Lemma D_96788 : decode_any W_96788 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9678c : bv 32 := 0xff010113.
Lemma F_9678c : fetch_word USEGS (0x9678c : word) = Some W_9678c.
Proof. vm_refl. Qed.
Lemma D_9678c : decode_any W_9678c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96790 : bv 32 := 0x00113423.
Lemma F_96790 : fetch_word USEGS (0x96790 : word) = Some W_96790.
Proof. vm_refl. Qed.
Lemma D_96790 : decode_any W_96790 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96794 : bv 32 := 0x00813023.
Lemma F_96794 : fetch_word USEGS (0x96794 : word) = Some W_96794.
Proof. vm_refl. Qed.
Lemma D_96794 : decode_any W_96794 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96798 : bv 32 := 0x00000593.
Lemma F_96798 : fetch_word USEGS (0x96798 : word) = Some W_96798.
Proof. vm_refl. Qed.
Lemma D_96798 : decode_any W_96798 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9679c : bv 32 := 0x00020613.
Lemma F_9679c : fetch_word USEGS (0x9679c : word) = Some W_9679c.
Proof. vm_refl. Qed.
Lemma D_9679c : decode_any W_9679c = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967a0 : bv 32 := 0xf5862603.
Lemma F_967a0 : fetch_word USEGS (0x967a0 : word) = Some W_967a0.
Proof. vm_refl. Qed.
Lemma D_967a0 : decode_any W_967a0 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967a4 : bv 32 := 0x0004f697.
Lemma F_967a4 : fetch_word USEGS (0x967a4 : word) = Some W_967a4.
Proof. vm_refl. Qed.
Lemma D_967a4 : decode_any W_967a4 = Some (Auipc 13 79, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967a8 : bv 32 := 0xadc68693.
Lemma F_967a8 : fetch_word USEGS (0x967a8 : word) = Some W_967a8.
Proof. vm_refl. Qed.
Lemma D_967a8 : decode_any W_967a8 = Some (OpImm ALU_ADD 13 13 2780, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967ac : bv 32 := 0x1606a72f.
Lemma F_967ac : fetch_word USEGS (0x967ac : word) = Some W_967ac.
Proof. vm_refl. Qed.
Lemma D_967ac : decode_any W_967ac = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967b0 : bv 32 := 0x00b71663.
Lemma F_967b0 : fetch_word USEGS (0x967b0 : word) = Some W_967b0.
Proof. vm_refl. Qed.
Lemma D_967b0 : decode_any W_967b0 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967b4 : bv 32 := 0x1ec6a7af.
Lemma F_967b4 : fetch_word USEGS (0x967b4 : word) = Some W_967b4.
Proof. vm_refl. Qed.
Lemma D_967b4 : decode_any W_967b4 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967b8 : bv 32 := 0xfe079ae3.
Lemma F_967b8 : fetch_word USEGS (0x967b8 : word) = Some W_967b8.
Proof. vm_refl. Qed.
Lemma D_967b8 : decode_any W_967b8 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967bc : bv 32 := 0x0007059b.
Lemma F_967bc : fetch_word USEGS (0x967bc : word) = Some W_967bc.
Proof. vm_refl. Qed.
Lemma D_967bc : decode_any W_967bc = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967c0 : bv 32 := 0x02c58263.
Lemma F_967c0 : fetch_word USEGS (0x967c0 : word) = Some W_967c0.
Proof. vm_refl. Qed.
Lemma D_967c0 : decode_any W_967c0 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967c4 : bv 32 := 0x02058263.
Lemma F_967c4 : fetch_word USEGS (0x967c4 : word) = Some W_967c4.
Proof. vm_refl. Qed.
Lemma D_967c4 : decode_any W_967c4 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967e8 : bv 32 := 0x00050413.
Lemma F_967e8 : fetch_word USEGS (0x967e8 : word) = Some W_967e8.
Proof. vm_refl. Qed.
Lemma D_967e8 : decode_any W_967e8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967ec : bv 32 := 0xcf5ff0ef.
Lemma F_967ec : fetch_word USEGS (0x967ec : word) = Some W_967ec.
Proof. vm_refl. Qed.
Lemma D_967ec : decode_any W_967ec = Some (Jal 1 2096372, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967f0 : bv 32 := 0xf51ff0ef.
Lemma F_967f0 : fetch_word USEGS (0x967f0 : word) = Some W_967f0.
Proof. vm_refl. Qed.
Lemma D_967f0 : decode_any W_967f0 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967f4 : bv 32 := 0x474050ef.
Lemma F_967f4 : fetch_word USEGS (0x967f4 : word) = Some W_967f4.
Proof. vm_refl. Qed.
Lemma D_967f4 : decode_any W_967f4 = Some (Jal 1 21620, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967f8 : bv 32 := 0x00040513.
Lemma F_967f8 : fetch_word USEGS (0x967f8 : word) = Some W_967f8.
Proof. vm_refl. Qed.
Lemma D_967f8 : decode_any W_967f8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967fc : bv 32 := 0xc99ff0ef.
Lemma F_967fc : fetch_word USEGS (0x967fc : word) = Some W_967fc.
Proof. vm_refl. Qed.
Lemma D_967fc : decode_any W_967fc = Some (Jal 1 2096280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_968e4 : bv 32 := 0xff010113.
Lemma F_968e4 : fetch_word USEGS (0x968e4 : word) = Some W_968e4.
Proof. vm_refl. Qed.
Lemma D_968e4 : decode_any W_968e4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_968e8 : bv 32 := 0x00113423.
Lemma F_968e8 : fetch_word USEGS (0x968e8 : word) = Some W_968e8.
Proof. vm_refl. Qed.
Lemma D_968e8 : decode_any W_968e8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_968ec : bv 32 := 0x00050e63.
Lemma F_968ec : fetch_word USEGS (0x968ec : word) = Some W_968ec.
Proof. vm_refl. Qed.
Lemma D_968ec : decode_any W_968ec = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_968f0 : bv 32 := 0x00050593.
Lemma F_968f0 : fetch_word USEGS (0x968f0 : word) = Some W_968f0.
Proof. vm_refl. Qed.
Lemma D_968f0 : decode_any W_968f0 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_968f4 : bv 32 := 0x0001c517.
Lemma F_968f4 : fetch_word USEGS (0x968f4 : word) = Some W_968f4.
Proof. vm_refl. Qed.
Lemma D_968f4 : decode_any W_968f4 = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_968f8 : bv 32 := 0x9b453503.
Lemma F_968f8 : fetch_word USEGS (0x968f8 : word) = Some W_968f8.
Proof. vm_refl. Qed.
Lemma D_968f8 : decode_any W_968f8 = Some (Load SZ8 true 10 10 2484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_968fc : bv 32 := 0x00800613.
Lemma F_968fc : fetch_word USEGS (0x968fc : word) = Some W_968fc.
Proof. vm_refl. Qed.
Lemma D_968fc : decode_any W_968fc = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96900 : bv 32 := 0x520100ef.
Lemma F_96900 : fetch_word USEGS (0x96900 : word) = Some W_96900.
Proof. vm_refl. Qed.
Lemma D_96900 : decode_any W_96900 = Some (Jal 1 66848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96904 : bv 32 := 0x01c0006f.
Lemma F_96904 : fetch_word USEGS (0x96904 : word) = Some W_96904.
Proof. vm_refl. Qed.
Lemma D_96904 : decode_any W_96904 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96920 : bv 32 := 0x0001c517.
Lemma F_96920 : fetch_word USEGS (0x96920 : word) = Some W_96920.
Proof. vm_refl. Qed.
Lemma D_96920 : decode_any W_96920 = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96924 : bv 32 := 0x98853503.
Lemma F_96924 : fetch_word USEGS (0x96924 : word) = Some W_96924.
Proof. vm_refl. Qed.
Lemma D_96924 : decode_any W_96924 = Some (Load SZ8 true 10 10 2440, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96928 : bv 32 := 0x000500a3.
Lemma F_96928 : fetch_word USEGS (0x96928 : word) = Some W_96928.
Proof. vm_refl. Qed.
Lemma D_96928 : decode_any W_96928 = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9692c : bv 32 := 0x00053503.
Lemma F_9692c : fetch_word USEGS (0x9692c : word) = Some W_9692c.
Proof. vm_refl. Qed.
Lemma D_9692c : decode_any W_9692c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96930 : bv 32 := 0x00020593.
Lemma F_96930 : fetch_word USEGS (0x96930 : word) = Some W_96930.
Proof. vm_refl. Qed.
Lemma D_96930 : decode_any W_96930 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96934 : bv 32 := 0xfea5b823.
Lemma F_96934 : fetch_word USEGS (0x96934 : word) = Some W_96934.
Proof. vm_refl. Qed.
Lemma D_96934 : decode_any W_96934 = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96938 : bv 32 := 0x00813083.
Lemma F_96938 : fetch_word USEGS (0x96938 : word) = Some W_96938.
Proof. vm_refl. Qed.
Lemma D_96938 : decode_any W_96938 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9693c : bv 32 := 0x01010113.
Lemma F_9693c : fetch_word USEGS (0x9693c : word) = Some W_9693c.
Proof. vm_refl. Qed.
Lemma D_9693c : decode_any W_9693c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96940 : bv 32 := 0x00008067.
Lemma F_96940 : fetch_word USEGS (0x96940 : word) = Some W_96940.
Proof. vm_refl. Qed.
Lemma D_96940 : decode_any W_96940 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9694c : bv 32 := 0xfffff5b7.
Lemma F_9694c : fetch_word USEGS (0x9694c : word) = Some W_9694c.
Proof. vm_refl. Qed.
Lemma D_9694c : decode_any W_9694c = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96950 : bv 32 := 0x0015859b.
Lemma F_96950 : fetch_word USEGS (0x96950 : word) = Some W_96950.
Proof. vm_refl. Qed.
Lemma D_96950 : decode_any W_96950 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96954 : bv 32 := 0x02b56663.
Lemma F_96954 : fetch_word USEGS (0x96954 : word) = Some W_96954.
Proof. vm_refl. Qed.
Lemma D_96954 : decode_any W_96954 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96980 : bv 32 := 0x00008067.
Lemma F_96980 : fetch_word USEGS (0x96980 : word) = Some W_96980.
Proof. vm_refl. Qed.
Lemma D_96980 : decode_any W_96980 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

