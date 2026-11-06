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
Definition W_a3000 : bv 32 := 0x0164f5b3.
Lemma F_a3000 : fetch_word AsanUbsan.M.loaded_segments (0xa3048 : word) = Some W_a3000.
Proof. vm_refl. Qed.
Lemma D_a3000 : decode_any W_a3000 = Some (Op ALU_AND 11 9 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3004 : bv 32 := 0x00459593.
Lemma F_a3004 : fetch_word AsanUbsan.M.loaded_segments (0xa304c : word) = Some W_a3004.
Proof. vm_refl. Qed.
Lemma D_a3004 : decode_any W_a3004 = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3008 : bv 32 := 0x00b504b3.
Lemma F_a3008 : fetch_word AsanUbsan.M.loaded_segments (0xa3050 : word) = Some W_a3008.
Proof. vm_refl. Qed.
Lemma D_a3008 : decode_any W_a3008 = Some (Op ALU_ADD 9 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a300c : bv 32 := 0x00810613.
Lemma F_a300c : fetch_word AsanUbsan.M.loaded_segments (0xa3054 : word) = Some W_a300c.
Proof. vm_refl. Qed.
Lemma D_a300c : decode_any W_a300c = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3010 : bv 32 := 0x00048513.
Lemma F_a3010 : fetch_word AsanUbsan.M.loaded_segments (0xa3058 : word) = Some W_a3010.
Proof. vm_refl. Qed.
Lemma D_a3010 : decode_any W_a3010 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3014 : bv 32 := 0x00000593.
Lemma F_a3014 : fetch_word AsanUbsan.M.loaded_segments (0xa305c : word) = Some W_a3014.
Proof. vm_refl. Qed.
Lemma D_a3014 : decode_any W_a3014 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3018 : bv 32 := 0x00098693.
Lemma F_a3018 : fetch_word AsanUbsan.M.loaded_segments (0xa3060 : word) = Some W_a3018.
Proof. vm_refl. Qed.
Lemma D_a3018 : decode_any W_a3018 = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a301c : bv 32 := 0xaf5ff0ef.
Lemma F_a301c : fetch_word AsanUbsan.M.loaded_segments (0xa3064 : word) = Some W_a301c.
Proof. vm_refl. Qed.
Lemma D_a301c : decode_any W_a301c = Some (Jal 1 2095860, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3020 : bv 32 := 0x0154a423.
Lemma F_a3020 : fetch_word AsanUbsan.M.loaded_segments (0xa3068 : word) = Some W_a3020.
Proof. vm_refl. Qed.
Lemma D_a3020 : decode_any W_a3020 = Some (Store SZ4 9 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3024 : bv 32 := 0x0310000f.
Lemma F_a3024 : fetch_word AsanUbsan.M.loaded_segments (0xa306c : word) = Some W_a3024.
Proof. vm_refl. Qed.
Lemma D_a3024 : decode_any W_a3024 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3028 : bv 32 := 0x000b8513.
Lemma F_a3028 : fetch_word AsanUbsan.M.loaded_segments (0xa3070 : word) = Some W_a3028.
Proof. vm_refl. Qed.
Lemma D_a3028 : decode_any W_a3028 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a302c : bv 32 := 0x01792023.
Lemma F_a302c : fetch_word AsanUbsan.M.loaded_segments (0xa3074 : word) = Some W_a302c.
Proof. vm_refl. Qed.
Lemma D_a302c : decode_any W_a302c = Some (Store SZ4 18 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3030 : bv 32 := 0x00040663.
Lemma F_a3030 : fetch_word AsanUbsan.M.loaded_segments (0xa3078 : word) = Some W_a3030.
Proof. vm_refl. Qed.
Lemma D_a3030 : decode_any W_a3030 = Some (Branch BC_EQ 8 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a303c : bv 32 := 0x06813083.
Lemma F_a303c : fetch_word AsanUbsan.M.loaded_segments (0xa3084 : word) = Some W_a303c.
Proof. vm_refl. Qed.
Lemma D_a303c : decode_any W_a303c = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3040 : bv 32 := 0x06013403.
Lemma F_a3040 : fetch_word AsanUbsan.M.loaded_segments (0xa3088 : word) = Some W_a3040.
Proof. vm_refl. Qed.
Lemma D_a3040 : decode_any W_a3040 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3044 : bv 32 := 0x05813483.
Lemma F_a3044 : fetch_word AsanUbsan.M.loaded_segments (0xa308c : word) = Some W_a3044.
Proof. vm_refl. Qed.
Lemma D_a3044 : decode_any W_a3044 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3048 : bv 32 := 0x05013903.
Lemma F_a3048 : fetch_word AsanUbsan.M.loaded_segments (0xa3090 : word) = Some W_a3048.
Proof. vm_refl. Qed.
Lemma D_a3048 : decode_any W_a3048 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a304c : bv 32 := 0x04813983.
Lemma F_a304c : fetch_word AsanUbsan.M.loaded_segments (0xa3094 : word) = Some W_a304c.
Proof. vm_refl. Qed.
Lemma D_a304c : decode_any W_a304c = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3050 : bv 32 := 0x04013a03.
Lemma F_a3050 : fetch_word AsanUbsan.M.loaded_segments (0xa3098 : word) = Some W_a3050.
Proof. vm_refl. Qed.
Lemma D_a3050 : decode_any W_a3050 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3054 : bv 32 := 0x03813a83.
Lemma F_a3054 : fetch_word AsanUbsan.M.loaded_segments (0xa309c : word) = Some W_a3054.
Proof. vm_refl. Qed.
Lemma D_a3054 : decode_any W_a3054 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3058 : bv 32 := 0x03013b03.
Lemma F_a3058 : fetch_word AsanUbsan.M.loaded_segments (0xa30a0 : word) = Some W_a3058.
Proof. vm_refl. Qed.
Lemma D_a3058 : decode_any W_a3058 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a305c : bv 32 := 0x02813b83.
Lemma F_a305c : fetch_word AsanUbsan.M.loaded_segments (0xa30a4 : word) = Some W_a305c.
Proof. vm_refl. Qed.
Lemma D_a305c : decode_any W_a305c = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3060 : bv 32 := 0x02013c03.
Lemma F_a3060 : fetch_word AsanUbsan.M.loaded_segments (0xa30a8 : word) = Some W_a3060.
Proof. vm_refl. Qed.
Lemma D_a3060 : decode_any W_a3060 = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3064 : bv 32 := 0x01813c83.
Lemma F_a3064 : fetch_word AsanUbsan.M.loaded_segments (0xa30ac : word) = Some W_a3064.
Proof. vm_refl. Qed.
Lemma D_a3064 : decode_any W_a3064 = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3068 : bv 32 := 0x07010113.
Lemma F_a3068 : fetch_word AsanUbsan.M.loaded_segments (0xa30b0 : word) = Some W_a3068.
Proof. vm_refl. Qed.
Lemma D_a3068 : decode_any W_a3068 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a306c : bv 32 := 0x00008067.
Lemma F_a306c : fetch_word AsanUbsan.M.loaded_segments (0xa30b4 : word) = Some W_a306c.
Proof. vm_refl. Qed.
Lemma D_a306c : decode_any W_a306c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a358c : bv 32 := 0xfd010113.
Lemma F_a358c : fetch_word AsanUbsan.M.loaded_segments (0xa35d4 : word) = Some W_a358c.
Proof. vm_refl. Qed.
Lemma D_a358c : decode_any W_a358c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3590 : bv 32 := 0x02113423.
Lemma F_a3590 : fetch_word AsanUbsan.M.loaded_segments (0xa35d8 : word) = Some W_a3590.
Proof. vm_refl. Qed.
Lemma D_a3590 : decode_any W_a3590 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3594 : bv 32 := 0x02813023.
Lemma F_a3594 : fetch_word AsanUbsan.M.loaded_segments (0xa35dc : word) = Some W_a3594.
Proof. vm_refl. Qed.
Lemma D_a3594 : decode_any W_a3594 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3598 : bv 32 := 0x00913c23.
Lemma F_a3598 : fetch_word AsanUbsan.M.loaded_segments (0xa35e0 : word) = Some W_a3598.
Proof. vm_refl. Qed.
Lemma D_a3598 : decode_any W_a3598 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a359c : bv 32 := 0x01213823.
Lemma F_a359c : fetch_word AsanUbsan.M.loaded_segments (0xa35e4 : word) = Some W_a359c.
Proof. vm_refl. Qed.
Lemma D_a359c : decode_any W_a359c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35a0 : bv 32 := 0x01313423.
Lemma F_a35a0 : fetch_word AsanUbsan.M.loaded_segments (0xa35e8 : word) = Some W_a35a0.
Proof. vm_refl. Qed.
Lemma D_a35a0 : decode_any W_a35a0 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35a4 : bv 32 := 0x00050413.
Lemma F_a35a4 : fetch_word AsanUbsan.M.loaded_segments (0xa35ec : word) = Some W_a35a4.
Proof. vm_refl. Qed.
Lemma D_a35a4 : decode_any W_a35a4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35a8 : bv 32 := 0x00000593.
Lemma F_a35a8 : fetch_word AsanUbsan.M.loaded_segments (0xa35f0 : word) = Some W_a35a8.
Proof. vm_refl. Qed.
Lemma D_a35a8 : decode_any W_a35a8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35ac : bv 32 := 0x800004b7.
Lemma F_a35ac : fetch_word AsanUbsan.M.loaded_segments (0xa35f4 : word) = Some W_a35ac.
Proof. vm_refl. Qed.
Lemma D_a35ac : decode_any W_a35ac = Some (Lui 9 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35b0 : bv 32 := 0x00900913.
Lemma F_a35b0 : fetch_word AsanUbsan.M.loaded_segments (0xa35f8 : word) = Some W_a35b0.
Proof. vm_refl. Qed.
Lemma D_a35b0 : decode_any W_a35b0 = Some (OpImm ALU_ADD 18 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35b4 : bv 32 := 0x00052503.
Lemma F_a35b4 : fetch_word AsanUbsan.M.loaded_segments (0xa35fc : word) = Some W_a35b4.
Proof. vm_refl. Qed.
Lemma D_a35b4 : decode_any W_a35b4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35b8 : bv 32 := 0x00055a63.
Lemma F_a35b8 : fetch_word AsanUbsan.M.loaded_segments (0xa3600 : word) = Some W_a35b8.
Proof. vm_refl. Qed.
Lemma D_a35b8 : decode_any W_a35b8 = Some (Branch BC_GE 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35cc : bv 32 := 0x00956633.
Lemma F_a35cc : fetch_word AsanUbsan.M.loaded_segments (0xa3614 : word) = Some W_a35cc.
Proof. vm_refl. Qed.
Lemma D_a35cc : decode_any W_a35cc = Some (Op ALU_OR 12 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35d0 : bv 32 := 0x160426af.
Lemma F_a35d0 : fetch_word AsanUbsan.M.loaded_segments (0xa3618 : word) = Some W_a35d0.
Proof. vm_refl. Qed.
Lemma D_a35d0 : decode_any W_a35d0 = Some (Lr AW true true 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35d4 : bv 32 := 0x00a69663.
Lemma F_a35d4 : fetch_word AsanUbsan.M.loaded_segments (0xa361c : word) = Some W_a35d4.
Proof. vm_refl. Qed.
Lemma D_a35d4 : decode_any W_a35d4 = Some (Branch BC_NE 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35d8 : bv 32 := 0x1ac4272f.
Lemma F_a35d8 : fetch_word AsanUbsan.M.loaded_segments (0xa3620 : word) = Some W_a35d8.
Proof. vm_refl. Qed.
Lemma D_a35d8 : decode_any W_a35d8 = Some (Sc AW false true 14 8 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35dc : bv 32 := 0xfe071ae3.
Lemma F_a35dc : fetch_word AsanUbsan.M.loaded_segments (0xa3624 : word) = Some W_a35dc.
Proof. vm_refl. Qed.
Lemma D_a35dc : decode_any W_a35dc = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35e0 : bv 32 := 0x02a68063.
Lemma F_a35e0 : fetch_word AsanUbsan.M.loaded_segments (0xa3628 : word) = Some W_a35e0.
Proof. vm_refl. Qed.
Lemma D_a35e0 : decode_any W_a35e0 = Some (Branch BC_EQ 13 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3600 : bv 32 := 0x02813083.
Lemma F_a3600 : fetch_word AsanUbsan.M.loaded_segments (0xa3648 : word) = Some W_a3600.
Proof. vm_refl. Qed.
Lemma D_a3600 : decode_any W_a3600 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3604 : bv 32 := 0x02013403.
Lemma F_a3604 : fetch_word AsanUbsan.M.loaded_segments (0xa364c : word) = Some W_a3604.
Proof. vm_refl. Qed.
Lemma D_a3604 : decode_any W_a3604 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3608 : bv 32 := 0x01813483.
Lemma F_a3608 : fetch_word AsanUbsan.M.loaded_segments (0xa3650 : word) = Some W_a3608.
Proof. vm_refl. Qed.
Lemma D_a3608 : decode_any W_a3608 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a360c : bv 32 := 0x01013903.
Lemma F_a360c : fetch_word AsanUbsan.M.loaded_segments (0xa3654 : word) = Some W_a360c.
Proof. vm_refl. Qed.
Lemma D_a360c : decode_any W_a360c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3610 : bv 32 := 0x00813983.
Lemma F_a3610 : fetch_word AsanUbsan.M.loaded_segments (0xa3658 : word) = Some W_a3610.
Proof. vm_refl. Qed.
Lemma D_a3610 : decode_any W_a3610 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3614 : bv 32 := 0x03010113.
Lemma F_a3614 : fetch_word AsanUbsan.M.loaded_segments (0xa365c : word) = Some W_a3614.
Proof. vm_refl. Qed.
Lemma D_a3614 : decode_any W_a3614 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3618 : bv 32 := 0x00008067.
Lemma F_a3618 : fetch_word AsanUbsan.M.loaded_segments (0xa3660 : word) = Some W_a3618.
Proof. vm_refl. Qed.
Lemma D_a3618 : decode_any W_a3618 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a377c : bv 32 := 0x00008513.
Lemma F_a377c : fetch_word AsanUbsan.M.loaded_segments (0xa37c4 : word) = Some W_a377c.
Proof. vm_refl. Qed.
Lemma D_a377c : decode_any W_a377c = Some (OpImm ALU_ADD 10 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3780 : bv 32 := 0x00008067.
Lemma F_a3780 : fetch_word AsanUbsan.M.loaded_segments (0xa37c8 : word) = Some W_a3780.
Proof. vm_refl. Qed.
Lemma D_a3780 : decode_any W_a3780 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3784 : bv 32 := 0xfc010113.
Lemma F_a3784 : fetch_word AsanUbsan.M.loaded_segments (0xa37cc : word) = Some W_a3784.
Proof. vm_refl. Qed.
Lemma D_a3784 : decode_any W_a3784 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3788 : bv 32 := 0x02113c23.
Lemma F_a3788 : fetch_word AsanUbsan.M.loaded_segments (0xa37d0 : word) = Some W_a3788.
Proof. vm_refl. Qed.
Lemma D_a3788 : decode_any W_a3788 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a378c : bv 32 := 0x02813823.
Lemma F_a378c : fetch_word AsanUbsan.M.loaded_segments (0xa37d4 : word) = Some W_a378c.
Proof. vm_refl. Qed.
Lemma D_a378c : decode_any W_a378c = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3790 : bv 32 := 0x02913423.
Lemma F_a3790 : fetch_word AsanUbsan.M.loaded_segments (0xa37d8 : word) = Some W_a3790.
Proof. vm_refl. Qed.
Lemma D_a3790 : decode_any W_a3790 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3794 : bv 32 := 0x03213023.
Lemma F_a3794 : fetch_word AsanUbsan.M.loaded_segments (0xa37dc : word) = Some W_a3794.
Proof. vm_refl. Qed.
Lemma D_a3794 : decode_any W_a3794 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3798 : bv 32 := 0x01313c23.
Lemma F_a3798 : fetch_word AsanUbsan.M.loaded_segments (0xa37e0 : word) = Some W_a3798.
Proof. vm_refl. Qed.
Lemma D_a3798 : decode_any W_a3798 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a379c : bv 32 := 0x01413823.
Lemma F_a379c : fetch_word AsanUbsan.M.loaded_segments (0xa37e4 : word) = Some W_a379c.
Proof. vm_refl. Qed.
Lemma D_a379c : decode_any W_a379c = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37a0 : bv 32 := 0x01513423.
Lemma F_a37a0 : fetch_word AsanUbsan.M.loaded_segments (0xa37e8 : word) = Some W_a37a0.
Proof. vm_refl. Qed.
Lemma D_a37a0 : decode_any W_a37a0 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37a4 : bv 32 := 0x01613023.
Lemma F_a37a4 : fetch_word AsanUbsan.M.loaded_segments (0xa37ec : word) = Some W_a37a4.
Proof. vm_refl. Qed.
Lemma D_a37a4 : decode_any W_a37a4 = Some (Store SZ8 2 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37a8 : bv 32 := 0x00068493.
Lemma F_a37a8 : fetch_word AsanUbsan.M.loaded_segments (0xa37f0 : word) = Some W_a37a8.
Proof. vm_refl. Qed.
Lemma D_a37a8 : decode_any W_a37a8 = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37ac : bv 32 := 0x02079413.
Lemma F_a37ac : fetch_word AsanUbsan.M.loaded_segments (0xa37f4 : word) = Some W_a37ac.
Proof. vm_refl. Qed.
Lemma D_a37ac : decode_any W_a37ac = Some (ShiftImm ALU_SLL 8 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37b0 : bv 32 := 0x00100693.
Lemma F_a37b0 : fetch_word AsanUbsan.M.loaded_segments (0xa37f8 : word) = Some W_a37b0.
Proof. vm_refl. Qed.
Lemma D_a37b0 : decode_any W_a37b0 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37b4 : bv 32 := 0x02045413.
Lemma F_a37b4 : fetch_word AsanUbsan.M.loaded_segments (0xa37fc : word) = Some W_a37b4.
Proof. vm_refl. Qed.
Lemma D_a37b4 : decode_any W_a37b4 = Some (ShiftImm ALU_SRL 8 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37b8 : bv 32 := 0x0ef6f863.
Lemma F_a37b8 : fetch_word AsanUbsan.M.loaded_segments (0xa3800 : word) = Some W_a37b8.
Proof. vm_refl. Qed.
Lemma D_a37b8 : decode_any W_a37b8 = Some (Branch BC_GEU 13 15 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37bc : bv 32 := 0x000c1697.
Lemma F_a37bc : fetch_word AsanUbsan.M.loaded_segments (0xa3804 : word) = Some W_a37bc.
Proof. vm_refl. Qed.
Lemma D_a37bc : decode_any W_a37bc = Some (Auipc 13 193, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37c0 : bv 32 := 0xcf46b903.
Lemma F_a37c0 : fetch_word AsanUbsan.M.loaded_segments (0xa3808 : word) = Some W_a37c0.
Proof. vm_refl. Qed.
Lemma D_a37c0 : decode_any W_a37c0 = Some (Load SZ8 true 18 13 3316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37c4 : bv 32 := 0x00093683.
Lemma F_a37c4 : fetch_word AsanUbsan.M.loaded_segments (0xa380c : word) = Some W_a37c4.
Proof. vm_refl. Qed.
Lemma D_a37c4 : decode_any W_a37c4 = Some (Load SZ8 true 13 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37c8 : bv 32 := 0x00068e63.
Lemma F_a37c8 : fetch_word AsanUbsan.M.loaded_segments (0xa3810 : word) = Some W_a37c8.
Proof. vm_refl. Qed.
Lemma D_a37c8 : decode_any W_a37c8 = Some (Branch BC_EQ 13 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37cc : bv 32 := 0x00100793.
Lemma F_a37cc : fetch_word AsanUbsan.M.loaded_segments (0xa3814 : word) = Some W_a37cc.
Proof. vm_refl. Qed.
Lemma D_a37cc : decode_any W_a37cc = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37d0 : bv 32 := 0x00c4d813.
Lemma F_a37d0 : fetch_word AsanUbsan.M.loaded_segments (0xa3818 : word) = Some W_a37d0.
Proof. vm_refl. Qed.
Lemma D_a37d0 : decode_any W_a37d0 = Some (ShiftImm ALU_SRL 16 9 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37d4 : bv 32 := 0x00f52423.
Lemma F_a37d4 : fetch_word AsanUbsan.M.loaded_segments (0xa381c : word) = Some W_a37d4.
Proof. vm_refl. Qed.
Lemma D_a37d4 : decode_any W_a37d4 = Some (Store SZ4 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37d8 : bv 32 := 0x00b53823.
Lemma F_a37d8 : fetch_word AsanUbsan.M.loaded_segments (0xa3820 : word) = Some W_a37d8.
Proof. vm_refl. Qed.
Lemma D_a37d8 : decode_any W_a37d8 = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37dc : bv 32 := 0x04081463.
Lemma F_a37dc : fetch_word AsanUbsan.M.loaded_segments (0xa3824 : word) = Some W_a37dc.
Proof. vm_refl. Qed.
Lemma D_a37dc : decode_any W_a37dc = Some (Branch BC_NE 16 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3824 : bv 32 := 0x0a977263.
Lemma F_a3824 : fetch_word AsanUbsan.M.loaded_segments (0xa386c : word) = Some W_a3824.
Proof. vm_refl. Qed.
Lemma D_a3824 : decode_any W_a3824 = Some (Branch BC_GEU 14 9 164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3828 : bv 32 := 0x04c77c63.
Lemma F_a3828 : fetch_word AsanUbsan.M.loaded_segments (0xa3870 : word) = Some W_a3828.
Proof. vm_refl. Qed.
Lemma D_a3828 : decode_any W_a3828 = Some (Branch BC_GEU 14 12 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a382c : bv 32 := 0xff048493.
Lemma F_a382c : fetch_word AsanUbsan.M.loaded_segments (0xa3874 : word) = Some W_a382c.
Proof. vm_refl. Qed.
Lemma D_a382c : decode_any W_a382c = Some (OpImm ALU_ADD 9 9 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3830 : bv 32 := 0x04967863.
Lemma F_a3830 : fetch_word AsanUbsan.M.loaded_segments (0xa3878 : word) = Some W_a3830.
Proof. vm_refl. Qed.
Lemma D_a3830 : decode_any W_a3830 = Some (Branch BC_GEU 12 9 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3834 : bv 32 := 0x00767713.
Lemma F_a3834 : fetch_word AsanUbsan.M.loaded_segments (0xa387c : word) = Some W_a3834.
Proof. vm_refl. Qed.
Lemma D_a3834 : decode_any W_a3834 = Some (OpImm ALU_AND 14 12 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3838 : bv 32 := 0x04071463.
Lemma F_a3838 : fetch_word AsanUbsan.M.loaded_segments (0xa3880 : word) = Some W_a3838.
Proof. vm_refl. Qed.
Lemma D_a3838 : decode_any W_a3838 = Some (Branch BC_NE 14 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a383c : bv 32 := 0x01050713.
Lemma F_a383c : fetch_word AsanUbsan.M.loaded_segments (0xa3884 : word) = Some W_a383c.
Proof. vm_refl. Qed.
Lemma D_a383c : decode_any W_a383c = Some (OpImm ALU_ADD 14 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3840 : bv 32 := 0x00100793.
Lemma F_a3840 : fetch_word AsanUbsan.M.loaded_segments (0xa3888 : word) = Some W_a3840.
Proof. vm_refl. Qed.
Lemma D_a3840 : decode_any W_a3840 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3844 : bv 32 := 0x0287fe63.
Lemma F_a3844 : fetch_word AsanUbsan.M.loaded_segments (0xa388c : word) = Some W_a3844.
Proof. vm_refl. Qed.
Lemma D_a3844 : decode_any W_a3844 = Some (Branch BC_GEU 15 8 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3848 : bv 32 := 0xff863803.
Lemma F_a3848 : fetch_word AsanUbsan.M.loaded_segments (0xa3890 : word) = Some W_a3848.
Proof. vm_refl. Qed.
Lemma D_a3848 : decode_any W_a3848 = Some (Load SZ8 true 16 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a384c : bv 32 := 0x02d86a63.
Lemma F_a384c : fetch_word AsanUbsan.M.loaded_segments (0xa3894 : word) = Some W_a384c.
Proof. vm_refl. Qed.
Lemma D_a384c : decode_any W_a384c = Some (Branch BC_LTU 16 13 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3850 : bv 32 := 0x00b80c63.
Lemma F_a3850 : fetch_word AsanUbsan.M.loaded_segments (0xa3898 : word) = Some W_a3850.
Proof. vm_refl. Qed.
Lemma D_a3850 : decode_any W_a3850 = Some (Branch BC_EQ 16 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3854 : bv 32 := 0x00379893.
Lemma F_a3854 : fetch_word AsanUbsan.M.loaded_segments (0xa389c : word) = Some W_a3854.
Proof. vm_refl. Qed.
Lemma D_a3854 : decode_any W_a3854 = Some (ShiftImm ALU_SLL 17 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3858 : bv 32 := 0x00178793.
Lemma F_a3858 : fetch_word AsanUbsan.M.loaded_segments (0xa38a0 : word) = Some W_a3858.
Proof. vm_refl. Qed.
Lemma D_a3858 : decode_any W_a3858 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a385c : bv 32 := 0x011708b3.
Lemma F_a385c : fetch_word AsanUbsan.M.loaded_segments (0xa38a4 : word) = Some W_a385c.
Proof. vm_refl. Qed.
Lemma D_a385c : decode_any W_a385c = Some (Op ALU_ADD 17 14 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3860 : bv 32 := 0x00f52423.
Lemma F_a3860 : fetch_word AsanUbsan.M.loaded_segments (0xa38a8 : word) = Some W_a3860.
Proof. vm_refl. Qed.
Lemma D_a3860 : decode_any W_a3860 = Some (Store SZ4 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3864 : bv 32 := 0x0108b023.
Lemma F_a3864 : fetch_word AsanUbsan.M.loaded_segments (0xa38ac : word) = Some W_a3864.
Proof. vm_refl. Qed.
Lemma D_a3864 : decode_any W_a3864 = Some (Store SZ8 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3868 : bv 32 := 0xff063803.
Lemma F_a3868 : fetch_word AsanUbsan.M.loaded_segments (0xa38b0 : word) = Some W_a3868.
Proof. vm_refl. Qed.
Lemma D_a3868 : decode_any W_a3868 = Some (Load SZ8 true 16 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a386c : bv 32 := 0x01067a63.
Lemma F_a386c : fetch_word AsanUbsan.M.loaded_segments (0xa38b4 : word) = Some W_a386c.
Proof. vm_refl. Qed.
Lemma D_a386c : decode_any W_a386c = Some (Branch BC_GEU 12 16 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3870 : bv 32 := 0x00987863.
Lemma F_a3870 : fetch_word AsanUbsan.M.loaded_segments (0xa38b8 : word) = Some W_a3870.
Proof. vm_refl. Qed.
Lemma D_a3870 : decode_any W_a3870 = Some (Branch BC_GEU 16 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3874 : bv 32 := 0x00787893.
Lemma F_a3874 : fetch_word AsanUbsan.M.loaded_segments (0xa38bc : word) = Some W_a3874.
Proof. vm_refl. Qed.
Lemma D_a3874 : decode_any W_a3874 = Some (OpImm ALU_AND 17 16 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3878 : bv 32 := 0x00080613.
Lemma F_a3878 : fetch_word AsanUbsan.M.loaded_segments (0xa38c0 : word) = Some W_a3878.
Proof. vm_refl. Qed.
Lemma D_a3878 : decode_any W_a3878 = Some (OpImm ALU_ADD 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a387c : bv 32 := 0xfc0884e3.
Lemma F_a387c : fetch_word AsanUbsan.M.loaded_segments (0xa38c4 : word) = Some W_a387c.
Proof. vm_refl. Qed.
Lemma D_a387c : decode_any W_a387c = Some (Branch BC_EQ 17 0 8136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3880 : bv 32 := 0x03813083.
Lemma F_a3880 : fetch_word AsanUbsan.M.loaded_segments (0xa38c8 : word) = Some W_a3880.
Proof. vm_refl. Qed.
Lemma D_a3880 : decode_any W_a3880 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3884 : bv 32 := 0x03013403.
Lemma F_a3884 : fetch_word AsanUbsan.M.loaded_segments (0xa38cc : word) = Some W_a3884.
Proof. vm_refl. Qed.
Lemma D_a3884 : decode_any W_a3884 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3888 : bv 32 := 0x02813483.
Lemma F_a3888 : fetch_word AsanUbsan.M.loaded_segments (0xa38d0 : word) = Some W_a3888.
Proof. vm_refl. Qed.
Lemma D_a3888 : decode_any W_a3888 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a388c : bv 32 := 0x02013903.
Lemma F_a388c : fetch_word AsanUbsan.M.loaded_segments (0xa38d4 : word) = Some W_a388c.
Proof. vm_refl. Qed.
Lemma D_a388c : decode_any W_a388c = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3890 : bv 32 := 0x01813983.
Lemma F_a3890 : fetch_word AsanUbsan.M.loaded_segments (0xa38d8 : word) = Some W_a3890.
Proof. vm_refl. Qed.
Lemma D_a3890 : decode_any W_a3890 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3894 : bv 32 := 0x01013a03.
Lemma F_a3894 : fetch_word AsanUbsan.M.loaded_segments (0xa38dc : word) = Some W_a3894.
Proof. vm_refl. Qed.
Lemma D_a3894 : decode_any W_a3894 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3898 : bv 32 := 0x00813a83.
Lemma F_a3898 : fetch_word AsanUbsan.M.loaded_segments (0xa38e0 : word) = Some W_a3898.
Proof. vm_refl. Qed.
Lemma D_a3898 : decode_any W_a3898 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a389c : bv 32 := 0x00013b03.
Lemma F_a389c : fetch_word AsanUbsan.M.loaded_segments (0xa38e4 : word) = Some W_a389c.
Proof. vm_refl. Qed.
Lemma D_a389c : decode_any W_a389c = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a38a0 : bv 32 := 0x04010113.
Lemma F_a38a0 : fetch_word AsanUbsan.M.loaded_segments (0xa38e8 : word) = Some W_a38a0.
Proof. vm_refl. Qed.
Lemma D_a38a0 : decode_any W_a38a0 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a38a4 : bv 32 := 0x00008067.
Lemma F_a38a4 : fetch_word AsanUbsan.M.loaded_segments (0xa38ec : word) = Some W_a38a4.
Proof. vm_refl. Qed.
Lemma D_a38a4 : decode_any W_a38a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3de0 : bv 32 := 0xfc010113.
Lemma F_a3de0 : fetch_word AsanUbsan.M.loaded_segments (0xa3e28 : word) = Some W_a3de0.
Proof. vm_refl. Qed.
Lemma D_a3de0 : decode_any W_a3de0 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3de4 : bv 32 := 0x02113c23.
Lemma F_a3de4 : fetch_word AsanUbsan.M.loaded_segments (0xa3e2c : word) = Some W_a3de4.
Proof. vm_refl. Qed.
Lemma D_a3de4 : decode_any W_a3de4 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3de8 : bv 32 := 0x02813823.
Lemma F_a3de8 : fetch_word AsanUbsan.M.loaded_segments (0xa3e30 : word) = Some W_a3de8.
Proof. vm_refl. Qed.
Lemma D_a3de8 : decode_any W_a3de8 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3dec : bv 32 := 0x02913423.
Lemma F_a3dec : fetch_word AsanUbsan.M.loaded_segments (0xa3e34 : word) = Some W_a3dec.
Proof. vm_refl. Qed.
Lemma D_a3dec : decode_any W_a3dec = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3df0 : bv 32 := 0x03213023.
Lemma F_a3df0 : fetch_word AsanUbsan.M.loaded_segments (0xa3e38 : word) = Some W_a3df0.
Proof. vm_refl. Qed.
Lemma D_a3df0 : decode_any W_a3df0 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3df4 : bv 32 := 0x01313c23.
Lemma F_a3df4 : fetch_word AsanUbsan.M.loaded_segments (0xa3e3c : word) = Some W_a3df4.
Proof. vm_refl. Qed.
Lemma D_a3df4 : decode_any W_a3df4 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3df8 : bv 32 := 0x01413823.
Lemma F_a3df8 : fetch_word AsanUbsan.M.loaded_segments (0xa3e40 : word) = Some W_a3df8.
Proof. vm_refl. Qed.
Lemma D_a3df8 : decode_any W_a3df8 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3dfc : bv 32 := 0x01513423.
Lemma F_a3dfc : fetch_word AsanUbsan.M.loaded_segments (0xa3e44 : word) = Some W_a3dfc.
Proof. vm_refl. Qed.
Lemma D_a3dfc : decode_any W_a3dfc = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3e00 : bv 32 := 0x00058413.
Lemma F_a3e00 : fetch_word AsanUbsan.M.loaded_segments (0xa3e48 : word) = Some W_a3e00.
Proof. vm_refl. Qed.
Lemma D_a3e00 : decode_any W_a3e00 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3e04 : bv 32 := 0x0015b593.
Lemma F_a3e04 : fetch_word AsanUbsan.M.loaded_segments (0xa3e4c : word) = Some W_a3e04.
Proof. vm_refl. Qed.
Lemma D_a3e04 : decode_any W_a3e04 = Some (OpImm ALU_SLTU 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3e08 : bv 32 := 0x7ff50293.
Lemma F_a3e08 : fetch_word AsanUbsan.M.loaded_segments (0xa3e50 : word) = Some W_a3e08.
Proof. vm_refl. Qed.
Lemma D_a3e08 : decode_any W_a3e08 = Some (OpImm ALU_ADD 5 10 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3e0c : bv 32 := 0xfff58593.
Lemma F_a3e0c : fetch_word AsanUbsan.M.loaded_segments (0xa3e54 : word) = Some W_a3e0c.
Proof. vm_refl. Qed.
Lemma D_a3e0c : decode_any W_a3e0c = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3e10 : bv 32 := 0x00d5f333.
Lemma F_a3e10 : fetch_word AsanUbsan.M.loaded_segments (0xa3e58 : word) = Some W_a3e10.
Proof. vm_refl. Qed.
Lemma D_a3e10 : decode_any W_a3e10 = Some (Op ALU_AND 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3e14 : bv 32 := 0x00100593.
Lemma F_a3e14 : fetch_word AsanUbsan.M.loaded_segments (0xa3e5c : word) = Some W_a3e14.
Proof. vm_refl. Qed.
Lemma D_a3e14 : decode_any W_a3e14 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3e18 : bv 32 := 0x0062b4a3.
Lemma F_a3e18 : fetch_word AsanUbsan.M.loaded_segments (0xa3e60 : word) = Some W_a3e18.
Proof. vm_refl. Qed.
Lemma D_a3e18 : decode_any W_a3e18 = Some (Store SZ8 5 6 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3e1c : bv 32 := 0x00b40863.
Lemma F_a3e1c : fetch_word AsanUbsan.M.loaded_segments (0xa3e64 : word) = Some W_a3e1c.
Proof. vm_refl. Qed.
Lemma D_a3e1c : decode_any W_a3e1c = Some (Branch BC_EQ 8 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3e20 : bv 32 := 0x02041c63.
Lemma F_a3e20 : fetch_word AsanUbsan.M.loaded_segments (0xa3e68 : word) = Some W_a3e20.
Proof. vm_refl. Qed.
Lemma D_a3e20 : decode_any W_a3e20 = Some (Branch BC_NE 8 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3e58 : bv 32 := 0x06089463.
Lemma F_a3e58 : fetch_word AsanUbsan.M.loaded_segments (0xa3ea0 : word) = Some W_a3e58.
Proof. vm_refl. Qed.
Lemma D_a3e58 : decode_any W_a3e58 = Some (Branch BC_NE 17 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3ec0 : bv 32 := 0x00060593.
Lemma F_a3ec0 : fetch_word AsanUbsan.M.loaded_segments (0xa3f08 : word) = Some W_a3ec0.
Proof. vm_refl. Qed.
Lemma D_a3ec0 : decode_any W_a3ec0 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3ec4 : bv 32 := 0x00068613.
Lemma F_a3ec4 : fetch_word AsanUbsan.M.loaded_segments (0xa3f0c : word) = Some W_a3ec4.
Proof. vm_refl. Qed.
Lemma D_a3ec4 : decode_any W_a3ec4 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3ec8 : bv 32 := 0x00078693.
Lemma F_a3ec8 : fetch_word AsanUbsan.M.loaded_segments (0xa3f10 : word) = Some W_a3ec8.
Proof. vm_refl. Qed.
Lemma D_a3ec8 : decode_any W_a3ec8 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3ecc : bv 32 := 0x00080713.
Lemma F_a3ecc : fetch_word AsanUbsan.M.loaded_segments (0xa3f14 : word) = Some W_a3ecc.
Proof. vm_refl. Qed.
Lemma D_a3ecc : decode_any W_a3ecc = Some (OpImm ALU_ADD 14 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3ed0 : bv 32 := 0x00040793.
Lemma F_a3ed0 : fetch_word AsanUbsan.M.loaded_segments (0xa3f18 : word) = Some W_a3ed0.
Proof. vm_refl. Qed.
Lemma D_a3ed0 : decode_any W_a3ed0 = Some (OpImm ALU_ADD 15 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3ed4 : bv 32 := 0x03813083.
Lemma F_a3ed4 : fetch_word AsanUbsan.M.loaded_segments (0xa3f1c : word) = Some W_a3ed4.
Proof. vm_refl. Qed.
Lemma D_a3ed4 : decode_any W_a3ed4 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3ed8 : bv 32 := 0x03013403.
Lemma F_a3ed8 : fetch_word AsanUbsan.M.loaded_segments (0xa3f20 : word) = Some W_a3ed8.
Proof. vm_refl. Qed.
Lemma D_a3ed8 : decode_any W_a3ed8 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3edc : bv 32 := 0x02813483.
Lemma F_a3edc : fetch_word AsanUbsan.M.loaded_segments (0xa3f24 : word) = Some W_a3edc.
Proof. vm_refl. Qed.
Lemma D_a3edc : decode_any W_a3edc = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3ee0 : bv 32 := 0x02013903.
Lemma F_a3ee0 : fetch_word AsanUbsan.M.loaded_segments (0xa3f28 : word) = Some W_a3ee0.
Proof. vm_refl. Qed.
Lemma D_a3ee0 : decode_any W_a3ee0 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3ee4 : bv 32 := 0x01813983.
Lemma F_a3ee4 : fetch_word AsanUbsan.M.loaded_segments (0xa3f2c : word) = Some W_a3ee4.
Proof. vm_refl. Qed.
Lemma D_a3ee4 : decode_any W_a3ee4 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3ee8 : bv 32 := 0x01013a03.
Lemma F_a3ee8 : fetch_word AsanUbsan.M.loaded_segments (0xa3f30 : word) = Some W_a3ee8.
Proof. vm_refl. Qed.
Lemma D_a3ee8 : decode_any W_a3ee8 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3eec : bv 32 := 0x00813a83.
Lemma F_a3eec : fetch_word AsanUbsan.M.loaded_segments (0xa3f34 : word) = Some W_a3eec.
Proof. vm_refl. Qed.
Lemma D_a3eec : decode_any W_a3eec = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3ef0 : bv 32 := 0x04010113.
Lemma F_a3ef0 : fetch_word AsanUbsan.M.loaded_segments (0xa3f38 : word) = Some W_a3ef0.
Proof. vm_refl. Qed.
Lemma D_a3ef0 : decode_any W_a3ef0 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3ef4 : bv 32 := 0x891ff06f.
Lemma F_a3ef4 : fetch_word AsanUbsan.M.loaded_segments (0xa3f3c : word) = Some W_a3ef4.
Proof. vm_refl. Qed.
Lemma D_a3ef4 : decode_any W_a3ef4 = Some (Jal 0 2095248, 4%Z).
Proof. vm_refl. Qed.

