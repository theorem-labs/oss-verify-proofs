(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_75488 : bv 32 := 0xfd010113.
Lemma F_75488 : fetch_word AsanUbsan.M.loaded_segments (0x75488 : word) = Some W_75488.
Proof. vm_refl. Qed.
Lemma D_75488 : decode_any W_75488 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7548c : bv 32 := 0x02113423.
Lemma F_7548c : fetch_word AsanUbsan.M.loaded_segments (0x7548c : word) = Some W_7548c.
Proof. vm_refl. Qed.
Lemma D_7548c : decode_any W_7548c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75490 : bv 32 := 0x02813023.
Lemma F_75490 : fetch_word AsanUbsan.M.loaded_segments (0x75490 : word) = Some W_75490.
Proof. vm_refl. Qed.
Lemma D_75490 : decode_any W_75490 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75494 : bv 32 := 0x00913c23.
Lemma F_75494 : fetch_word AsanUbsan.M.loaded_segments (0x75494 : word) = Some W_75494.
Proof. vm_refl. Qed.
Lemma D_75494 : decode_any W_75494 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75498 : bv 32 := 0x01213823.
Lemma F_75498 : fetch_word AsanUbsan.M.loaded_segments (0x75498 : word) = Some W_75498.
Proof. vm_refl. Qed.
Lemma D_75498 : decode_any W_75498 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7549c : bv 32 := 0x01313423.
Lemma F_7549c : fetch_word AsanUbsan.M.loaded_segments (0x7549c : word) = Some W_7549c.
Proof. vm_refl. Qed.
Lemma D_7549c : decode_any W_7549c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_754a0 : bv 32 := 0x00050413.
Lemma F_754a0 : fetch_word AsanUbsan.M.loaded_segments (0x754a0 : word) = Some W_754a0.
Proof. vm_refl. Qed.
Lemma D_754a0 : decode_any W_754a0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_754a4 : bv 32 := 0x00000593.
Lemma F_754a4 : fetch_word AsanUbsan.M.loaded_segments (0x754a4 : word) = Some W_754a4.
Proof. vm_refl. Qed.
Lemma D_754a4 : decode_any W_754a4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_754a8 : bv 32 := 0x800004b7.
Lemma F_754a8 : fetch_word AsanUbsan.M.loaded_segments (0x754a8 : word) = Some W_754a8.
Proof. vm_refl. Qed.
Lemma D_754a8 : decode_any W_754a8 = Some (Lui 9 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_754ac : bv 32 := 0x00900913.
Lemma F_754ac : fetch_word AsanUbsan.M.loaded_segments (0x754ac : word) = Some W_754ac.
Proof. vm_refl. Qed.
Lemma D_754ac : decode_any W_754ac = Some (OpImm ALU_ADD 18 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_754b0 : bv 32 := 0x00052503.
Lemma F_754b0 : fetch_word AsanUbsan.M.loaded_segments (0x754b0 : word) = Some W_754b0.
Proof. vm_refl. Qed.
Lemma D_754b0 : decode_any W_754b0 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_754b4 : bv 32 := 0x00055a63.
Lemma F_754b4 : fetch_word AsanUbsan.M.loaded_segments (0x754b4 : word) = Some W_754b4.
Proof. vm_refl. Qed.
Lemma D_754b4 : decode_any W_754b4 = Some (Branch BC_GE 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_754b8 : bv 32 := 0x0280006f.
Lemma F_754b8 : fetch_word AsanUbsan.M.loaded_segments (0x754b8 : word) = Some W_754b8.
Proof. vm_refl. Qed.
Lemma D_754b8 : decode_any W_754b8 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_754bc : bv 32 := 0x00098593.
Lemma F_754bc : fetch_word AsanUbsan.M.loaded_segments (0x754bc : word) = Some W_754bc.
Proof. vm_refl. Qed.
Lemma D_754bc : decode_any W_754bc = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_754c0 : bv 32 := 0x00042503.
Lemma F_754c0 : fetch_word AsanUbsan.M.loaded_segments (0x754c0 : word) = Some W_754c0.
Proof. vm_refl. Qed.
Lemma D_754c0 : decode_any W_754c0 = Some (Load SZ4 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_754c4 : bv 32 := 0x00054e63.
Lemma F_754c4 : fetch_word AsanUbsan.M.loaded_segments (0x754c4 : word) = Some W_754c4.
Proof. vm_refl. Qed.
Lemma D_754c4 : decode_any W_754c4 = Some (Branch BC_LT 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_754c8 : bv 32 := 0x00956633.
Lemma F_754c8 : fetch_word AsanUbsan.M.loaded_segments (0x754c8 : word) = Some W_754c8.
Proof. vm_refl. Qed.
Lemma D_754c8 : decode_any W_754c8 = Some (Op ALU_OR 12 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_754cc : bv 32 := 0x160426af.
Lemma F_754cc : fetch_word AsanUbsan.M.loaded_segments (0x754cc : word) = Some W_754cc.
Proof. vm_refl. Qed.
Lemma D_754cc : decode_any W_754cc = Some (Lr AW true true 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_754d0 : bv 32 := 0x00a69663.
Lemma F_754d0 : fetch_word AsanUbsan.M.loaded_segments (0x754d0 : word) = Some W_754d0.
Proof. vm_refl. Qed.
Lemma D_754d0 : decode_any W_754d0 = Some (Branch BC_NE 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_754d4 : bv 32 := 0x1ac4272f.
Lemma F_754d4 : fetch_word AsanUbsan.M.loaded_segments (0x754d4 : word) = Some W_754d4.
Proof. vm_refl. Qed.
Lemma D_754d4 : decode_any W_754d4 = Some (Sc AW false true 14 8 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_754d8 : bv 32 := 0xfe071ae3.
Lemma F_754d8 : fetch_word AsanUbsan.M.loaded_segments (0x754d8 : word) = Some W_754d8.
Proof. vm_refl. Qed.
Lemma D_754d8 : decode_any W_754d8 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_754dc : bv 32 := 0x02a68063.
Lemma F_754dc : fetch_word AsanUbsan.M.loaded_segments (0x754dc : word) = Some W_754dc.
Proof. vm_refl. Qed.
Lemma D_754dc : decode_any W_754dc = Some (Branch BC_EQ 13 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_754e0 : bv 32 := 0x0015899b.
Lemma F_754e0 : fetch_word AsanUbsan.M.loaded_segments (0x754e0 : word) = Some W_754e0.
Proof. vm_refl. Qed.
Lemma D_754e0 : decode_any W_754e0 = Some (OpImm32 19 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_754e4 : bv 32 := 0xfcb97ce3.
Lemma F_754e4 : fetch_word AsanUbsan.M.loaded_segments (0x754e4 : word) = Some W_754e4.
Proof. vm_refl. Qed.
Lemma D_754e4 : decode_any W_754e4 = Some (Branch BC_GEU 18 11 8152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_754e8 : bv 32 := 0xe24f10ef.
Lemma F_754e8 : fetch_word AsanUbsan.M.loaded_segments (0x754e8 : word) = Some W_754e8.
Proof. vm_refl. Qed.
Lemma D_754e8 : decode_any W_754e8 = Some (Jal 1 2037284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_754ec : bv 32 := 0x00098593.
Lemma F_754ec : fetch_word AsanUbsan.M.loaded_segments (0x754ec : word) = Some W_754ec.
Proof. vm_refl. Qed.
Lemma D_754ec : decode_any W_754ec = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_754f0 : bv 32 := 0x00042503.
Lemma F_754f0 : fetch_word AsanUbsan.M.loaded_segments (0x754f0 : word) = Some W_754f0.
Proof. vm_refl. Qed.
Lemma D_754f0 : decode_any W_754f0 = Some (Load SZ4 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_754f4 : bv 32 := 0xfc055ae3.
Lemma F_754f4 : fetch_word AsanUbsan.M.loaded_segments (0x754f4 : word) = Some W_754f4.
Proof. vm_refl. Qed.
Lemma D_754f4 : decode_any W_754f4 = Some (Branch BC_GE 10 0 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_754f8 : bv 32 := 0xfe9ff06f.
Lemma F_754f8 : fetch_word AsanUbsan.M.loaded_segments (0x754f8 : word) = Some W_754f8.
Proof. vm_refl. Qed.
Lemma D_754f8 : decode_any W_754f8 = Some (Jal 0 2097128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_754fc : bv 32 := 0x02813083.
Lemma F_754fc : fetch_word AsanUbsan.M.loaded_segments (0x754fc : word) = Some W_754fc.
Proof. vm_refl. Qed.
Lemma D_754fc : decode_any W_754fc = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75500 : bv 32 := 0x02013403.
Lemma F_75500 : fetch_word AsanUbsan.M.loaded_segments (0x75500 : word) = Some W_75500.
Proof. vm_refl. Qed.
Lemma D_75500 : decode_any W_75500 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75504 : bv 32 := 0x01813483.
Lemma F_75504 : fetch_word AsanUbsan.M.loaded_segments (0x75504 : word) = Some W_75504.
Proof. vm_refl. Qed.
Lemma D_75504 : decode_any W_75504 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75508 : bv 32 := 0x01013903.
Lemma F_75508 : fetch_word AsanUbsan.M.loaded_segments (0x75508 : word) = Some W_75508.
Proof. vm_refl. Qed.
Lemma D_75508 : decode_any W_75508 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7550c : bv 32 := 0x00813983.
Lemma F_7550c : fetch_word AsanUbsan.M.loaded_segments (0x7550c : word) = Some W_7550c.
Proof. vm_refl. Qed.
Lemma D_7550c : decode_any W_7550c = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75510 : bv 32 := 0x03010113.
Lemma F_75510 : fetch_word AsanUbsan.M.loaded_segments (0x75510 : word) = Some W_75510.
Proof. vm_refl. Qed.
Lemma D_75510 : decode_any W_75510 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75514 : bv 32 := 0x00008067.
Lemma F_75514 : fetch_word AsanUbsan.M.loaded_segments (0x75514 : word) = Some W_75514.
Proof. vm_refl. Qed.
Lemma D_75514 : decode_any W_75514 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
