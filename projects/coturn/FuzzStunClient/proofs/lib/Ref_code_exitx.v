(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.


(* [comment removed for export] *)
Definition W_13e08 : bv 32 := 0x00023517.
Lemma F_13e08 : fetch_word Plain.M.loaded_segments (0x13e08 : word) = Some W_13e08.
Proof. vm_refl. Qed.
Lemma D_13e08 : decode_any W_13e08 = Some (Auipc 10 35, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e0c : bv 32 := 0x88c54503.
Lemma F_13e0c : fetch_word Plain.M.loaded_segments (0x13e0c : word) = Some W_13e0c.
Proof. vm_refl. Qed.
Lemma D_13e0c : decode_any W_13e0c = Some (Load SZ1 false 10 10 2188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e10 : bv 32 := 0x00051463.
Lemma F_13e10 : fetch_word Plain.M.loaded_segments (0x13e10 : word) = Some W_13e10.
Proof. vm_refl. Qed.
Lemma D_13e10 : decode_any W_13e10 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e14 : bv 32 := 0x00008067.
Lemma F_13e14 : fetch_word Plain.M.loaded_segments (0x13e14 : word) = Some W_13e14.
Proof. vm_refl. Qed.
Lemma D_13e14 : decode_any W_13e14 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b948 : bv 32 := 0x00892583.
Lemma F_1b948 : fetch_word Plain.M.loaded_segments (0x1b948 : word) = Some W_1b948.
Proof. vm_refl. Qed.
Lemma D_1b948 : decode_any W_1b948 = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b94c : bv 32 := 0x0180006f.
Lemma F_1b94c : fetch_word Plain.M.loaded_segments (0x1b94c : word) = Some W_1b94c.
Proof. vm_refl. Qed.
Lemma D_1b94c : decode_any W_1b94c = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b950 : bv 32 := 0x00053503.
Lemma F_1b950 : fetch_word Plain.M.loaded_segments (0x1b950 : word) = Some W_1b950.
Proof. vm_refl. Qed.
Lemma D_1b950 : decode_any W_1b950 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b954 : bv 32 := 0x02000593.
Lemma F_1b954 : fetch_word Plain.M.loaded_segments (0x1b954 : word) = Some W_1b954.
Proof. vm_refl. Qed.
Lemma D_1b954 : decode_any W_1b954 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b958 : bv 32 := 0x00b92423.
Lemma F_1b958 : fetch_word Plain.M.loaded_segments (0x1b958 : word) = Some W_1b958.
Proof. vm_refl. Qed.
Lemma D_1b958 : decode_any W_1b958 = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b95c : bv 32 := 0x00a93823.
Lemma F_1b95c : fetch_word Plain.M.loaded_segments (0x1b95c : word) = Some W_1b95c.
Proof. vm_refl. Qed.
Lemma D_1b95c : decode_any W_1b95c = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b960 : bv 32 := 0x04050a63.
Lemma F_1b960 : fetch_word Plain.M.loaded_segments (0x1b960 : word) = Some W_1b960.
Proof. vm_refl. Qed.
Lemma D_1b960 : decode_any W_1b960 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b964 : bv 32 := 0xfff5861b.
Lemma F_1b964 : fetch_word Plain.M.loaded_segments (0x1b964 : word) = Some W_1b964.
Proof. vm_refl. Qed.
Lemma D_1b964 : decode_any W_1b964 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b968 : bv 32 := 0x00c92423.
Lemma F_1b968 : fetch_word Plain.M.loaded_segments (0x1b968 : word) = Some W_1b968.
Proof. vm_refl. Qed.
Lemma D_1b968 : decode_any W_1b968 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b96c : bv 32 := 0xfeb052e3.
Lemma F_1b96c : fetch_word Plain.M.loaded_segments (0x1b96c : word) = Some W_1b96c.
Proof. vm_refl. Qed.
Lemma D_1b96c : decode_any W_1b96c = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b970 : bv 32 := 0x01093503.
Lemma F_1b970 : fetch_word Plain.M.loaded_segments (0x1b970 : word) = Some W_1b970.
Proof. vm_refl. Qed.
Lemma D_1b970 : decode_any W_1b970 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b974 : bv 32 := 0x00361613.
Lemma F_1b974 : fetch_word Plain.M.loaded_segments (0x1b974 : word) = Some W_1b974.
Proof. vm_refl. Qed.
Lemma D_1b974 : decode_any W_1b974 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b978 : bv 32 := 0x00c50533.
Lemma F_1b978 : fetch_word Plain.M.loaded_segments (0x1b978 : word) = Some W_1b978.
Proof. vm_refl. Qed.
Lemma D_1b978 : decode_any W_1b978 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b97c : bv 32 := 0x00853983.
Lemma F_1b97c : fetch_word Plain.M.loaded_segments (0x1b97c : word) = Some W_1b97c.
Proof. vm_refl. Qed.
Lemma D_1b97c : decode_any W_1b97c = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b980 : bv 32 := 0x10853483.
Lemma F_1b980 : fetch_word Plain.M.loaded_segments (0x1b980 : word) = Some W_1b980.
Proof. vm_refl. Qed.
Lemma D_1b980 : decode_any W_1b980 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b984 : bv 32 := 0x00040513.
Lemma F_1b984 : fetch_word Plain.M.loaded_segments (0x1b984 : word) = Some W_1b984.
Proof. vm_refl. Qed.
Lemma D_1b984 : decode_any W_1b984 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b988 : bv 32 := 0x680080ef.
Lemma F_1b988 : fetch_word Plain.M.loaded_segments (0x1b988 : word) = Some W_1b988.
Proof. vm_refl. Qed.
Lemma D_1b988 : decode_any W_1b988 = Some (Jal 1 34432, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b98c : bv 32 := 0x00048513.
Lemma F_1b98c : fetch_word Plain.M.loaded_segments (0x1b98c : word) = Some W_1b98c.
Proof. vm_refl. Qed.
Lemma D_1b98c : decode_any W_1b98c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b990 : bv 32 := 0x000980e7.
Lemma F_1b990 : fetch_word Plain.M.loaded_segments (0x1b990 : word) = Some W_1b990.
Proof. vm_refl. Qed.
Lemma D_1b990 : decode_any W_1b990 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b994 : bv 32 := 0x00040513.
Lemma F_1b994 : fetch_word Plain.M.loaded_segments (0x1b994 : word) = Some W_1b994.
Proof. vm_refl. Qed.
Lemma D_1b994 : decode_any W_1b994 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b998 : bv 32 := 0x3e8080ef.
Lemma F_1b998 : fetch_word Plain.M.loaded_segments (0x1b998 : word) = Some W_1b998.
Proof. vm_refl. Qed.
Lemma D_1b998 : decode_any W_1b998 = Some (Jal 1 33768, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b99c : bv 32 := 0x00892503.
Lemma F_1b99c : fetch_word Plain.M.loaded_segments (0x1b99c : word) = Some W_1b99c.
Proof. vm_refl. Qed.
Lemma D_1b99c : decode_any W_1b99c = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9a0 : bv 32 := 0xfff5061b.
Lemma F_1b9a0 : fetch_word Plain.M.loaded_segments (0x1b9a0 : word) = Some W_1b9a0.
Proof. vm_refl. Qed.
Lemma D_1b9a0 : decode_any W_1b9a0 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9a4 : bv 32 := 0x00c92423.
Lemma F_1b9a4 : fetch_word Plain.M.loaded_segments (0x1b9a4 : word) = Some W_1b9a4.
Proof. vm_refl. Qed.
Lemma D_1b9a4 : decode_any W_1b9a4 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9a8 : bv 32 := 0xfca044e3.
Lemma F_1b9a8 : fetch_word Plain.M.loaded_segments (0x1b9a8 : word) = Some W_1b9a8.
Proof. vm_refl. Qed.
Lemma D_1b9a8 : decode_any W_1b9a8 = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9ac : bv 32 := 0x01093503.
Lemma F_1b9ac : fetch_word Plain.M.loaded_segments (0x1b9ac : word) = Some W_1b9ac.
Proof. vm_refl. Qed.
Lemma D_1b9ac : decode_any W_1b9ac = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9b0 : bv 32 := 0xfa1ff06f.
Lemma F_1b9b0 : fetch_word Plain.M.loaded_segments (0x1b9b0 : word) = Some W_1b9b0.
Proof. vm_refl. Qed.
Lemma D_1b9b0 : decode_any W_1b9b0 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1baa4 : bv 32 := 0x00050067.
Lemma F_1baa4 : fetch_word Plain.M.loaded_segments (0x1baa4 : word) = Some W_1baa4.
Proof. vm_refl. Qed.
Lemma D_1baa4 : decode_any W_1baa4 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.
