(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_63548 : bv 32 := 0x0007b597.
Lemma F_63548 : fetch_word AsanUbsan.M.loaded_segments (0x63548 : word) = Some W_63548.
Proof. vm_refl. Qed.
Lemma D_63548 : decode_any W_63548 = Some (Auipc 11 123, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6354c : bv 32 := 0xf485b583.
Lemma F_6354c : fetch_word AsanUbsan.M.loaded_segments (0x6354c : word) = Some W_6354c.
Proof. vm_refl. Qed.
Lemma D_6354c : decode_any W_6354c = Some (Load SZ8 true 11 11 3912, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63550 : bv 32 := 0x0005b583.
Lemma F_63550 : fetch_word AsanUbsan.M.loaded_segments (0x63550 : word) = Some W_63550.
Proof. vm_refl. Qed.
Lemma D_63550 : decode_any W_63550 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63554 : bv 32 := 0xfff58613.
Lemma F_63554 : fetch_word AsanUbsan.M.loaded_segments (0x63554 : word) = Some W_63554.
Proof. vm_refl. Qed.
Lemma D_63554 : decode_any W_63554 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63558 : bv 32 := 0x00c5b6b3.
Lemma F_63558 : fetch_word AsanUbsan.M.loaded_segments (0x63558 : word) = Some W_63558.
Proof. vm_refl. Qed.
Lemma D_63558 : decode_any W_63558 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6355c : bv 32 := 0xfff68693.
Lemma F_6355c : fetch_word AsanUbsan.M.loaded_segments (0x6355c : word) = Some W_6355c.
Proof. vm_refl. Qed.
Lemma D_6355c : decode_any W_6355c = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63560 : bv 32 := 0x00c6f6b3.
Lemma F_63560 : fetch_word AsanUbsan.M.loaded_segments (0x63560 : word) = Some W_63560.
Proof. vm_refl. Qed.
Lemma D_63560 : decode_any W_63560 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63564 : bv 32 := 0x04a6f263.
Lemma F_63564 : fetch_word AsanUbsan.M.loaded_segments (0x63564 : word) = Some W_63564.
Proof. vm_refl. Qed.
Lemma D_63564 : decode_any W_63564 = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63568 : bv 32 := 0x0007b697.
Lemma F_63568 : fetch_word AsanUbsan.M.loaded_segments (0x63568 : word) = Some W_63568.
Proof. vm_refl. Qed.
Lemma D_63568 : decode_any W_63568 = Some (Auipc 13 123, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6356c : bv 32 := 0xf306b683.
Lemma F_6356c : fetch_word AsanUbsan.M.loaded_segments (0x6356c : word) = Some W_6356c.
Proof. vm_refl. Qed.
Lemma D_6356c : decode_any W_6356c = Some (Load SZ8 true 13 13 3888, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63570 : bv 32 := 0x0007b717.
Lemma F_63570 : fetch_word AsanUbsan.M.loaded_segments (0x63570 : word) = Some W_63570.
Proof. vm_refl. Qed.
Lemma D_63570 : decode_any W_63570 = Some (Auipc 14 123, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63574 : bv 32 := 0xf3073703.
Lemma F_63574 : fetch_word AsanUbsan.M.loaded_segments (0x63574 : word) = Some W_63574.
Proof. vm_refl. Qed.
Lemma D_63574 : decode_any W_63574 = Some (Load SZ8 true 14 14 3888, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63578 : bv 32 := 0x0006b803.
Lemma F_63578 : fetch_word AsanUbsan.M.loaded_segments (0x63578 : word) = Some W_63578.
Proof. vm_refl. Qed.
Lemma D_63578 : decode_any W_63578 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6357c : bv 32 := 0x00073683.
Lemma F_6357c : fetch_word AsanUbsan.M.loaded_segments (0x6357c : word) = Some W_6357c.
Proof. vm_refl. Qed.
Lemma D_6357c : decode_any W_6357c = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63580 : bv 32 := 0xfff80793.
Lemma F_63580 : fetch_word AsanUbsan.M.loaded_segments (0x63580 : word) = Some W_63580.
Proof. vm_refl. Qed.
Lemma D_63580 : decode_any W_63580 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63584 : bv 32 := 0x00a7f463.
Lemma F_63584 : fetch_word AsanUbsan.M.loaded_segments (0x63584 : word) = Some W_63584.
Proof. vm_refl. Qed.
Lemma D_63584 : decode_any W_63584 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63588 : bv 32 := 0x02a6f063.
Lemma F_63588 : fetch_word AsanUbsan.M.loaded_segments (0x63588 : word) = Some W_63588.
Proof. vm_refl. Qed.
Lemma D_63588 : decode_any W_63588 = Some (Branch BC_GEU 13 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6358c : bv 32 := 0x0007b717.
Lemma F_6358c : fetch_word AsanUbsan.M.loaded_segments (0x6358c : word) = Some W_6358c.
Proof. vm_refl. Qed.
Lemma D_6358c : decode_any W_6358c = Some (Auipc 14 123, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63590 : bv 32 := 0xf1c73703.
Lemma F_63590 : fetch_word AsanUbsan.M.loaded_segments (0x63590 : word) = Some W_63590.
Proof. vm_refl. Qed.
Lemma D_63590 : decode_any W_63590 = Some (Load SZ8 true 14 14 3868, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63594 : bv 32 := 0x00073283.
Lemma F_63594 : fetch_word AsanUbsan.M.loaded_segments (0x63594 : word) = Some W_63594.
Proof. vm_refl. Qed.
Lemma D_63594 : decode_any W_63594 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63598 : bv 32 := 0x0032d713.
Lemma F_63598 : fetch_word AsanUbsan.M.loaded_segments (0x63598 : word) = Some W_63598.
Proof. vm_refl. Qed.
Lemma D_63598 : decode_any W_63598 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6359c : bv 32 := 0x00b708b3.
Lemma F_6359c : fetch_word AsanUbsan.M.loaded_segments (0x6359c : word) = Some W_6359c.
Proof. vm_refl. Qed.
Lemma D_6359c : decode_any W_6359c = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635a0 : bv 32 := 0x00a2ea63.
Lemma F_635a0 : fetch_word AsanUbsan.M.loaded_segments (0x635a0 : word) = Some W_635a0.
Proof. vm_refl. Qed.
Lemma D_635a0 : decode_any W_635a0 = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635a4 : bv 32 := 0x00a8f863.
Lemma F_635a4 : fetch_word AsanUbsan.M.loaded_segments (0x635a4 : word) = Some W_635a4.
Proof. vm_refl. Qed.
Lemma D_635a4 : decode_any W_635a4 = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635a8 : bv 32 := 0x00355513.
Lemma F_635a8 : fetch_word AsanUbsan.M.loaded_segments (0x635a8 : word) = Some W_635a8.
Proof. vm_refl. Qed.
Lemma D_635a8 : decode_any W_635a8 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635ac : bv 32 := 0x00a58533.
Lemma F_635ac : fetch_word AsanUbsan.M.loaded_segments (0x635ac : word) = Some W_635ac.
Proof. vm_refl. Qed.
Lemma D_635ac : decode_any W_635ac = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635b0 : bv 32 := 0x00008067.
Lemma F_635b0 : fetch_word AsanUbsan.M.loaded_segments (0x635b0 : word) = Some W_635b0.
Proof. vm_refl. Qed.
Lemma D_635b0 : decode_any W_635b0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
