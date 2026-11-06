(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_45fb0 : bv 32 := 0xfff4c593.
Lemma F_45fb0 : fetch_word Asan.M.loaded_segments (0x45fb0 : word) = Some W_45fb0.
Proof. vm_refl. Qed.
Lemma D_45fb0 : decode_any W_45fb0 = Some (OpImm ALU_XOR 11 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45fb4 : bv 32 := 0x80040a13.
Lemma F_45fb4 : fetch_word Asan.M.loaded_segments (0x45fb4 : word) = Some W_45fb4.
Proof. vm_refl. Qed.
Lemma D_45fb4 : decode_any W_45fb4 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45fb8 : bv 32 := 0xfb8a0a13.
Lemma F_45fb8 : fetch_word Asan.M.loaded_segments (0x45fb8 : word) = Some W_45fb8.
Proof. vm_refl. Qed.
Lemma D_45fb8 : decode_any W_45fb8 = Some (OpImm ALU_ADD 20 20 4024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45fbc : bv 32 := 0x06a5e863.
Lemma F_45fbc : fetch_word Asan.M.loaded_segments (0x45fbc : word) = Some W_45fbc.
Proof. vm_refl. Qed.
Lemma D_45fbc : decode_any W_45fbc = Some (Branch BC_LTU 11 10 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45fc0 : bv 32 := 0xfbf50593.
Lemma F_45fc0 : fetch_word Asan.M.loaded_segments (0x45fc0 : word) = Some W_45fc0.
Proof. vm_refl. Qed.
Lemma D_45fc0 : decode_any W_45fc0 = Some (OpImm ALU_ADD 11 10 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45fc4 : bv 32 := 0xfc000613.
Lemma F_45fc4 : fetch_word Asan.M.loaded_segments (0x45fc4 : word) = Some W_45fc4.
Proof. vm_refl. Qed.
Lemma D_45fc4 : decode_any W_45fc4 = Some (OpImm ALU_ADD 12 0 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45fc8 : bv 32 := 0x0cc5ee63.
Lemma F_45fc8 : fetch_word Asan.M.loaded_segments (0x45fc8 : word) = Some W_45fc8.
Proof. vm_refl. Qed.
Lemma D_45fc8 : decode_any W_45fc8 = Some (Branch BC_LTU 11 12 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45fcc : bv 32 := 0x00065597.
Lemma F_45fcc : fetch_word Asan.M.loaded_segments (0x45fcc : word) = Some W_45fcc.
Proof. vm_refl. Qed.
Lemma D_45fcc : decode_any W_45fcc = Some (Auipc 11 101, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45fd0 : bv 32 := 0xeb45b583.
Lemma F_45fd0 : fetch_word Asan.M.loaded_segments (0x45fd0 : word) = Some W_45fd0.
Proof. vm_refl. Qed.
Lemma D_45fd0 : decode_any W_45fd0 = Some (Load SZ8 true 11 11 3764, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45fd4 : bv 32 := 0x00a486b3.
Lemma F_45fd4 : fetch_word Asan.M.loaded_segments (0x45fd4 : word) = Some W_45fd4.
Proof. vm_refl. Qed.
Lemma D_45fd4 : decode_any W_45fd4 = Some (Op ALU_ADD 13 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45fd8 : bv 32 := 0x0005b603.
Lemma F_45fd8 : fetch_word Asan.M.loaded_segments (0x45fd8 : word) = Some W_45fd8.
Proof. vm_refl. Qed.
Lemma D_45fd8 : decode_any W_45fd8 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45fdc : bv 32 := 0x0034d593.
Lemma F_45fdc : fetch_word Asan.M.loaded_segments (0x45fdc : word) = Some W_45fdc.
Proof. vm_refl. Qed.
Lemma D_45fdc : decode_any W_45fdc = Some (ShiftImm ALU_SRL 11 9 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45fe0 : bv 32 := 0xfff68693.
Lemma F_45fe0 : fetch_word Asan.M.loaded_segments (0x45fe0 : word) = Some W_45fe0.
Proof. vm_refl. Qed.
Lemma D_45fe0 : decode_any W_45fe0 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45fe4 : bv 32 := 0x0036d713.
Lemma F_45fe4 : fetch_word Asan.M.loaded_segments (0x45fe4 : word) = Some W_45fe4.
Proof. vm_refl. Qed.
Lemma D_45fe4 : decode_any W_45fe4 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45fe8 : bv 32 := 0x00b605b3.
Lemma F_45fe8 : fetch_word Asan.M.loaded_segments (0x45fe8 : word) = Some W_45fe8.
Proof. vm_refl. Qed.
Lemma D_45fe8 : decode_any W_45fe8 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45fec : bv 32 := 0x00e60633.
Lemma F_45fec : fetch_word Asan.M.loaded_segments (0x45fec : word) = Some W_45fec.
Proof. vm_refl. Qed.
Lemma D_45fec : decode_any W_45fec = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45ff0 : bv 32 := 0xff85f713.
Lemma F_45ff0 : fetch_word Asan.M.loaded_segments (0x45ff0 : word) = Some W_45ff0.
Proof. vm_refl. Qed.
Lemma D_45ff0 : decode_any W_45ff0 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45ff4 : bv 32 := 0xff867793.
Lemma F_45ff4 : fetch_word Asan.M.loaded_segments (0x45ff4 : word) = Some W_45ff4.
Proof. vm_refl. Qed.
Lemma D_45ff4 : decode_any W_45ff4 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45ff8 : bv 32 := 0x00073703.
Lemma F_45ff8 : fetch_word Asan.M.loaded_segments (0x45ff8 : word) = Some W_45ff8.
Proof. vm_refl. Qed.
Lemma D_45ff8 : decode_any W_45ff8 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_45ffc : bv 32 := 0x0007b783.
Lemma F_45ffc : fetch_word Asan.M.loaded_segments (0x45ffc : word) = Some W_45ffc.
Proof. vm_refl. Qed.
Lemma D_45ffc : decode_any W_45ffc = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_46000 : bv 32 := 0x00e7e733.
Lemma F_46000 : fetch_word Asan.M.loaded_segments (0x46000 : word) = Some W_46000.
Proof. vm_refl. Qed.
Lemma D_46000 : decode_any W_46000 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_46004 : bv 32 := 0x14071663.
Lemma F_46004 : fetch_word Asan.M.loaded_segments (0x46004 : word) = Some W_46004.
Proof. vm_refl. Qed.
Lemma D_46004 : decode_any W_46004 = Some (Branch BC_NE 14 0 332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_46008 : bv 32 := 0x06010113.
Lemma F_46008 : fetch_word Asan.M.loaded_segments (0x46008 : word) = Some W_46008.
Proof. vm_refl. Qed.
Lemma D_46008 : decode_any W_46008 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.
