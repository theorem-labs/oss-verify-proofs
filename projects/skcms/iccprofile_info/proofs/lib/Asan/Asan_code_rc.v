(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_436e4 : bv 32 := 0xfff4c593.
Lemma F_436e4 : fetch_word Asan.M.loaded_segments (0x436e4 : word) = Some W_436e4.
Proof. vm_refl. Qed.
Lemma D_436e4 : decode_any W_436e4 = Some (OpImm ALU_XOR 11 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_436e8 : bv 32 := 0x80040a13.
Lemma F_436e8 : fetch_word Asan.M.loaded_segments (0x436e8 : word) = Some W_436e8.
Proof. vm_refl. Qed.
Lemma D_436e8 : decode_any W_436e8 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_436ec : bv 32 := 0xfb8a0a13.
Lemma F_436ec : fetch_word Asan.M.loaded_segments (0x436ec : word) = Some W_436ec.
Proof. vm_refl. Qed.
Lemma D_436ec : decode_any W_436ec = Some (OpImm ALU_ADD 20 20 4024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_436f0 : bv 32 := 0x06a5e863.
Lemma F_436f0 : fetch_word Asan.M.loaded_segments (0x436f0 : word) = Some W_436f0.
Proof. vm_refl. Qed.
Lemma D_436f0 : decode_any W_436f0 = Some (Branch BC_LTU 11 10 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_436f4 : bv 32 := 0xfbf50593.
Lemma F_436f4 : fetch_word Asan.M.loaded_segments (0x436f4 : word) = Some W_436f4.
Proof. vm_refl. Qed.
Lemma D_436f4 : decode_any W_436f4 = Some (OpImm ALU_ADD 11 10 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_436f8 : bv 32 := 0xfc000613.
Lemma F_436f8 : fetch_word Asan.M.loaded_segments (0x436f8 : word) = Some W_436f8.
Proof. vm_refl. Qed.
Lemma D_436f8 : decode_any W_436f8 = Some (OpImm ALU_ADD 12 0 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_436fc : bv 32 := 0x0cc5ee63.
Lemma F_436fc : fetch_word Asan.M.loaded_segments (0x436fc : word) = Some W_436fc.
Proof. vm_refl. Qed.
Lemma D_436fc : decode_any W_436fc = Some (Branch BC_LTU 11 12 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_43700 : bv 32 := 0x0005b597.
Lemma F_43700 : fetch_word Asan.M.loaded_segments (0x43700 : word) = Some W_43700.
Proof. vm_refl. Qed.
Lemma D_43700 : decode_any W_43700 = Some (Auipc 11 91, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_43704 : bv 32 := 0x3f05b583.
Lemma F_43704 : fetch_word Asan.M.loaded_segments (0x43704 : word) = Some W_43704.
Proof. vm_refl. Qed.
Lemma D_43704 : decode_any W_43704 = Some (Load SZ8 true 11 11 1008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_43708 : bv 32 := 0x00a486b3.
Lemma F_43708 : fetch_word Asan.M.loaded_segments (0x43708 : word) = Some W_43708.
Proof. vm_refl. Qed.
Lemma D_43708 : decode_any W_43708 = Some (Op ALU_ADD 13 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4370c : bv 32 := 0x0005b603.
Lemma F_4370c : fetch_word Asan.M.loaded_segments (0x4370c : word) = Some W_4370c.
Proof. vm_refl. Qed.
Lemma D_4370c : decode_any W_4370c = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_43710 : bv 32 := 0x0034d593.
Lemma F_43710 : fetch_word Asan.M.loaded_segments (0x43710 : word) = Some W_43710.
Proof. vm_refl. Qed.
Lemma D_43710 : decode_any W_43710 = Some (ShiftImm ALU_SRL 11 9 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_43714 : bv 32 := 0xfff68693.
Lemma F_43714 : fetch_word Asan.M.loaded_segments (0x43714 : word) = Some W_43714.
Proof. vm_refl. Qed.
Lemma D_43714 : decode_any W_43714 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_43718 : bv 32 := 0x0036d713.
Lemma F_43718 : fetch_word Asan.M.loaded_segments (0x43718 : word) = Some W_43718.
Proof. vm_refl. Qed.
Lemma D_43718 : decode_any W_43718 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4371c : bv 32 := 0x00b605b3.
Lemma F_4371c : fetch_word Asan.M.loaded_segments (0x4371c : word) = Some W_4371c.
Proof. vm_refl. Qed.
Lemma D_4371c : decode_any W_4371c = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_43720 : bv 32 := 0x00e60633.
Lemma F_43720 : fetch_word Asan.M.loaded_segments (0x43720 : word) = Some W_43720.
Proof. vm_refl. Qed.
Lemma D_43720 : decode_any W_43720 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_43724 : bv 32 := 0xff85f713.
Lemma F_43724 : fetch_word Asan.M.loaded_segments (0x43724 : word) = Some W_43724.
Proof. vm_refl. Qed.
Lemma D_43724 : decode_any W_43724 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_43728 : bv 32 := 0xff867793.
Lemma F_43728 : fetch_word Asan.M.loaded_segments (0x43728 : word) = Some W_43728.
Proof. vm_refl. Qed.
Lemma D_43728 : decode_any W_43728 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4372c : bv 32 := 0x00073703.
Lemma F_4372c : fetch_word Asan.M.loaded_segments (0x4372c : word) = Some W_4372c.
Proof. vm_refl. Qed.
Lemma D_4372c : decode_any W_4372c = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_43730 : bv 32 := 0x0007b783.
Lemma F_43730 : fetch_word Asan.M.loaded_segments (0x43730 : word) = Some W_43730.
Proof. vm_refl. Qed.
Lemma D_43730 : decode_any W_43730 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_43734 : bv 32 := 0x00e7e733.
Lemma F_43734 : fetch_word Asan.M.loaded_segments (0x43734 : word) = Some W_43734.
Proof. vm_refl. Qed.
Lemma D_43734 : decode_any W_43734 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_43738 : bv 32 := 0x14071663.
Lemma F_43738 : fetch_word Asan.M.loaded_segments (0x43738 : word) = Some W_43738.
Proof. vm_refl. Qed.
Lemma D_43738 : decode_any W_43738 = Some (Branch BC_NE 14 0 332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4373c : bv 32 := 0x06010113.
Lemma F_4373c : fetch_word Asan.M.loaded_segments (0x4373c : word) = Some W_4373c.
Proof. vm_refl. Qed.
Lemma D_4373c : decode_any W_4373c = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.
