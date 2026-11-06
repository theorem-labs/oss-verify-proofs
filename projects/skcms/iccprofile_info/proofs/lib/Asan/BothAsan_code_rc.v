(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_43710 : bv 32 := 0xfff4c593.
Lemma F_43710 : fetch_word AsanUbsan.M.loaded_segments (0x43710 : word) = Some W_43710.
Proof. vm_refl. Qed.
Lemma D_43710 : decode_any W_43710 = Some (OpImm ALU_XOR 11 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_43714 : bv 32 := 0x80040a13.
Lemma F_43714 : fetch_word AsanUbsan.M.loaded_segments (0x43714 : word) = Some W_43714.
Proof. vm_refl. Qed.
Lemma D_43714 : decode_any W_43714 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_43718 : bv 32 := 0xfb8a0a13.
Lemma F_43718 : fetch_word AsanUbsan.M.loaded_segments (0x43718 : word) = Some W_43718.
Proof. vm_refl. Qed.
Lemma D_43718 : decode_any W_43718 = Some (OpImm ALU_ADD 20 20 4024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4371c : bv 32 := 0x06a5e863.
Lemma F_4371c : fetch_word AsanUbsan.M.loaded_segments (0x4371c : word) = Some W_4371c.
Proof. vm_refl. Qed.
Lemma D_4371c : decode_any W_4371c = Some (Branch BC_LTU 11 10 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_43720 : bv 32 := 0xfbf50593.
Lemma F_43720 : fetch_word AsanUbsan.M.loaded_segments (0x43720 : word) = Some W_43720.
Proof. vm_refl. Qed.
Lemma D_43720 : decode_any W_43720 = Some (OpImm ALU_ADD 11 10 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_43724 : bv 32 := 0xfc000613.
Lemma F_43724 : fetch_word AsanUbsan.M.loaded_segments (0x43724 : word) = Some W_43724.
Proof. vm_refl. Qed.
Lemma D_43724 : decode_any W_43724 = Some (OpImm ALU_ADD 12 0 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_43728 : bv 32 := 0x0cc5ee63.
Lemma F_43728 : fetch_word AsanUbsan.M.loaded_segments (0x43728 : word) = Some W_43728.
Proof. vm_refl. Qed.
Lemma D_43728 : decode_any W_43728 = Some (Branch BC_LTU 11 12 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4372c : bv 32 := 0x0005c597.
Lemma F_4372c : fetch_word AsanUbsan.M.loaded_segments (0x4372c : word) = Some W_4372c.
Proof. vm_refl. Qed.
Lemma D_4372c : decode_any W_4372c = Some (Auipc 11 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_43730 : bv 32 := 0x1f45b583.
Lemma F_43730 : fetch_word AsanUbsan.M.loaded_segments (0x43730 : word) = Some W_43730.
Proof. vm_refl. Qed.
Lemma D_43730 : decode_any W_43730 = Some (Load SZ8 true 11 11 500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_43734 : bv 32 := 0x00a486b3.
Lemma F_43734 : fetch_word AsanUbsan.M.loaded_segments (0x43734 : word) = Some W_43734.
Proof. vm_refl. Qed.
Lemma D_43734 : decode_any W_43734 = Some (Op ALU_ADD 13 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_43738 : bv 32 := 0x0005b603.
Lemma F_43738 : fetch_word AsanUbsan.M.loaded_segments (0x43738 : word) = Some W_43738.
Proof. vm_refl. Qed.
Lemma D_43738 : decode_any W_43738 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4373c : bv 32 := 0x0034d593.
Lemma F_4373c : fetch_word AsanUbsan.M.loaded_segments (0x4373c : word) = Some W_4373c.
Proof. vm_refl. Qed.
Lemma D_4373c : decode_any W_4373c = Some (ShiftImm ALU_SRL 11 9 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_43740 : bv 32 := 0xfff68693.
Lemma F_43740 : fetch_word AsanUbsan.M.loaded_segments (0x43740 : word) = Some W_43740.
Proof. vm_refl. Qed.
Lemma D_43740 : decode_any W_43740 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_43744 : bv 32 := 0x0036d713.
Lemma F_43744 : fetch_word AsanUbsan.M.loaded_segments (0x43744 : word) = Some W_43744.
Proof. vm_refl. Qed.
Lemma D_43744 : decode_any W_43744 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_43748 : bv 32 := 0x00b605b3.
Lemma F_43748 : fetch_word AsanUbsan.M.loaded_segments (0x43748 : word) = Some W_43748.
Proof. vm_refl. Qed.
Lemma D_43748 : decode_any W_43748 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4374c : bv 32 := 0x00e60633.
Lemma F_4374c : fetch_word AsanUbsan.M.loaded_segments (0x4374c : word) = Some W_4374c.
Proof. vm_refl. Qed.
Lemma D_4374c : decode_any W_4374c = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_43750 : bv 32 := 0xff85f713.
Lemma F_43750 : fetch_word AsanUbsan.M.loaded_segments (0x43750 : word) = Some W_43750.
Proof. vm_refl. Qed.
Lemma D_43750 : decode_any W_43750 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_43754 : bv 32 := 0xff867793.
Lemma F_43754 : fetch_word AsanUbsan.M.loaded_segments (0x43754 : word) = Some W_43754.
Proof. vm_refl. Qed.
Lemma D_43754 : decode_any W_43754 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_43758 : bv 32 := 0x00073703.
Lemma F_43758 : fetch_word AsanUbsan.M.loaded_segments (0x43758 : word) = Some W_43758.
Proof. vm_refl. Qed.
Lemma D_43758 : decode_any W_43758 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4375c : bv 32 := 0x0007b783.
Lemma F_4375c : fetch_word AsanUbsan.M.loaded_segments (0x4375c : word) = Some W_4375c.
Proof. vm_refl. Qed.
Lemma D_4375c : decode_any W_4375c = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_43760 : bv 32 := 0x00e7e733.
Lemma F_43760 : fetch_word AsanUbsan.M.loaded_segments (0x43760 : word) = Some W_43760.
Proof. vm_refl. Qed.
Lemma D_43760 : decode_any W_43760 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_43764 : bv 32 := 0x14071663.
Lemma F_43764 : fetch_word AsanUbsan.M.loaded_segments (0x43764 : word) = Some W_43764.
Proof. vm_refl. Qed.
Lemma D_43764 : decode_any W_43764 = Some (Branch BC_NE 14 0 332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_43768 : bv 32 := 0x06010113.
Lemma F_43768 : fetch_word AsanUbsan.M.loaded_segments (0x43768 : word) = Some W_43768.
Proof. vm_refl. Qed.
Lemma D_43768 : decode_any W_43768 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.
