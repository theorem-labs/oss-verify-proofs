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
Definition W_63540 : bv 32 := 0x00000593.
Lemma F_63540 : fetch_word AsanUbsan.M.loaded_segments (0x63540 : word) = Some W_63540.
Proof. vm_refl. Qed.
Lemma D_63540 : decode_any W_63540 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63544 : bv 32 := 0x00b50633.
Lemma F_63544 : fetch_word AsanUbsan.M.loaded_segments (0x63544 : word) = Some W_63544.
Proof. vm_refl. Qed.
Lemma D_63544 : decode_any W_63544 = Some (Op ALU_ADD 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63548 : bv 32 := 0x00064603.
Lemma F_63548 : fetch_word AsanUbsan.M.loaded_segments (0x63548 : word) = Some W_63548.
Proof. vm_refl. Qed.
Lemma D_63548 : decode_any W_63548 = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6354c : bv 32 := 0x00158593.
Lemma F_6354c : fetch_word AsanUbsan.M.loaded_segments (0x6354c : word) = Some W_6354c.
Proof. vm_refl. Qed.
Lemma D_6354c : decode_any W_6354c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63550 : bv 32 := 0xfe061ae3.
Lemma F_63550 : fetch_word AsanUbsan.M.loaded_segments (0x63550 : word) = Some W_63550.
Proof. vm_refl. Qed.
Lemma D_63550 : decode_any W_63550 = Some (Branch BC_NE 12 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63554 : bv 32 := 0xfff58513.
Lemma F_63554 : fetch_word AsanUbsan.M.loaded_segments (0x63554 : word) = Some W_63554.
Proof. vm_refl. Qed.
Lemma D_63554 : decode_any W_63554 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63558 : bv 32 := 0x00008067.
Lemma F_63558 : fetch_word AsanUbsan.M.loaded_segments (0x63558 : word) = Some W_63558.
Proof. vm_refl. Qed.
Lemma D_63558 : decode_any W_63558 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
