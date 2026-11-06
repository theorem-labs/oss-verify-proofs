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
Definition W_66300 : bv 32 := 0x00000593.
Lemma F_66300 : fetch_word AsanUbsan.M.loaded_segments (0x66300 : word) = Some W_66300.
Proof. vm_refl. Qed.
Lemma D_66300 : decode_any W_66300 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66304 : bv 32 := 0x00b50633.
Lemma F_66304 : fetch_word AsanUbsan.M.loaded_segments (0x66304 : word) = Some W_66304.
Proof. vm_refl. Qed.
Lemma D_66304 : decode_any W_66304 = Some (Op ALU_ADD 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66308 : bv 32 := 0x00064603.
Lemma F_66308 : fetch_word AsanUbsan.M.loaded_segments (0x66308 : word) = Some W_66308.
Proof. vm_refl. Qed.
Lemma D_66308 : decode_any W_66308 = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6630c : bv 32 := 0x00158593.
Lemma F_6630c : fetch_word AsanUbsan.M.loaded_segments (0x6630c : word) = Some W_6630c.
Proof. vm_refl. Qed.
Lemma D_6630c : decode_any W_6630c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66310 : bv 32 := 0xfe061ae3.
Lemma F_66310 : fetch_word AsanUbsan.M.loaded_segments (0x66310 : word) = Some W_66310.
Proof. vm_refl. Qed.
Lemma D_66310 : decode_any W_66310 = Some (Branch BC_NE 12 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66314 : bv 32 := 0xfff58513.
Lemma F_66314 : fetch_word AsanUbsan.M.loaded_segments (0x66314 : word) = Some W_66314.
Proof. vm_refl. Qed.
Lemma D_66314 : decode_any W_66314 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66318 : bv 32 := 0x00008067.
Lemma F_66318 : fetch_word AsanUbsan.M.loaded_segments (0x66318 : word) = Some W_66318.
Proof. vm_refl. Qed.
Lemma D_66318 : decode_any W_66318 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
