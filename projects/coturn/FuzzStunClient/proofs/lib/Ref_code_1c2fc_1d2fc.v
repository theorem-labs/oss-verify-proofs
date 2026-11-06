(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

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
Definition W_1c430 : bv 32 := 0x00072503.
Lemma F_1c430 : fetch_word Plain.M.loaded_segments (0x1c430 : word) = Some W_1c430.
Proof. vm_refl. Qed.
Lemma D_1c430 : decode_any W_1c430 = Some (Load SZ4 true 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c434 : bv 32 := 0x00b56633.
Lemma F_1c434 : fetch_word Plain.M.loaded_segments (0x1c434 : word) = Some W_1c434.
Proof. vm_refl. Qed.
Lemma D_1c434 : decode_any W_1c434 = Some (Op ALU_OR 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c438 : bv 32 := 0x160726af.
Lemma F_1c438 : fetch_word Plain.M.loaded_segments (0x1c438 : word) = Some W_1c438.
Proof. vm_refl. Qed.
Lemma D_1c438 : decode_any W_1c438 = Some (Lr AW true true 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c43c : bv 32 := 0x00a69663.
Lemma F_1c43c : fetch_word Plain.M.loaded_segments (0x1c43c : word) = Some W_1c43c.
Proof. vm_refl. Qed.
Lemma D_1c43c : decode_any W_1c43c = Some (Branch BC_NE 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c440 : bv 32 := 0x1ec727af.
Lemma F_1c440 : fetch_word Plain.M.loaded_segments (0x1c440 : word) = Some W_1c440.
Proof. vm_refl. Qed.
Lemma D_1c440 : decode_any W_1c440 = Some (Sc AW true true 15 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c444 : bv 32 := 0xfe079ae3.
Lemma F_1c444 : fetch_word Plain.M.loaded_segments (0x1c444 : word) = Some W_1c444.
Proof. vm_refl. Qed.
Lemma D_1c444 : decode_any W_1c444 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c448 : bv 32 := 0x0006869b.
Lemma F_1c448 : fetch_word Plain.M.loaded_segments (0x1c448 : word) = Some W_1c448.
Proof. vm_refl. Qed.
Lemma D_1c448 : decode_any W_1c448 = Some (OpImm32 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c44c : bv 32 := 0xfea692e3.
Lemma F_1c44c : fetch_word Plain.M.loaded_segments (0x1c44c : word) = Some W_1c44c.
Proof. vm_refl. Qed.
Lemma D_1c44c : decode_any W_1c44c = Some (Branch BC_NE 13 10 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc10 : bv 32 := 0x00062703.
Lemma F_1cc10 : fetch_word Plain.M.loaded_segments (0x1cc10 : word) = Some W_1cc10.
Proof. vm_refl. Qed.
Lemma D_1cc10 : decode_any W_1cc10 = Some (Load SZ4 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc14 : bv 32 := 0x00d777b3.
Lemma F_1cc14 : fetch_word Plain.M.loaded_segments (0x1cc14 : word) = Some W_1cc14.
Proof. vm_refl. Qed.
Lemma D_1cc14 : decode_any W_1cc14 = Some (Op ALU_AND 15 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc18 : bv 32 := 0x1606282f.
Lemma F_1cc18 : fetch_word Plain.M.loaded_segments (0x1cc18 : word) = Some W_1cc18.
Proof. vm_refl. Qed.
Lemma D_1cc18 : decode_any W_1cc18 = Some (Lr AW true true 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc1c : bv 32 := 0x00e81663.
Lemma F_1cc1c : fetch_word Plain.M.loaded_segments (0x1cc1c : word) = Some W_1cc1c.
Proof. vm_refl. Qed.
Lemma D_1cc1c : decode_any W_1cc1c = Some (Branch BC_NE 16 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc20 : bv 32 := 0x1ef628af.
Lemma F_1cc20 : fetch_word Plain.M.loaded_segments (0x1cc20 : word) = Some W_1cc20.
Proof. vm_refl. Qed.
Lemma D_1cc20 : decode_any W_1cc20 = Some (Sc AW true true 17 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc24 : bv 32 := 0xfe089ae3.
Lemma F_1cc24 : fetch_word Plain.M.loaded_segments (0x1cc24 : word) = Some W_1cc24.
Proof. vm_refl. Qed.
Lemma D_1cc24 : decode_any W_1cc24 = Some (Branch BC_NE 17 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc28 : bv 32 := 0x0008081b.
Lemma F_1cc28 : fetch_word Plain.M.loaded_segments (0x1cc28 : word) = Some W_1cc28.
Proof. vm_refl. Qed.
Lemma D_1cc28 : decode_any W_1cc28 = Some (OpImm32 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1cc2c : bv 32 := 0xfee812e3.
Lemma F_1cc2c : fetch_word Plain.M.loaded_segments (0x1cc2c : word) = Some W_1cc2c.
Proof. vm_refl. Qed.
Lemma D_1cc2c : decode_any W_1cc2c = Some (Branch BC_NE 16 14 8164, 4%Z).
Proof. vm_refl. Qed.
