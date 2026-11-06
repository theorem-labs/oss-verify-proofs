(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation ASEGS_I := ImgA.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_78158 : bv 32 := 0x63d0f0ef.
Lemma F_78158 : fetch_word ASEGS_I (0x78158 : word) = Some W_78158.
Proof. vm_refl. Qed.
Lemma D_78158 : decode_any W_78158 = Some (Jal 1 65084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7815c : bv 32 := 0xfa050ce3.
Lemma F_7815c : fetch_word ASEGS_I (0x7815c : word) = Some W_7815c.
Proof. vm_refl. Qed.
Lemma D_7815c : decode_any W_7815c = Some (Branch BC_EQ 10 0 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78160 : bv 32 := 0x00000413.
Lemma F_78160 : fetch_word ASEGS_I (0x78160 : word) = Some W_78160.
Proof. vm_refl. Qed.
Lemma D_78160 : decode_any W_78160 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78164 : bv 32 := 0x00040513.
Lemma F_78164 : fetch_word ASEGS_I (0x78164 : word) = Some W_78164.
Proof. vm_refl. Qed.
Lemma D_78164 : decode_any W_78164 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78168 : bv 32 := 0x03813083.
Lemma F_78168 : fetch_word ASEGS_I (0x78168 : word) = Some W_78168.
Proof. vm_refl. Qed.
Lemma D_78168 : decode_any W_78168 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7816c : bv 32 := 0x03013403.
Lemma F_7816c : fetch_word ASEGS_I (0x7816c : word) = Some W_7816c.
Proof. vm_refl. Qed.
Lemma D_7816c : decode_any W_7816c = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78170 : bv 32 := 0x02813483.
Lemma F_78170 : fetch_word ASEGS_I (0x78170 : word) = Some W_78170.
Proof. vm_refl. Qed.
Lemma D_78170 : decode_any W_78170 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78174 : bv 32 := 0x02013903.
Lemma F_78174 : fetch_word ASEGS_I (0x78174 : word) = Some W_78174.
Proof. vm_refl. Qed.
Lemma D_78174 : decode_any W_78174 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78178 : bv 32 := 0x01813983.
Lemma F_78178 : fetch_word ASEGS_I (0x78178 : word) = Some W_78178.
Proof. vm_refl. Qed.
Lemma D_78178 : decode_any W_78178 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7817c : bv 32 := 0x01013a03.
Lemma F_7817c : fetch_word ASEGS_I (0x7817c : word) = Some W_7817c.
Proof. vm_refl. Qed.
Lemma D_7817c : decode_any W_7817c = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78180 : bv 32 := 0x00813a83.
Lemma F_78180 : fetch_word ASEGS_I (0x78180 : word) = Some W_78180.
Proof. vm_refl. Qed.
Lemma D_78180 : decode_any W_78180 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78184 : bv 32 := 0x04010113.
Lemma F_78184 : fetch_word ASEGS_I (0x78184 : word) = Some W_78184.
Proof. vm_refl. Qed.
Lemma D_78184 : decode_any W_78184 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78188 : bv 32 := 0x00008067.
Lemma F_78188 : fetch_word ASEGS_I (0x78188 : word) = Some W_78188.
Proof. vm_refl. Qed.
Lemma D_78188 : decode_any W_78188 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7818c : bv 32 := 0x000b2297.
Lemma F_7818c : fetch_word ASEGS_I (0x7818c : word) = Some W_7818c.
Proof. vm_refl. Qed.
Lemma D_7818c : decode_any W_7818c = Some (Auipc 5 178, 4%Z).
Proof. vm_refl. Qed.
