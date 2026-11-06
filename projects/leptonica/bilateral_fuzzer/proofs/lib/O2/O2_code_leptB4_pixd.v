(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_193d0 : bv 32 := 0xfe010113.
Lemma F_193d0 : fetch_word Plain.M.loaded_segments (0x19428 : word) = Some W_193d0.
Proof. vm_refl. Qed.
Lemma D_193d0 : decode_any W_193d0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193d4 : bv 32 := 0x00113c23.
Lemma F_193d4 : fetch_word Plain.M.loaded_segments (0x1942c : word) = Some W_193d4.
Proof. vm_refl. Qed.
Lemma D_193d4 : decode_any W_193d4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193d8 : bv 32 := 0x00813823.
Lemma F_193d8 : fetch_word Plain.M.loaded_segments (0x19430 : word) = Some W_193d8.
Proof. vm_refl. Qed.
Lemma D_193d8 : decode_any W_193d8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193dc : bv 32 := 0x00913423.
Lemma F_193dc : fetch_word Plain.M.loaded_segments (0x19434 : word) = Some W_193dc.
Proof. vm_refl. Qed.
Lemma D_193dc : decode_any W_193dc = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193e0 : bv 32 := 0x06050863.
Lemma F_193e0 : fetch_word Plain.M.loaded_segments (0x19438 : word) = Some W_193e0.
Proof. vm_refl. Qed.
Lemma D_193e0 : decode_any W_193e0 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193e4 : bv 32 := 0x00053403.
Lemma F_193e4 : fetch_word Plain.M.loaded_segments (0x1943c : word) = Some W_193e4.
Proof. vm_refl. Qed.
Lemma D_193e4 : decode_any W_193e4 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193e8 : bv 32 := 0x0a040063.
Lemma F_193e8 : fetch_word Plain.M.loaded_segments (0x19440 : word) = Some W_193e8.
Proof. vm_refl. Qed.
Lemma D_193e8 : decode_any W_193e8 = Some (Branch BC_EQ 8 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193ec : bv 32 := 0x01440593.
Lemma F_193ec : fetch_word Plain.M.loaded_segments (0x19444 : word) = Some W_193ec.
Proof. vm_refl. Qed.
Lemma D_193ec : decode_any W_193ec = Some (OpImm ALU_ADD 11 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193f0 : bv 32 := 0xfff00613.
Lemma F_193f0 : fetch_word Plain.M.loaded_segments (0x19448 : word) = Some W_193f0.
Proof. vm_refl. Qed.
Lemma D_193f0 : decode_any W_193f0 = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193f4 : bv 32 := 0x06c5a5af.
Lemma F_193f4 : fetch_word Plain.M.loaded_segments (0x1944c : word) = Some W_193f4.
Proof. vm_refl. Qed.
Lemma D_193f4 : decode_any W_193f4 = Some (Amo AMO_ADD AW true true 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193f8 : bv 32 := 0x00100613.
Lemma F_193f8 : fetch_word Plain.M.loaded_segments (0x19450 : word) = Some W_193f8.
Proof. vm_refl. Qed.
Lemma D_193f8 : decode_any W_193f8 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193fc : bv 32 := 0x04c59663.
Lemma F_193fc : fetch_word Plain.M.loaded_segments (0x19454 : word) = Some W_193fc.
Proof. vm_refl. Qed.
Lemma D_193fc : decode_any W_193fc = Some (Branch BC_NE 11 12 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19400 : bv 32 := 0x00050493.
Lemma F_19400 : fetch_word Plain.M.loaded_segments (0x19458 : word) = Some W_19400.
Proof. vm_refl. Qed.
Lemma D_19400 : decode_any W_19400 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19404 : bv 32 := 0x03843503.
Lemma F_19404 : fetch_word Plain.M.loaded_segments (0x1945c : word) = Some W_19404.
Proof. vm_refl. Qed.
Lemma D_19404 : decode_any W_19404 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19408 : bv 32 := 0x00050863.
Lemma F_19408 : fetch_word Plain.M.loaded_segments (0x19460 : word) = Some W_19408.
Proof. vm_refl. Qed.
Lemma D_19408 : decode_any W_19408 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1940c : bv 32 := 0x00020597.
Lemma F_1940c : fetch_word Plain.M.loaded_segments (0x19464 : word) = Some W_1940c.
Proof. vm_refl. Qed.
Lemma D_1940c : decode_any W_1940c = Some (Auipc 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19410 : bv 32 := 0x0945b583.
Lemma F_19410 : fetch_word Plain.M.loaded_segments (0x19468 : word) = Some W_19410.
Proof. vm_refl. Qed.
Lemma D_19410 : decode_any W_19410 = Some (Load SZ8 true 11 11 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19414 : bv 32 := 0x000580e7.
Lemma F_19414 : fetch_word Plain.M.loaded_segments (0x1946c : word) = Some W_19414.
Proof. vm_refl. Qed.
Lemma D_19414 : decode_any W_19414 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19418 : bv 32 := 0x02843503.
Lemma F_19418 : fetch_word Plain.M.loaded_segments (0x19470 : word) = Some W_19418.
Proof. vm_refl. Qed.
Lemma D_19418 : decode_any W_19418 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1941c : bv 32 := 0x00050463.
Lemma F_1941c : fetch_word Plain.M.loaded_segments (0x19474 : word) = Some W_1941c.
Proof. vm_refl. Qed.
Lemma D_1941c : decode_any W_1941c = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19424 : bv 32 := 0x03043503.
Lemma F_19424 : fetch_word Plain.M.loaded_segments (0x1947c : word) = Some W_19424.
Proof. vm_refl. Qed.
Lemma D_19424 : decode_any W_19424 = Some (Load SZ8 true 10 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19428 : bv 32 := 0x00a13023.
Lemma F_19428 : fetch_word Plain.M.loaded_segments (0x19480 : word) = Some W_19428.
Proof. vm_refl. Qed.
Lemma D_19428 : decode_any W_19428 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1942c : bv 32 := 0x00050863.
Lemma F_1942c : fetch_word Plain.M.loaded_segments (0x19484 : word) = Some W_1942c.
Proof. vm_refl. Qed.
Lemma D_1942c : decode_any W_1942c = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19430 : bv 32 := 0x00010513.
Lemma F_19430 : fetch_word Plain.M.loaded_segments (0x19488 : word) = Some W_19430.
Proof. vm_refl. Qed.
Lemma D_19430 : decode_any W_19430 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19434 : bv 32 := 0x544030ef.
Lemma F_19434 : fetch_word Plain.M.loaded_segments (0x1948c : word) = Some W_19434.
Proof. vm_refl. Qed.
Lemma D_19434 : decode_any W_19434 = Some (Jal 1 13636, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19438 : bv 32 := 0x02043823.
Lemma F_19438 : fetch_word Plain.M.loaded_segments (0x19490 : word) = Some W_19438.
Proof. vm_refl. Qed.
Lemma D_19438 : decode_any W_19438 = Some (Store SZ8 8 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1943c : bv 32 := 0x00040513.
Lemma F_1943c : fetch_word Plain.M.loaded_segments (0x19494 : word) = Some W_1943c.
Proof. vm_refl. Qed.
Lemma D_1943c : decode_any W_1943c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19440 : bv 32 := 0x374160ef.
Lemma F_19440 : fetch_word Plain.M.loaded_segments (0x19498 : word) = Some W_19440.
Proof. vm_refl. Qed.
Lemma D_19440 : decode_any W_19440 = Some (Jal 1 90996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19444 : bv 32 := 0x00048513.
Lemma F_19444 : fetch_word Plain.M.loaded_segments (0x1949c : word) = Some W_19444.
Proof. vm_refl. Qed.
Lemma D_19444 : decode_any W_19444 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19448 : bv 32 := 0x00053023.
Lemma F_19448 : fetch_word Plain.M.loaded_segments (0x194a0 : word) = Some W_19448.
Proof. vm_refl. Qed.
Lemma D_19448 : decode_any W_19448 = Some (Store SZ8 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1944c : bv 32 := 0x03c0006f.
Lemma F_1944c : fetch_word Plain.M.loaded_segments (0x194a4 : word) = Some W_1944c.
Proof. vm_refl. Qed.
Lemma D_1944c : decode_any W_1944c = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19488 : bv 32 := 0x01813083.
Lemma F_19488 : fetch_word Plain.M.loaded_segments (0x194e0 : word) = Some W_19488.
Proof. vm_refl. Qed.
Lemma D_19488 : decode_any W_19488 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1948c : bv 32 := 0x01013403.
Lemma F_1948c : fetch_word Plain.M.loaded_segments (0x194e4 : word) = Some W_1948c.
Proof. vm_refl. Qed.
Lemma D_1948c : decode_any W_1948c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19490 : bv 32 := 0x00813483.
Lemma F_19490 : fetch_word Plain.M.loaded_segments (0x194e8 : word) = Some W_19490.
Proof. vm_refl. Qed.
Lemma D_19490 : decode_any W_19490 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19494 : bv 32 := 0x02010113.
Lemma F_19494 : fetch_word Plain.M.loaded_segments (0x194ec : word) = Some W_19494.
Proof. vm_refl. Qed.
Lemma D_19494 : decode_any W_19494 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19498 : bv 32 := 0x00008067.
Lemma F_19498 : fetch_word Plain.M.loaded_segments (0x194f0 : word) = Some W_19498.
Proof. vm_refl. Qed.
Lemma D_19498 : decode_any W_19498 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
