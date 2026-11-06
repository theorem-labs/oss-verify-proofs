(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_8d3f8 : bv 32 := 0x00155593.
Lemma F_8d3f8 : fetch_word Asan.M.loaded_segments (0x8d448 : word) = Some W_8d3f8.
Proof. vm_refl. Qed.
Lemma D_8d3f8 : decode_any W_8d3f8 = Some (ShiftImm ALU_SRL 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d3fc : bv 32 := 0x55555637.
Lemma F_8d3fc : fetch_word Asan.M.loaded_segments (0x8d44c : word) = Some W_8d3fc.
Proof. vm_refl. Qed.
Lemma D_8d3fc : decode_any W_8d3fc = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d400 : bv 32 := 0x333336b7.
Lemma F_8d400 : fetch_word Asan.M.loaded_segments (0x8d450 : word) = Some W_8d400.
Proof. vm_refl. Qed.
Lemma D_8d400 : decode_any W_8d400 = Some (Lui 13 209715, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d404 : bv 32 := 0x0f0f1737.
Lemma F_8d404 : fetch_word Asan.M.loaded_segments (0x8d454 : word) = Some W_8d404.
Proof. vm_refl. Qed.
Lemma D_8d404 : decode_any W_8d404 = Some (Lui 14 61681, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d408 : bv 32 := 0x010107b7.
Lemma F_8d408 : fetch_word Asan.M.loaded_segments (0x8d458 : word) = Some W_8d408.
Proof. vm_refl. Qed.
Lemma D_8d408 : decode_any W_8d408 = Some (Lui 15 4112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d40c : bv 32 := 0x00b56533.
Lemma F_8d40c : fetch_word Asan.M.loaded_segments (0x8d45c : word) = Some W_8d40c.
Proof. vm_refl. Qed.
Lemma D_8d40c : decode_any W_8d40c = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d410 : bv 32 := 0x5556059b.
Lemma F_8d410 : fetch_word Asan.M.loaded_segments (0x8d460 : word) = Some W_8d410.
Proof. vm_refl. Qed.
Lemma D_8d410 : decode_any W_8d410 = Some (OpImm32 11 12 1365, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d414 : bv 32 := 0x3336861b.
Lemma F_8d414 : fetch_word Asan.M.loaded_segments (0x8d464 : word) = Some W_8d414.
Proof. vm_refl. Qed.
Lemma D_8d414 : decode_any W_8d414 = Some (OpImm32 12 13 819, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d418 : bv 32 := 0xf0f7069b.
Lemma F_8d418 : fetch_word Asan.M.loaded_segments (0x8d468 : word) = Some W_8d418.
Proof. vm_refl. Qed.
Lemma D_8d418 : decode_any W_8d418 = Some (OpImm32 13 14 3855, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d41c : bv 32 := 0x1017871b.
Lemma F_8d41c : fetch_word Asan.M.loaded_segments (0x8d46c : word) = Some W_8d41c.
Proof. vm_refl. Qed.
Lemma D_8d41c : decode_any W_8d41c = Some (OpImm32 14 15 257, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d420 : bv 32 := 0x00255793.
Lemma F_8d420 : fetch_word Asan.M.loaded_segments (0x8d470 : word) = Some W_8d420.
Proof. vm_refl. Qed.
Lemma D_8d420 : decode_any W_8d420 = Some (ShiftImm ALU_SRL 15 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d424 : bv 32 := 0x00f56533.
Lemma F_8d424 : fetch_word Asan.M.loaded_segments (0x8d474 : word) = Some W_8d424.
Proof. vm_refl. Qed.
Lemma D_8d424 : decode_any W_8d424 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d428 : bv 32 := 0x02059793.
Lemma F_8d428 : fetch_word Asan.M.loaded_segments (0x8d478 : word) = Some W_8d428.
Proof. vm_refl. Qed.
Lemma D_8d428 : decode_any W_8d428 = Some (ShiftImm ALU_SLL 15 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d42c : bv 32 := 0x00f585b3.
Lemma F_8d42c : fetch_word Asan.M.loaded_segments (0x8d47c : word) = Some W_8d42c.
Proof. vm_refl. Qed.
Lemma D_8d42c : decode_any W_8d42c = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d430 : bv 32 := 0x02061793.
Lemma F_8d430 : fetch_word Asan.M.loaded_segments (0x8d480 : word) = Some W_8d430.
Proof. vm_refl. Qed.
Lemma D_8d430 : decode_any W_8d430 = Some (ShiftImm ALU_SLL 15 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d434 : bv 32 := 0x00f60633.
Lemma F_8d434 : fetch_word Asan.M.loaded_segments (0x8d484 : word) = Some W_8d434.
Proof. vm_refl. Qed.
Lemma D_8d434 : decode_any W_8d434 = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d438 : bv 32 := 0x02069793.
Lemma F_8d438 : fetch_word Asan.M.loaded_segments (0x8d488 : word) = Some W_8d438.
Proof. vm_refl. Qed.
Lemma D_8d438 : decode_any W_8d438 = Some (ShiftImm ALU_SLL 15 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d43c : bv 32 := 0x00f686b3.
Lemma F_8d43c : fetch_word Asan.M.loaded_segments (0x8d48c : word) = Some W_8d43c.
Proof. vm_refl. Qed.
Lemma D_8d43c : decode_any W_8d43c = Some (Op ALU_ADD 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d440 : bv 32 := 0x02071793.
Lemma F_8d440 : fetch_word Asan.M.loaded_segments (0x8d490 : word) = Some W_8d440.
Proof. vm_refl. Qed.
Lemma D_8d440 : decode_any W_8d440 = Some (ShiftImm ALU_SLL 15 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d444 : bv 32 := 0x00f70733.
Lemma F_8d444 : fetch_word Asan.M.loaded_segments (0x8d494 : word) = Some W_8d444.
Proof. vm_refl. Qed.
Lemma D_8d444 : decode_any W_8d444 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d448 : bv 32 := 0x00455793.
Lemma F_8d448 : fetch_word Asan.M.loaded_segments (0x8d498 : word) = Some W_8d448.
Proof. vm_refl. Qed.
Lemma D_8d448 : decode_any W_8d448 = Some (ShiftImm ALU_SRL 15 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d44c : bv 32 := 0x00f56533.
Lemma F_8d44c : fetch_word Asan.M.loaded_segments (0x8d49c : word) = Some W_8d44c.
Proof. vm_refl. Qed.
Lemma D_8d44c : decode_any W_8d44c = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d450 : bv 32 := 0x00855793.
Lemma F_8d450 : fetch_word Asan.M.loaded_segments (0x8d4a0 : word) = Some W_8d450.
Proof. vm_refl. Qed.
Lemma D_8d450 : decode_any W_8d450 = Some (ShiftImm ALU_SRL 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d454 : bv 32 := 0x00f56533.
Lemma F_8d454 : fetch_word Asan.M.loaded_segments (0x8d4a4 : word) = Some W_8d454.
Proof. vm_refl. Qed.
Lemma D_8d454 : decode_any W_8d454 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d458 : bv 32 := 0x01055793.
Lemma F_8d458 : fetch_word Asan.M.loaded_segments (0x8d4a8 : word) = Some W_8d458.
Proof. vm_refl. Qed.
Lemma D_8d458 : decode_any W_8d458 = Some (ShiftImm ALU_SRL 15 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d45c : bv 32 := 0x00f56533.
Lemma F_8d45c : fetch_word Asan.M.loaded_segments (0x8d4ac : word) = Some W_8d45c.
Proof. vm_refl. Qed.
Lemma D_8d45c : decode_any W_8d45c = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d460 : bv 32 := 0x02055793.
Lemma F_8d460 : fetch_word Asan.M.loaded_segments (0x8d4b0 : word) = Some W_8d460.
Proof. vm_refl. Qed.
Lemma D_8d460 : decode_any W_8d460 = Some (ShiftImm ALU_SRL 15 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d464 : bv 32 := 0x00f56533.
Lemma F_8d464 : fetch_word Asan.M.loaded_segments (0x8d4b4 : word) = Some W_8d464.
Proof. vm_refl. Qed.
Lemma D_8d464 : decode_any W_8d464 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d468 : bv 32 := 0xfff54513.
Lemma F_8d468 : fetch_word Asan.M.loaded_segments (0x8d4b8 : word) = Some W_8d468.
Proof. vm_refl. Qed.
Lemma D_8d468 : decode_any W_8d468 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d46c : bv 32 := 0x00155793.
Lemma F_8d46c : fetch_word Asan.M.loaded_segments (0x8d4bc : word) = Some W_8d46c.
Proof. vm_refl. Qed.
Lemma D_8d46c : decode_any W_8d46c = Some (ShiftImm ALU_SRL 15 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d470 : bv 32 := 0x00b7f5b3.
Lemma F_8d470 : fetch_word Asan.M.loaded_segments (0x8d4c0 : word) = Some W_8d470.
Proof. vm_refl. Qed.
Lemma D_8d470 : decode_any W_8d470 = Some (Op ALU_AND 11 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d474 : bv 32 := 0x40b50533.
Lemma F_8d474 : fetch_word Asan.M.loaded_segments (0x8d4c4 : word) = Some W_8d474.
Proof. vm_refl. Qed.
Lemma D_8d474 : decode_any W_8d474 = Some (Op ALU_SUB 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d478 : bv 32 := 0x00c575b3.
Lemma F_8d478 : fetch_word Asan.M.loaded_segments (0x8d4c8 : word) = Some W_8d478.
Proof. vm_refl. Qed.
Lemma D_8d478 : decode_any W_8d478 = Some (Op ALU_AND 11 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d47c : bv 32 := 0x00255513.
Lemma F_8d47c : fetch_word Asan.M.loaded_segments (0x8d4cc : word) = Some W_8d47c.
Proof. vm_refl. Qed.
Lemma D_8d47c : decode_any W_8d47c = Some (ShiftImm ALU_SRL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d480 : bv 32 := 0x00c57533.
Lemma F_8d480 : fetch_word Asan.M.loaded_segments (0x8d4d0 : word) = Some W_8d480.
Proof. vm_refl. Qed.
Lemma D_8d480 : decode_any W_8d480 = Some (Op ALU_AND 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d484 : bv 32 := 0x00a58533.
Lemma F_8d484 : fetch_word Asan.M.loaded_segments (0x8d4d4 : word) = Some W_8d484.
Proof. vm_refl. Qed.
Lemma D_8d484 : decode_any W_8d484 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d488 : bv 32 := 0x00455593.
Lemma F_8d488 : fetch_word Asan.M.loaded_segments (0x8d4d8 : word) = Some W_8d488.
Proof. vm_refl. Qed.
Lemma D_8d488 : decode_any W_8d488 = Some (ShiftImm ALU_SRL 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d48c : bv 32 := 0x00b50533.
Lemma F_8d48c : fetch_word Asan.M.loaded_segments (0x8d4dc : word) = Some W_8d48c.
Proof. vm_refl. Qed.
Lemma D_8d48c : decode_any W_8d48c = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d490 : bv 32 := 0x00d57533.
Lemma F_8d490 : fetch_word Asan.M.loaded_segments (0x8d4e0 : word) = Some W_8d490.
Proof. vm_refl. Qed.
Lemma D_8d490 : decode_any W_8d490 = Some (Op ALU_AND 10 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d494 : bv 32 := 0x02e50533.
Lemma F_8d494 : fetch_word Asan.M.loaded_segments (0x8d4e4 : word) = Some W_8d494.
Proof. vm_refl. Qed.
Lemma D_8d494 : decode_any W_8d494 = Some (Mul M_MUL 10 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d498 : bv 32 := 0x03855513.
Lemma F_8d498 : fetch_word Asan.M.loaded_segments (0x8d4e8 : word) = Some W_8d498.
Proof. vm_refl. Qed.
Lemma D_8d498 : decode_any W_8d498 = Some (ShiftImm ALU_SRL 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d49c : bv 32 := 0x40a0053b.
Lemma F_8d49c : fetch_word Asan.M.loaded_segments (0x8d4ec : word) = Some W_8d49c.
Proof. vm_refl. Qed.
Lemma D_8d49c : decode_any W_8d49c = Some (Op32 ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d4a0 : bv 32 := 0xfff00593.
Lemma F_8d4a0 : fetch_word Asan.M.loaded_segments (0x8d4f0 : word) = Some W_8d4a0.
Proof. vm_refl. Qed.
Lemma D_8d4a0 : decode_any W_8d4a0 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d4a4 : bv 32 := 0x00a59533.
Lemma F_8d4a4 : fetch_word Asan.M.loaded_segments (0x8d4f4 : word) = Some W_8d4a4.
Proof. vm_refl. Qed.
Lemma D_8d4a4 : decode_any W_8d4a4 = Some (Op ALU_SLL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d4a8 : bv 32 := 0xfff54513.
Lemma F_8d4a8 : fetch_word Asan.M.loaded_segments (0x8d4f8 : word) = Some W_8d4a8.
Proof. vm_refl. Qed.
Lemma D_8d4a8 : decode_any W_8d4a8 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.
