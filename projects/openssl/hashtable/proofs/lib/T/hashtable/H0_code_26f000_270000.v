(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.openssl.hashtable.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_26f448 : bv 32 := 0xff010113.
Lemma F_26f448 : fetch_word Plain.M.loaded_segments (0x26f48c : word) = Some W_26f448.
Proof. vm_refl. Qed.
Lemma D_26f448 : decode_any W_26f448 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f44c : bv 32 := 0x00113423.
Lemma F_26f44c : fetch_word Plain.M.loaded_segments (0x26f490 : word) = Some W_26f44c.
Proof. vm_refl. Qed.
Lemma D_26f44c : decode_any W_26f44c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f450 : bv 32 := 0x00813023.
Lemma F_26f450 : fetch_word Plain.M.loaded_segments (0x26f494 : word) = Some W_26f450.
Proof. vm_refl. Qed.
Lemma D_26f450 : decode_any W_26f450 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f454 : bv 32 := 0x741000ef.
Lemma F_26f454 : fetch_word Plain.M.loaded_segments (0x26f498 : word) = Some W_26f454.
Proof. vm_refl. Qed.
Lemma D_26f454 : decode_any W_26f454 = Some (Jal 1 3904, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f458 : bv 32 := 0x00053403.
Lemma F_26f458 : fetch_word Plain.M.loaded_segments (0x26f49c : word) = Some W_26f458.
Proof. vm_refl. Qed.
Lemma D_26f458 : decode_any W_26f458 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f45c : bv 32 := 0x12041663.
Lemma F_26f45c : fetch_word Plain.M.loaded_segments (0x26f4a0 : word) = Some W_26f45c.
Proof. vm_refl. Qed.
Lemma D_26f45c : decode_any W_26f45c = Some (Branch BC_NE 8 0 300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f460 : bv 32 := 0x0006a517.
Lemma F_26f460 : fetch_word Plain.M.loaded_segments (0x26f4a4 : word) = Some W_26f460.
Proof. vm_refl. Qed.
Lemma D_26f460 : decode_any W_26f460 = Some (Auipc 10 106, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f464 : bv 32 := 0xd7453403.
Lemma F_26f464 : fetch_word Plain.M.loaded_segments (0x26f4a8 : word) = Some W_26f464.
Proof. vm_refl. Qed.
Lemma D_26f464 : decode_any W_26f464 = Some (Load SZ8 true 8 10 3444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f468 : bv 32 := 0x04040a63.
Lemma F_26f468 : fetch_word Plain.M.loaded_segments (0x26f4ac : word) = Some W_26f468.
Proof. vm_refl. Qed.
Lemma D_26f468 : decode_any W_26f468 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f46c : bv 32 := 0x08c42503.
Lemma F_26f46c : fetch_word Plain.M.loaded_segments (0x26f4b0 : word) = Some W_26f46c.
Proof. vm_refl. Qed.
Lemma D_26f46c : decode_any W_26f46c = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f470 : bv 32 := 0x00054663.
Lemma F_26f470 : fetch_word Plain.M.loaded_segments (0x26f4b4 : word) = Some W_26f470.
Proof. vm_refl. Qed.
Lemma D_26f470 : decode_any W_26f470 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f474 : bv 32 := 0x00040513.
Lemma F_26f474 : fetch_word Plain.M.loaded_segments (0x26f4b8 : word) = Some W_26f474.
Proof. vm_refl. Qed.
Lemma D_26f474 : decode_any W_26f474 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f478 : bv 32 := 0x9d1ff0ef.
Lemma F_26f478 : fetch_word Plain.M.loaded_segments (0x26f4bc : word) = Some W_26f478.
Proof. vm_refl. Qed.
Lemma D_26f478 : decode_any W_26f478 = Some (Jal 1 2095568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f47c : bv 32 := 0x02843503.
Lemma F_26f47c : fetch_word Plain.M.loaded_segments (0x26f4c0 : word) = Some W_26f47c.
Proof. vm_refl. Qed.
Lemma D_26f47c : decode_any W_26f47c = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f480 : bv 32 := 0x03843583.
Lemma F_26f480 : fetch_word Plain.M.loaded_segments (0x26f4c4 : word) = Some W_26f480.
Proof. vm_refl. Qed.
Lemma D_26f480 : decode_any W_26f480 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f484 : bv 32 := 0x00b50c63.
Lemma F_26f484 : fetch_word Plain.M.loaded_segments (0x26f4c8 : word) = Some W_26f484.
Proof. vm_refl. Qed.
Lemma D_26f484 : decode_any W_26f484 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f488 : bv 32 := 0x04843683.
Lemma F_26f488 : fetch_word Plain.M.loaded_segments (0x26f4cc : word) = Some W_26f488.
Proof. vm_refl. Qed.
Lemma D_26f488 : decode_any W_26f488 = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f48c : bv 32 := 0x00040513.
Lemma F_26f48c : fetch_word Plain.M.loaded_segments (0x26f4d0 : word) = Some W_26f48c.
Proof. vm_refl. Qed.
Lemma D_26f48c : decode_any W_26f48c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f490 : bv 32 := 0x00000593.
Lemma F_26f490 : fetch_word Plain.M.loaded_segments (0x26f4d4 : word) = Some W_26f490.
Proof. vm_refl. Qed.
Lemma D_26f490 : decode_any W_26f490 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f494 : bv 32 := 0x00000613.
Lemma F_26f494 : fetch_word Plain.M.loaded_segments (0x26f4d8 : word) = Some W_26f494.
Proof. vm_refl. Qed.
Lemma D_26f494 : decode_any W_26f494 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f498 : bv 32 := 0x000680e7.
Lemma F_26f498 : fetch_word Plain.M.loaded_segments (0x26f4dc : word) = Some W_26f498.
Proof. vm_refl. Qed.
Lemma D_26f498 : decode_any W_26f498 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f49c : bv 32 := 0x00843503.
Lemma F_26f49c : fetch_word Plain.M.loaded_segments (0x26f4e0 : word) = Some W_26f49c.
Proof. vm_refl. Qed.
Lemma D_26f49c : decode_any W_26f49c = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f4a0 : bv 32 := 0x01043583.
Lemma F_26f4a0 : fetch_word Plain.M.loaded_segments (0x26f4e4 : word) = Some W_26f4a0.
Proof. vm_refl. Qed.
Lemma D_26f4a0 : decode_any W_26f4a0 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f4a4 : bv 32 := 0x00b50c63.
Lemma F_26f4a4 : fetch_word Plain.M.loaded_segments (0x26f4e8 : word) = Some W_26f4a4.
Proof. vm_refl. Qed.
Lemma D_26f4a4 : decode_any W_26f4a4 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f4a8 : bv 32 := 0x05043683.
Lemma F_26f4a8 : fetch_word Plain.M.loaded_segments (0x26f4ec : word) = Some W_26f4a8.
Proof. vm_refl. Qed.
Lemma D_26f4a8 : decode_any W_26f4a8 = Some (Load SZ8 true 13 8 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f4ac : bv 32 := 0x40b505b3.
Lemma F_26f4ac : fetch_word Plain.M.loaded_segments (0x26f4f0 : word) = Some W_26f4ac.
Proof. vm_refl. Qed.
Lemma D_26f4ac : decode_any W_26f4ac = Some (Op ALU_SUB 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f4b0 : bv 32 := 0x00100613.
Lemma F_26f4b0 : fetch_word Plain.M.loaded_segments (0x26f4f4 : word) = Some W_26f4b0.
Proof. vm_refl. Qed.
Lemma D_26f4b0 : decode_any W_26f4b0 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f4b4 : bv 32 := 0x00040513.
Lemma F_26f4b4 : fetch_word Plain.M.loaded_segments (0x26f4f8 : word) = Some W_26f4b4.
Proof. vm_refl. Qed.
Lemma D_26f4b4 : decode_any W_26f4b4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f4b8 : bv 32 := 0x000680e7.
Lemma F_26f4b8 : fetch_word Plain.M.loaded_segments (0x26f4fc : word) = Some W_26f4b8.
Proof. vm_refl. Qed.
Lemma D_26f4b8 : decode_any W_26f4b8 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f4bc : bv 32 := 0x0006a517.
Lemma F_26f4bc : fetch_word Plain.M.loaded_segments (0x26f500 : word) = Some W_26f4bc.
Proof. vm_refl. Qed.
Lemma D_26f4bc : decode_any W_26f4bc = Some (Auipc 10 106, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f4c0 : bv 32 := 0xe0853403.
Lemma F_26f4c0 : fetch_word Plain.M.loaded_segments (0x26f504 : word) = Some W_26f4c0.
Proof. vm_refl. Qed.
Lemma D_26f4c0 : decode_any W_26f4c0 = Some (Load SZ8 true 8 10 3592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f4c4 : bv 32 := 0x04040a63.
Lemma F_26f4c4 : fetch_word Plain.M.loaded_segments (0x26f508 : word) = Some W_26f4c4.
Proof. vm_refl. Qed.
Lemma D_26f4c4 : decode_any W_26f4c4 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f4c8 : bv 32 := 0x08c42503.
Lemma F_26f4c8 : fetch_word Plain.M.loaded_segments (0x26f50c : word) = Some W_26f4c8.
Proof. vm_refl. Qed.
Lemma D_26f4c8 : decode_any W_26f4c8 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f4cc : bv 32 := 0x00054663.
Lemma F_26f4cc : fetch_word Plain.M.loaded_segments (0x26f510 : word) = Some W_26f4cc.
Proof. vm_refl. Qed.
Lemma D_26f4cc : decode_any W_26f4cc = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f4d0 : bv 32 := 0x00040513.
Lemma F_26f4d0 : fetch_word Plain.M.loaded_segments (0x26f514 : word) = Some W_26f4d0.
Proof. vm_refl. Qed.
Lemma D_26f4d0 : decode_any W_26f4d0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f4d4 : bv 32 := 0x975ff0ef.
Lemma F_26f4d4 : fetch_word Plain.M.loaded_segments (0x26f518 : word) = Some W_26f4d4.
Proof. vm_refl. Qed.
Lemma D_26f4d4 : decode_any W_26f4d4 = Some (Jal 1 2095476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f4d8 : bv 32 := 0x02843503.
Lemma F_26f4d8 : fetch_word Plain.M.loaded_segments (0x26f51c : word) = Some W_26f4d8.
Proof. vm_refl. Qed.
Lemma D_26f4d8 : decode_any W_26f4d8 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f4dc : bv 32 := 0x03843583.
Lemma F_26f4dc : fetch_word Plain.M.loaded_segments (0x26f520 : word) = Some W_26f4dc.
Proof. vm_refl. Qed.
Lemma D_26f4dc : decode_any W_26f4dc = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f4e0 : bv 32 := 0x00b50c63.
Lemma F_26f4e0 : fetch_word Plain.M.loaded_segments (0x26f524 : word) = Some W_26f4e0.
Proof. vm_refl. Qed.
Lemma D_26f4e0 : decode_any W_26f4e0 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f4e4 : bv 32 := 0x04843683.
Lemma F_26f4e4 : fetch_word Plain.M.loaded_segments (0x26f528 : word) = Some W_26f4e4.
Proof. vm_refl. Qed.
Lemma D_26f4e4 : decode_any W_26f4e4 = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f4e8 : bv 32 := 0x00040513.
Lemma F_26f4e8 : fetch_word Plain.M.loaded_segments (0x26f52c : word) = Some W_26f4e8.
Proof. vm_refl. Qed.
Lemma D_26f4e8 : decode_any W_26f4e8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f4ec : bv 32 := 0x00000593.
Lemma F_26f4ec : fetch_word Plain.M.loaded_segments (0x26f530 : word) = Some W_26f4ec.
Proof. vm_refl. Qed.
Lemma D_26f4ec : decode_any W_26f4ec = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f4f0 : bv 32 := 0x00000613.
Lemma F_26f4f0 : fetch_word Plain.M.loaded_segments (0x26f534 : word) = Some W_26f4f0.
Proof. vm_refl. Qed.
Lemma D_26f4f0 : decode_any W_26f4f0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f4f4 : bv 32 := 0x000680e7.
Lemma F_26f4f4 : fetch_word Plain.M.loaded_segments (0x26f538 : word) = Some W_26f4f4.
Proof. vm_refl. Qed.
Lemma D_26f4f4 : decode_any W_26f4f4 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f4f8 : bv 32 := 0x00843503.
Lemma F_26f4f8 : fetch_word Plain.M.loaded_segments (0x26f53c : word) = Some W_26f4f8.
Proof. vm_refl. Qed.
Lemma D_26f4f8 : decode_any W_26f4f8 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f4fc : bv 32 := 0x01043583.
Lemma F_26f4fc : fetch_word Plain.M.loaded_segments (0x26f540 : word) = Some W_26f4fc.
Proof. vm_refl. Qed.
Lemma D_26f4fc : decode_any W_26f4fc = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f500 : bv 32 := 0x00b50c63.
Lemma F_26f500 : fetch_word Plain.M.loaded_segments (0x26f544 : word) = Some W_26f500.
Proof. vm_refl. Qed.
Lemma D_26f500 : decode_any W_26f500 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f504 : bv 32 := 0x05043683.
Lemma F_26f504 : fetch_word Plain.M.loaded_segments (0x26f548 : word) = Some W_26f504.
Proof. vm_refl. Qed.
Lemma D_26f504 : decode_any W_26f504 = Some (Load SZ8 true 13 8 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f508 : bv 32 := 0x40b505b3.
Lemma F_26f508 : fetch_word Plain.M.loaded_segments (0x26f54c : word) = Some W_26f508.
Proof. vm_refl. Qed.
Lemma D_26f508 : decode_any W_26f508 = Some (Op ALU_SUB 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f50c : bv 32 := 0x00100613.
Lemma F_26f50c : fetch_word Plain.M.loaded_segments (0x26f550 : word) = Some W_26f50c.
Proof. vm_refl. Qed.
Lemma D_26f50c : decode_any W_26f50c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f510 : bv 32 := 0x00040513.
Lemma F_26f510 : fetch_word Plain.M.loaded_segments (0x26f554 : word) = Some W_26f510.
Proof. vm_refl. Qed.
Lemma D_26f510 : decode_any W_26f510 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f514 : bv 32 := 0x000680e7.
Lemma F_26f514 : fetch_word Plain.M.loaded_segments (0x26f558 : word) = Some W_26f514.
Proof. vm_refl. Qed.
Lemma D_26f514 : decode_any W_26f514 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f518 : bv 32 := 0x0006a517.
Lemma F_26f518 : fetch_word Plain.M.loaded_segments (0x26f55c : word) = Some W_26f518.
Proof. vm_refl. Qed.
Lemma D_26f518 : decode_any W_26f518 = Some (Auipc 10 106, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f51c : bv 32 := 0xbcc53403.
Lemma F_26f51c : fetch_word Plain.M.loaded_segments (0x26f560 : word) = Some W_26f51c.
Proof. vm_refl. Qed.
Lemma D_26f51c : decode_any W_26f51c = Some (Load SZ8 true 8 10 3020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f520 : bv 32 := 0x0a040e63.
Lemma F_26f520 : fetch_word Plain.M.loaded_segments (0x26f564 : word) = Some W_26f520.
Proof. vm_refl. Qed.
Lemma D_26f520 : decode_any W_26f520 = Some (Branch BC_EQ 8 0 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f524 : bv 32 := 0x08c42503.
Lemma F_26f524 : fetch_word Plain.M.loaded_segments (0x26f568 : word) = Some W_26f524.
Proof. vm_refl. Qed.
Lemma D_26f524 : decode_any W_26f524 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f528 : bv 32 := 0x00054663.
Lemma F_26f528 : fetch_word Plain.M.loaded_segments (0x26f56c : word) = Some W_26f528.
Proof. vm_refl. Qed.
Lemma D_26f528 : decode_any W_26f528 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f52c : bv 32 := 0x00040513.
Lemma F_26f52c : fetch_word Plain.M.loaded_segments (0x26f570 : word) = Some W_26f52c.
Proof. vm_refl. Qed.
Lemma D_26f52c : decode_any W_26f52c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f530 : bv 32 := 0x919ff0ef.
Lemma F_26f530 : fetch_word Plain.M.loaded_segments (0x26f574 : word) = Some W_26f530.
Proof. vm_refl. Qed.
Lemma D_26f530 : decode_any W_26f530 = Some (Jal 1 2095384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f534 : bv 32 := 0x02843503.
Lemma F_26f534 : fetch_word Plain.M.loaded_segments (0x26f578 : word) = Some W_26f534.
Proof. vm_refl. Qed.
Lemma D_26f534 : decode_any W_26f534 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f538 : bv 32 := 0x03843583.
Lemma F_26f538 : fetch_word Plain.M.loaded_segments (0x26f57c : word) = Some W_26f538.
Proof. vm_refl. Qed.
Lemma D_26f538 : decode_any W_26f538 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f53c : bv 32 := 0x00b50c63.
Lemma F_26f53c : fetch_word Plain.M.loaded_segments (0x26f580 : word) = Some W_26f53c.
Proof. vm_refl. Qed.
Lemma D_26f53c : decode_any W_26f53c = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f540 : bv 32 := 0x04843683.
Lemma F_26f540 : fetch_word Plain.M.loaded_segments (0x26f584 : word) = Some W_26f540.
Proof. vm_refl. Qed.
Lemma D_26f540 : decode_any W_26f540 = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f544 : bv 32 := 0x00040513.
Lemma F_26f544 : fetch_word Plain.M.loaded_segments (0x26f588 : word) = Some W_26f544.
Proof. vm_refl. Qed.
Lemma D_26f544 : decode_any W_26f544 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f548 : bv 32 := 0x00000593.
Lemma F_26f548 : fetch_word Plain.M.loaded_segments (0x26f58c : word) = Some W_26f548.
Proof. vm_refl. Qed.
Lemma D_26f548 : decode_any W_26f548 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f54c : bv 32 := 0x00000613.
Lemma F_26f54c : fetch_word Plain.M.loaded_segments (0x26f590 : word) = Some W_26f54c.
Proof. vm_refl. Qed.
Lemma D_26f54c : decode_any W_26f54c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f550 : bv 32 := 0x000680e7.
Lemma F_26f550 : fetch_word Plain.M.loaded_segments (0x26f594 : word) = Some W_26f550.
Proof. vm_refl. Qed.
Lemma D_26f550 : decode_any W_26f550 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f554 : bv 32 := 0x00843503.
Lemma F_26f554 : fetch_word Plain.M.loaded_segments (0x26f598 : word) = Some W_26f554.
Proof. vm_refl. Qed.
Lemma D_26f554 : decode_any W_26f554 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f558 : bv 32 := 0x01043583.
Lemma F_26f558 : fetch_word Plain.M.loaded_segments (0x26f59c : word) = Some W_26f558.
Proof. vm_refl. Qed.
Lemma D_26f558 : decode_any W_26f558 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f55c : bv 32 := 0x08b50063.
Lemma F_26f55c : fetch_word Plain.M.loaded_segments (0x26f5a0 : word) = Some W_26f55c.
Proof. vm_refl. Qed.
Lemma D_26f55c : decode_any W_26f55c = Some (Branch BC_EQ 10 11 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f560 : bv 32 := 0x05043303.
Lemma F_26f560 : fetch_word Plain.M.loaded_segments (0x26f5a4 : word) = Some W_26f560.
Proof. vm_refl. Qed.
Lemma D_26f560 : decode_any W_26f560 = Some (Load SZ8 true 6 8 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f564 : bv 32 := 0x40b505b3.
Lemma F_26f564 : fetch_word Plain.M.loaded_segments (0x26f5a8 : word) = Some W_26f564.
Proof. vm_refl. Qed.
Lemma D_26f564 : decode_any W_26f564 = Some (Op ALU_SUB 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f568 : bv 32 := 0x00100613.
Lemma F_26f568 : fetch_word Plain.M.loaded_segments (0x26f5ac : word) = Some W_26f568.
Proof. vm_refl. Qed.
Lemma D_26f568 : decode_any W_26f568 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f56c : bv 32 := 0x00040513.
Lemma F_26f56c : fetch_word Plain.M.loaded_segments (0x26f5b0 : word) = Some W_26f56c.
Proof. vm_refl. Qed.
Lemma D_26f56c : decode_any W_26f56c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f570 : bv 32 := 0x00813083.
Lemma F_26f570 : fetch_word Plain.M.loaded_segments (0x26f5b4 : word) = Some W_26f570.
Proof. vm_refl. Qed.
Lemma D_26f570 : decode_any W_26f570 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f574 : bv 32 := 0x00013403.
Lemma F_26f574 : fetch_word Plain.M.loaded_segments (0x26f5b8 : word) = Some W_26f574.
Proof. vm_refl. Qed.
Lemma D_26f574 : decode_any W_26f574 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f578 : bv 32 := 0x01010113.
Lemma F_26f578 : fetch_word Plain.M.loaded_segments (0x26f5bc : word) = Some W_26f578.
Proof. vm_refl. Qed.
Lemma D_26f578 : decode_any W_26f578 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f57c : bv 32 := 0x00030067.
Lemma F_26f57c : fetch_word Plain.M.loaded_segments (0x26f5c0 : word) = Some W_26f57c.
Proof. vm_refl. Qed.
Lemma D_26f57c : decode_any W_26f57c = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f580 : bv 32 := 0x07043403.
Lemma F_26f580 : fetch_word Plain.M.loaded_segments (0x26f5c4 : word) = Some W_26f580.
Proof. vm_refl. Qed.
Lemma D_26f580 : decode_any W_26f580 = Some (Load SZ8 true 8 8 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f584 : bv 32 := 0xec040ee3.
Lemma F_26f584 : fetch_word Plain.M.loaded_segments (0x26f5c8 : word) = Some W_26f584.
Proof. vm_refl. Qed.
Lemma D_26f584 : decode_any W_26f584 = Some (Branch BC_EQ 8 0 7900, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f588 : bv 32 := 0x08c42503.
Lemma F_26f588 : fetch_word Plain.M.loaded_segments (0x26f5cc : word) = Some W_26f588.
Proof. vm_refl. Qed.
Lemma D_26f588 : decode_any W_26f588 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f58c : bv 32 := 0x00054663.
Lemma F_26f58c : fetch_word Plain.M.loaded_segments (0x26f5d0 : word) = Some W_26f58c.
Proof. vm_refl. Qed.
Lemma D_26f58c : decode_any W_26f58c = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f590 : bv 32 := 0x00040513.
Lemma F_26f590 : fetch_word Plain.M.loaded_segments (0x26f5d4 : word) = Some W_26f590.
Proof. vm_refl. Qed.
Lemma D_26f590 : decode_any W_26f590 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f594 : bv 32 := 0x8b5ff0ef.
Lemma F_26f594 : fetch_word Plain.M.loaded_segments (0x26f5d8 : word) = Some W_26f594.
Proof. vm_refl. Qed.
Lemma D_26f594 : decode_any W_26f594 = Some (Jal 1 2095284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f598 : bv 32 := 0x02843503.
Lemma F_26f598 : fetch_word Plain.M.loaded_segments (0x26f5dc : word) = Some W_26f598.
Proof. vm_refl. Qed.
Lemma D_26f598 : decode_any W_26f598 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f59c : bv 32 := 0x03843583.
Lemma F_26f59c : fetch_word Plain.M.loaded_segments (0x26f5e0 : word) = Some W_26f59c.
Proof. vm_refl. Qed.
Lemma D_26f59c : decode_any W_26f59c = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f5a0 : bv 32 := 0x00b50c63.
Lemma F_26f5a0 : fetch_word Plain.M.loaded_segments (0x26f5e4 : word) = Some W_26f5a0.
Proof. vm_refl. Qed.
Lemma D_26f5a0 : decode_any W_26f5a0 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f5a4 : bv 32 := 0x04843683.
Lemma F_26f5a4 : fetch_word Plain.M.loaded_segments (0x26f5e8 : word) = Some W_26f5a4.
Proof. vm_refl. Qed.
Lemma D_26f5a4 : decode_any W_26f5a4 = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f5a8 : bv 32 := 0x00040513.
Lemma F_26f5a8 : fetch_word Plain.M.loaded_segments (0x26f5ec : word) = Some W_26f5a8.
Proof. vm_refl. Qed.
Lemma D_26f5a8 : decode_any W_26f5a8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f5ac : bv 32 := 0x00000593.
Lemma F_26f5ac : fetch_word Plain.M.loaded_segments (0x26f5f0 : word) = Some W_26f5ac.
Proof. vm_refl. Qed.
Lemma D_26f5ac : decode_any W_26f5ac = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f5b0 : bv 32 := 0x00000613.
Lemma F_26f5b0 : fetch_word Plain.M.loaded_segments (0x26f5f4 : word) = Some W_26f5b0.
Proof. vm_refl. Qed.
Lemma D_26f5b0 : decode_any W_26f5b0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f5b4 : bv 32 := 0x000680e7.
Lemma F_26f5b4 : fetch_word Plain.M.loaded_segments (0x26f5f8 : word) = Some W_26f5b4.
Proof. vm_refl. Qed.
Lemma D_26f5b4 : decode_any W_26f5b4 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f5b8 : bv 32 := 0x00843503.
Lemma F_26f5b8 : fetch_word Plain.M.loaded_segments (0x26f5fc : word) = Some W_26f5b8.
Proof. vm_refl. Qed.
Lemma D_26f5b8 : decode_any W_26f5b8 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f5bc : bv 32 := 0x01043583.
Lemma F_26f5bc : fetch_word Plain.M.loaded_segments (0x26f600 : word) = Some W_26f5bc.
Proof. vm_refl. Qed.
Lemma D_26f5bc : decode_any W_26f5bc = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f5c0 : bv 32 := 0xfcb500e3.
Lemma F_26f5c0 : fetch_word Plain.M.loaded_segments (0x26f604 : word) = Some W_26f5c0.
Proof. vm_refl. Qed.
Lemma D_26f5c0 : decode_any W_26f5c0 = Some (Branch BC_EQ 10 11 8128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f5c4 : bv 32 := 0x05043683.
Lemma F_26f5c4 : fetch_word Plain.M.loaded_segments (0x26f608 : word) = Some W_26f5c4.
Proof. vm_refl. Qed.
Lemma D_26f5c4 : decode_any W_26f5c4 = Some (Load SZ8 true 13 8 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f5c8 : bv 32 := 0x40b505b3.
Lemma F_26f5c8 : fetch_word Plain.M.loaded_segments (0x26f60c : word) = Some W_26f5c8.
Proof. vm_refl. Qed.
Lemma D_26f5c8 : decode_any W_26f5c8 = Some (Op ALU_SUB 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f5cc : bv 32 := 0x00100613.
Lemma F_26f5cc : fetch_word Plain.M.loaded_segments (0x26f610 : word) = Some W_26f5cc.
Proof. vm_refl. Qed.
Lemma D_26f5cc : decode_any W_26f5cc = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f5d0 : bv 32 := 0x00040513.
Lemma F_26f5d0 : fetch_word Plain.M.loaded_segments (0x26f614 : word) = Some W_26f5d0.
Proof. vm_refl. Qed.
Lemma D_26f5d0 : decode_any W_26f5d0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f5d4 : bv 32 := 0x000680e7.
Lemma F_26f5d4 : fetch_word Plain.M.loaded_segments (0x26f618 : word) = Some W_26f5d4.
Proof. vm_refl. Qed.
Lemma D_26f5d4 : decode_any W_26f5d4 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f5d8 : bv 32 := 0xfa9ff06f.
Lemma F_26f5d8 : fetch_word Plain.M.loaded_segments (0x26f61c : word) = Some W_26f5d8.
Proof. vm_refl. Qed.
Lemma D_26f5d8 : decode_any W_26f5d8 = Some (Jal 0 2097064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f5dc : bv 32 := 0x00813083.
Lemma F_26f5dc : fetch_word Plain.M.loaded_segments (0x26f620 : word) = Some W_26f5dc.
Proof. vm_refl. Qed.
Lemma D_26f5dc : decode_any W_26f5dc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f5e0 : bv 32 := 0x00013403.
Lemma F_26f5e0 : fetch_word Plain.M.loaded_segments (0x26f624 : word) = Some W_26f5e0.
Proof. vm_refl. Qed.
Lemma D_26f5e0 : decode_any W_26f5e0 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f5e4 : bv 32 := 0x01010113.
Lemma F_26f5e4 : fetch_word Plain.M.loaded_segments (0x26f628 : word) = Some W_26f5e4.
Proof. vm_refl. Qed.
Lemma D_26f5e4 : decode_any W_26f5e4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f5e8 : bv 32 := 0x00008067.
Lemma F_26f5e8 : fetch_word Plain.M.loaded_segments (0x26f62c : word) = Some W_26f5e8.
Proof. vm_refl. Qed.
Lemma D_26f5e8 : decode_any W_26f5e8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f9c0 : bv 32 := 0xf9010113.
Lemma F_26f9c0 : fetch_word Plain.M.loaded_segments (0x26fa04 : word) = Some W_26f9c0.
Proof. vm_refl. Qed.
Lemma D_26f9c0 : decode_any W_26f9c0 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f9c4 : bv 32 := 0x06113423.
Lemma F_26f9c4 : fetch_word Plain.M.loaded_segments (0x26fa08 : word) = Some W_26f9c4.
Proof. vm_refl. Qed.
Lemma D_26f9c4 : decode_any W_26f9c4 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f9c8 : bv 32 := 0x06813023.
Lemma F_26f9c8 : fetch_word Plain.M.loaded_segments (0x26fa0c : word) = Some W_26f9c8.
Proof. vm_refl. Qed.
Lemma D_26f9c8 : decode_any W_26f9c8 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f9cc : bv 32 := 0x04913c23.
Lemma F_26f9cc : fetch_word Plain.M.loaded_segments (0x26fa10 : word) = Some W_26f9cc.
Proof. vm_refl. Qed.
Lemma D_26f9cc : decode_any W_26f9cc = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f9d0 : bv 32 := 0x05213823.
Lemma F_26f9d0 : fetch_word Plain.M.loaded_segments (0x26fa14 : word) = Some W_26f9d0.
Proof. vm_refl. Qed.
Lemma D_26f9d0 : decode_any W_26f9d0 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f9d4 : bv 32 := 0x05313423.
Lemma F_26f9d4 : fetch_word Plain.M.loaded_segments (0x26fa18 : word) = Some W_26f9d4.
Proof. vm_refl. Qed.
Lemma D_26f9d4 : decode_any W_26f9d4 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f9d8 : bv 32 := 0x05413023.
Lemma F_26f9d8 : fetch_word Plain.M.loaded_segments (0x26fa1c : word) = Some W_26f9d8.
Proof. vm_refl. Qed.
Lemma D_26f9d8 : decode_any W_26f9d8 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f9dc : bv 32 := 0x03513c23.
Lemma F_26f9dc : fetch_word Plain.M.loaded_segments (0x26fa20 : word) = Some W_26f9dc.
Proof. vm_refl. Qed.
Lemma D_26f9dc : decode_any W_26f9dc = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f9e0 : bv 32 := 0x03613823.
Lemma F_26f9e0 : fetch_word Plain.M.loaded_segments (0x26fa24 : word) = Some W_26f9e0.
Proof. vm_refl. Qed.
Lemma D_26f9e0 : decode_any W_26f9e0 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f9e4 : bv 32 := 0x00060413.
Lemma F_26f9e4 : fetch_word Plain.M.loaded_segments (0x26fa28 : word) = Some W_26f9e4.
Proof. vm_refl. Qed.
Lemma D_26f9e4 : decode_any W_26f9e4 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f9e8 : bv 32 := 0x00050493.
Lemma F_26f9e8 : fetch_word Plain.M.loaded_segments (0x26fa2c : word) = Some W_26f9e8.
Proof. vm_refl. Qed.
Lemma D_26f9e8 : decode_any W_26f9e8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f9ec : bv 32 := 0x00068517.
Lemma F_26f9ec : fetch_word Plain.M.loaded_segments (0x26fa30 : word) = Some W_26f9ec.
Proof. vm_refl. Qed.
Lemma D_26f9ec : decode_any W_26f9ec = Some (Auipc 10 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f9f0 : bv 32 := 0x17053a83.
Lemma F_26f9f0 : fetch_word Plain.M.loaded_segments (0x26fa34 : word) = Some W_26f9f0.
Proof. vm_refl. Qed.
Lemma D_26f9f0 : decode_any W_26f9f0 = Some (Load SZ8 true 21 10 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f9f4 : bv 32 := 0x000ab503.
Lemma F_26f9f4 : fetch_word Plain.M.loaded_segments (0x26fa38 : word) = Some W_26f9f4.
Proof. vm_refl. Qed.
Lemma D_26f9f4 : decode_any W_26f9f4 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f9f8 : bv 32 := 0x02a13423.
Lemma F_26f9f8 : fetch_word Plain.M.loaded_segments (0x26fa3c : word) = Some W_26f9f8.
Proof. vm_refl. Qed.
Lemma D_26f9f8 : decode_any W_26f9f8 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f9fc : bv 32 := 0x0284b503.
Lemma F_26f9fc : fetch_word Plain.M.loaded_segments (0x26fa40 : word) = Some W_26f9fc.
Proof. vm_refl. Qed.
Lemma D_26f9fc : decode_any W_26f9fc = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa00 : bv 32 := 0x0384b603.
Lemma F_26fa00 : fetch_word Plain.M.loaded_segments (0x26fa44 : word) = Some W_26fa00.
Proof. vm_refl. Qed.
Lemma D_26fa00 : decode_any W_26fa00 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa04 : bv 32 := 0x40c50b33.
Lemma F_26fa04 : fetch_word Plain.M.loaded_segments (0x26fa48 : word) = Some W_26fa04.
Proof. vm_refl. Qed.
Lemma D_26fa04 : decode_any W_26fa04 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa08 : bv 32 := 0x00c546b3.
Lemma F_26fa08 : fetch_word Plain.M.loaded_segments (0x26fa4c : word) = Some W_26fa08.
Proof. vm_refl. Qed.
Lemma D_26fa08 : decode_any W_26fa08 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa0c : bv 32 := 0x00c13423.
Lemma F_26fa0c : fetch_word Plain.M.loaded_segments (0x26fa50 : word) = Some W_26fa0c.
Proof. vm_refl. Qed.
Lemma D_26fa0c : decode_any W_26fa0c = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa10 : bv 32 := 0x01613823.
Lemma F_26fa10 : fetch_word Plain.M.loaded_segments (0x26fa54 : word) = Some W_26fa10.
Proof. vm_refl. Qed.
Lemma D_26fa10 : decode_any W_26fa10 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa14 : bv 32 := 0x00b13c23.
Lemma F_26fa14 : fetch_word Plain.M.loaded_segments (0x26fa58 : word) = Some W_26fa14.
Proof. vm_refl. Qed.
Lemma D_26fa14 : decode_any W_26fa14 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa18 : bv 32 := 0x02813023.
Lemma F_26fa18 : fetch_word Plain.M.loaded_segments (0x26fa5c : word) = Some W_26fa18.
Proof. vm_refl. Qed.
Lemma D_26fa18 : decode_any W_26fa18 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa1c : bv 32 := 0x008b0b33.
Lemma F_26fa1c : fetch_word Plain.M.loaded_segments (0x26fa60 : word) = Some W_26fa1c.
Proof. vm_refl. Qed.
Lemma D_26fa1c : decode_any W_26fa1c = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa20 : bv 32 := 0x00d03933.
Lemma F_26fa20 : fetch_word Plain.M.loaded_segments (0x26fa64 : word) = Some W_26fa20.
Proof. vm_refl. Qed.
Lemma D_26fa20 : decode_any W_26fa20 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa24 : bv 32 := 0x00c50663.
Lemma F_26fa24 : fetch_word Plain.M.loaded_segments (0x26fa68 : word) = Some W_26fa24.
Proof. vm_refl. Qed.
Lemma D_26fa24 : decode_any W_26fa24 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa28 : bv 32 := 0x00810993.
Lemma F_26fa28 : fetch_word Plain.M.loaded_segments (0x26fa6c : word) = Some W_26fa28.
Proof. vm_refl. Qed.
Lemma D_26fa28 : decode_any W_26fa28 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa2c : bv 32 := 0x0080006f.
Lemma F_26fa2c : fetch_word Plain.M.loaded_segments (0x26fa70 : word) = Some W_26fa2c.
Proof. vm_refl. Qed.
Lemma D_26fa2c : decode_any W_26fa2c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa30 : bv 32 := 0x01810993.
Lemma F_26fa30 : fetch_word Plain.M.loaded_segments (0x26fa74 : word) = Some W_26fa30.
Proof. vm_refl. Qed.
Lemma D_26fa30 : decode_any W_26fa30 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa34 : bv 32 := 0x0784a503.
Lemma F_26fa34 : fetch_word Plain.M.loaded_segments (0x26fa78 : word) = Some W_26fa34.
Proof. vm_refl. Qed.
Lemma D_26fa34 : decode_any W_26fa34 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa38 : bv 32 := 0x00190913.
Lemma F_26fa38 : fetch_word Plain.M.loaded_segments (0x26fa7c : word) = Some W_26fa38.
Proof. vm_refl. Qed.
Lemma D_26fa38 : decode_any W_26fa38 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa3c : bv 32 := 0x04200893.
Lemma F_26fa3c : fetch_word Plain.M.loaded_segments (0x26fa80 : word) = Some W_26fa3c.
Proof. vm_refl. Qed.
Lemma D_26fa3c : decode_any W_26fa3c = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa40 : bv 32 := 0x00098593.
Lemma F_26fa40 : fetch_word Plain.M.loaded_segments (0x26fa84 : word) = Some W_26fa40.
Proof. vm_refl. Qed.
Lemma D_26fa40 : decode_any W_26fa40 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa44 : bv 32 := 0x00090613.
Lemma F_26fa44 : fetch_word Plain.M.loaded_segments (0x26fa88 : word) = Some W_26fa44.
Proof. vm_refl. Qed.
Lemma D_26fa44 : decode_any W_26fa44 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa48 : bv 32 := 0x00000073.
Lemma F_26fa48 : fetch_word Plain.M.loaded_segments (0x26fa8c : word) = Some W_26fa48.
Proof. vm_refl. Qed.
Lemma D_26fa48 : decode_any W_26fa48 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_26fa48 : is_ecall W_26fa48 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26fa4c : bv 32 := 0xb0cfc0ef.
Lemma F_26fa4c : fetch_word Plain.M.loaded_segments (0x26fa90 : word) = Some W_26fa4c.
Proof. vm_refl. Qed.
Lemma D_26fa4c : decode_any W_26fa4c = Some (Jal 1 2081548, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa50 : bv 32 := 0x09651863.
Lemma F_26fa50 : fetch_word Plain.M.loaded_segments (0x26fa94 : word) = Some W_26fa50.
Proof. vm_refl. Qed.
Lemma D_26fa50 : decode_any W_26fa50 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa54 : bv 32 := 0x0584b503.
Lemma F_26fa54 : fetch_word Plain.M.loaded_segments (0x26fa98 : word) = Some W_26fa54.
Proof. vm_refl. Qed.
Lemma D_26fa54 : decode_any W_26fa54 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa58 : bv 32 := 0x0604b583.
Lemma F_26fa58 : fetch_word Plain.M.loaded_segments (0x26fa9c : word) = Some W_26fa58.
Proof. vm_refl. Qed.
Lemma D_26fa58 : decode_any W_26fa58 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa5c : bv 32 := 0x00b505b3.
Lemma F_26fa5c : fetch_word Plain.M.loaded_segments (0x26faa0 : word) = Some W_26fa5c.
Proof. vm_refl. Qed.
Lemma D_26fa5c : decode_any W_26fa5c = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa60 : bv 32 := 0x02b4b023.
Lemma F_26fa60 : fetch_word Plain.M.loaded_segments (0x26faa4 : word) = Some W_26fa60.
Proof. vm_refl. Qed.
Lemma D_26fa60 : decode_any W_26fa60 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa64 : bv 32 := 0x02a4b423.
Lemma F_26fa64 : fetch_word Plain.M.loaded_segments (0x26faa8 : word) = Some W_26fa64.
Proof. vm_refl. Qed.
Lemma D_26fa64 : decode_any W_26fa64 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa68 : bv 32 := 0x02a4bc23.
Lemma F_26fa68 : fetch_word Plain.M.loaded_segments (0x26faac : word) = Some W_26fa68.
Proof. vm_refl. Qed.
Lemma D_26fa68 : decode_any W_26fa68 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa6c : bv 32 := 0x00040513.
Lemma F_26fa6c : fetch_word Plain.M.loaded_segments (0x26fab0 : word) = Some W_26fa6c.
Proof. vm_refl. Qed.
Lemma D_26fa6c : decode_any W_26fa6c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa70 : bv 32 := 0x000ab583.
Lemma F_26fa70 : fetch_word Plain.M.loaded_segments (0x26fab4 : word) = Some W_26fa70.
Proof. vm_refl. Qed.
Lemma D_26fa70 : decode_any W_26fa70 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa74 : bv 32 := 0x02813603.
Lemma F_26fa74 : fetch_word Plain.M.loaded_segments (0x26fab8 : word) = Some W_26fa74.
Proof. vm_refl. Qed.
Lemma D_26fa74 : decode_any W_26fa74 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa78 : bv 32 := 0x0cc59a63.
Lemma F_26fa78 : fetch_word Plain.M.loaded_segments (0x26fabc : word) = Some W_26fa78.
Proof. vm_refl. Qed.
Lemma D_26fa78 : decode_any W_26fa78 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa7c : bv 32 := 0x06813083.
Lemma F_26fa7c : fetch_word Plain.M.loaded_segments (0x26fac0 : word) = Some W_26fa7c.
Proof. vm_refl. Qed.
Lemma D_26fa7c : decode_any W_26fa7c = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa80 : bv 32 := 0x06013403.
Lemma F_26fa80 : fetch_word Plain.M.loaded_segments (0x26fac4 : word) = Some W_26fa80.
Proof. vm_refl. Qed.
Lemma D_26fa80 : decode_any W_26fa80 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa84 : bv 32 := 0x05813483.
Lemma F_26fa84 : fetch_word Plain.M.loaded_segments (0x26fac8 : word) = Some W_26fa84.
Proof. vm_refl. Qed.
Lemma D_26fa84 : decode_any W_26fa84 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa88 : bv 32 := 0x05013903.
Lemma F_26fa88 : fetch_word Plain.M.loaded_segments (0x26facc : word) = Some W_26fa88.
Proof. vm_refl. Qed.
Lemma D_26fa88 : decode_any W_26fa88 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa8c : bv 32 := 0x04813983.
Lemma F_26fa8c : fetch_word Plain.M.loaded_segments (0x26fad0 : word) = Some W_26fa8c.
Proof. vm_refl. Qed.
Lemma D_26fa8c : decode_any W_26fa8c = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa90 : bv 32 := 0x04013a03.
Lemma F_26fa90 : fetch_word Plain.M.loaded_segments (0x26fad4 : word) = Some W_26fa90.
Proof. vm_refl. Qed.
Lemma D_26fa90 : decode_any W_26fa90 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa94 : bv 32 := 0x03813a83.
Lemma F_26fa94 : fetch_word Plain.M.loaded_segments (0x26fad8 : word) = Some W_26fa94.
Proof. vm_refl. Qed.
Lemma D_26fa94 : decode_any W_26fa94 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa98 : bv 32 := 0x03013b03.
Lemma F_26fa98 : fetch_word Plain.M.loaded_segments (0x26fadc : word) = Some W_26fa98.
Proof. vm_refl. Qed.
Lemma D_26fa98 : decode_any W_26fa98 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fa9c : bv 32 := 0x07010113.
Lemma F_26fa9c : fetch_word Plain.M.loaded_segments (0x26fae0 : word) = Some W_26fa9c.
Proof. vm_refl. Qed.
Lemma D_26fa9c : decode_any W_26fa9c = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26faa0 : bv 32 := 0x00008067.
Lemma F_26faa0 : fetch_word Plain.M.loaded_segments (0x26fae4 : word) = Some W_26faa0.
Proof. vm_refl. Qed.
Lemma D_26faa0 : decode_any W_26faa0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26faa4 : bv 32 := 0x00800713.
Lemma F_26faa4 : fetch_word Plain.M.loaded_segments (0x26fae8 : word) = Some W_26faa4.
Proof. vm_refl. Qed.
Lemma D_26faa4 : decode_any W_26faa4 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26faa8 : bv 32 := 0x000a0593.
Lemma F_26faa8 : fetch_word Plain.M.loaded_segments (0x26faec : word) = Some W_26faa8.
Proof. vm_refl. Qed.
Lemma D_26faa8 : decode_any W_26faa8 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26faac : bv 32 := 0x00e98733.
Lemma F_26faac : fetch_word Plain.M.loaded_segments (0x26faf0 : word) = Some W_26faac.
Proof. vm_refl. Qed.
Lemma D_26faac : decode_any W_26faac = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fab0 : bv 32 := 0x00073783.
Lemma F_26fab0 : fetch_word Plain.M.loaded_segments (0x26faf4 : word) = Some W_26fab0.
Proof. vm_refl. Qed.
Lemma D_26fab0 : decode_any W_26fab0 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fab4 : bv 32 := 0x40ab0b33.
Lemma F_26fab4 : fetch_word Plain.M.loaded_segments (0x26faf8 : word) = Some W_26fab4.
Proof. vm_refl. Qed.
Lemma D_26fab4 : decode_any W_26fab4 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fab8 : bv 32 := 0x0784a503.
Lemma F_26fab8 : fetch_word Plain.M.loaded_segments (0x26fafc : word) = Some W_26fab8.
Proof. vm_refl. Qed.
Lemma D_26fab8 : decode_any W_26fab8 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fabc : bv 32 := 0x40c9093b.
Lemma F_26fabc : fetch_word Plain.M.loaded_segments (0x26fb00 : word) = Some W_26fabc.
Proof. vm_refl. Qed.
Lemma D_26fabc : decode_any W_26fabc = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fac0 : bv 32 := 0x40d787b3.
Lemma F_26fac0 : fetch_word Plain.M.loaded_segments (0x26fb04 : word) = Some W_26fac0.
Proof. vm_refl. Qed.
Lemma D_26fac0 : decode_any W_26fac0 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fac4 : bv 32 := 0x00f73023.
Lemma F_26fac4 : fetch_word Plain.M.loaded_segments (0x26fb08 : word) = Some W_26fac4.
Proof. vm_refl. Qed.
Lemma D_26fac4 : decode_any W_26fac4 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fac8 : bv 32 := 0x04200893.
Lemma F_26fac8 : fetch_word Plain.M.loaded_segments (0x26fb0c : word) = Some W_26fac8.
Proof. vm_refl. Qed.
Lemma D_26fac8 : decode_any W_26fac8 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26facc : bv 32 := 0x00090613.
Lemma F_26facc : fetch_word Plain.M.loaded_segments (0x26fb10 : word) = Some W_26facc.
Proof. vm_refl. Qed.
Lemma D_26facc : decode_any W_26facc = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fad0 : bv 32 := 0x00000073.
Lemma F_26fad0 : fetch_word Plain.M.loaded_segments (0x26fb14 : word) = Some W_26fad0.
Proof. vm_refl. Qed.
Lemma D_26fad0 : decode_any W_26fad0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_26fad0 : is_ecall W_26fad0 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26fad4 : bv 32 := 0xa84fc0ef.
Lemma F_26fad4 : fetch_word Plain.M.loaded_segments (0x26fb18 : word) = Some W_26fad4.
Proof. vm_refl. Qed.
Lemma D_26fad4 : decode_any W_26fad4 = Some (Jal 1 2081412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fad8 : bv 32 := 0x000a0993.
Lemma F_26fad8 : fetch_word Plain.M.loaded_segments (0x26fb1c : word) = Some W_26fad8.
Proof. vm_refl. Qed.
Lemma D_26fad8 : decode_any W_26fad8 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fadc : bv 32 := 0xf7650ce3.
Lemma F_26fadc : fetch_word Plain.M.loaded_segments (0x26fb20 : word) = Some W_26fadc.
Proof. vm_refl. Qed.
Lemma D_26fadc : decode_any W_26fadc = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fae0 : bv 32 := 0x02054c63.
Lemma F_26fae0 : fetch_word Plain.M.loaded_segments (0x26fb24 : word) = Some W_26fae0.
Proof. vm_refl. Qed.
Lemma D_26fae0 : decode_any W_26fae0 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fae4 : bv 32 := 0x0089b583.
Lemma F_26fae4 : fetch_word Plain.M.loaded_segments (0x26fb28 : word) = Some W_26fae4.
Proof. vm_refl. Qed.
Lemma D_26fae4 : decode_any W_26fae4 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fae8 : bv 32 := 0x00a5b633.
Lemma F_26fae8 : fetch_word Plain.M.loaded_segments (0x26fb2c : word) = Some W_26fae8.
Proof. vm_refl. Qed.
Lemma D_26fae8 : decode_any W_26fae8 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26faec : bv 32 := 0x00461a13.
Lemma F_26faec : fetch_word Plain.M.loaded_segments (0x26fb30 : word) = Some W_26faec.
Proof. vm_refl. Qed.
Lemma D_26faec : decode_any W_26faec = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26faf0 : bv 32 := 0x01498a33.
Lemma F_26faf0 : fetch_word Plain.M.loaded_segments (0x26fb34 : word) = Some W_26faf0.
Proof. vm_refl. Qed.
Lemma D_26faf0 : decode_any W_26faf0 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26faf4 : bv 32 := 0x000a3703.
Lemma F_26faf4 : fetch_word Plain.M.loaded_segments (0x26fb38 : word) = Some W_26faf4.
Proof. vm_refl. Qed.
Lemma D_26faf4 : decode_any W_26faf4 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26faf8 : bv 32 := 0x40c006b3.
Lemma F_26faf8 : fetch_word Plain.M.loaded_segments (0x26fb3c : word) = Some W_26faf8.
Proof. vm_refl. Qed.
Lemma D_26faf8 : decode_any W_26faf8 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fafc : bv 32 := 0x00b6f6b3.
Lemma F_26fafc : fetch_word Plain.M.loaded_segments (0x26fb40 : word) = Some W_26fafc.
Proof. vm_refl. Qed.
Lemma D_26fafc : decode_any W_26fafc = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb00 : bv 32 := 0x40d506b3.
Lemma F_26fb00 : fetch_word Plain.M.loaded_segments (0x26fb44 : word) = Some W_26fb00.
Proof. vm_refl. Qed.
Lemma D_26fb00 : decode_any W_26fb00 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb04 : bv 32 := 0x00d70733.
Lemma F_26fb04 : fetch_word Plain.M.loaded_segments (0x26fb48 : word) = Some W_26fb04.
Proof. vm_refl. Qed.
Lemma D_26fb04 : decode_any W_26fb04 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb08 : bv 32 := 0x00ea3023.
Lemma F_26fb08 : fetch_word Plain.M.loaded_segments (0x26fb4c : word) = Some W_26fb08.
Proof. vm_refl. Qed.
Lemma D_26fb08 : decode_any W_26fb08 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb0c : bv 32 := 0xf8a5fce3.
Lemma F_26fb0c : fetch_word Plain.M.loaded_segments (0x26fb50 : word) = Some W_26fb0c.
Proof. vm_refl. Qed.
Lemma D_26fb0c : decode_any W_26fb0c = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb10 : bv 32 := 0x01800713.
Lemma F_26fb10 : fetch_word Plain.M.loaded_segments (0x26fb54 : word) = Some W_26fb10.
Proof. vm_refl. Qed.
Lemma D_26fb10 : decode_any W_26fb10 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb14 : bv 32 := 0xf95ff06f.
Lemma F_26fb14 : fetch_word Plain.M.loaded_segments (0x26fb58 : word) = Some W_26fb14.
Proof. vm_refl. Qed.
Lemma D_26fb14 : decode_any W_26fb14 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb18 : bv 32 := 0x00000513.
Lemma F_26fb18 : fetch_word Plain.M.loaded_segments (0x26fb5c : word) = Some W_26fb18.
Proof. vm_refl. Qed.
Lemma D_26fb18 : decode_any W_26fb18 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb1c : bv 32 := 0x0004a583.
Lemma F_26fb1c : fetch_word Plain.M.loaded_segments (0x26fb60 : word) = Some W_26fb1c.
Proof. vm_refl. Qed.
Lemma D_26fb1c : decode_any W_26fb1c = Some (Load SZ4 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb20 : bv 32 := 0x0009091b.
Lemma F_26fb20 : fetch_word Plain.M.loaded_segments (0x26fb64 : word) = Some W_26fb20.
Proof. vm_refl. Qed.
Lemma D_26fb20 : decode_any W_26fb20 = Some (OpImm32 18 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb24 : bv 32 := 0x00200613.
Lemma F_26fb24 : fetch_word Plain.M.loaded_segments (0x26fb68 : word) = Some W_26fb24.
Proof. vm_refl. Qed.
Lemma D_26fb24 : decode_any W_26fb24 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb28 : bv 32 := 0x0205e593.
Lemma F_26fb28 : fetch_word Plain.M.loaded_segments (0x26fb6c : word) = Some W_26fb28.
Proof. vm_refl. Qed.
Lemma D_26fb28 : decode_any W_26fb28 = Some (OpImm ALU_OR 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb2c : bv 32 := 0x00b4a023.
Lemma F_26fb2c : fetch_word Plain.M.loaded_segments (0x26fb70 : word) = Some W_26fb2c.
Proof. vm_refl. Qed.
Lemma D_26fb2c : decode_any W_26fb2c = Some (Store SZ4 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb30 : bv 32 := 0x0204b023.
Lemma F_26fb30 : fetch_word Plain.M.loaded_segments (0x26fb74 : word) = Some W_26fb30.
Proof. vm_refl. Qed.
Lemma D_26fb30 : decode_any W_26fb30 = Some (Store SZ8 9 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb34 : bv 32 := 0x0204b423.
Lemma F_26fb34 : fetch_word Plain.M.loaded_segments (0x26fb78 : word) = Some W_26fb34.
Proof. vm_refl. Qed.
Lemma D_26fb34 : decode_any W_26fb34 = Some (Store SZ8 9 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb38 : bv 32 := 0x0204bc23.
Lemma F_26fb38 : fetch_word Plain.M.loaded_segments (0x26fb7c : word) = Some W_26fb38.
Proof. vm_refl. Qed.
Lemma D_26fb38 : decode_any W_26fb38 = Some (Store SZ8 9 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb3c : bv 32 := 0xf2c90ae3.
Lemma F_26fb3c : fetch_word Plain.M.loaded_segments (0x26fb80 : word) = Some W_26fb3c.
Proof. vm_refl. Qed.
Lemma D_26fb3c : decode_any W_26fb3c = Some (Branch BC_EQ 18 12 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb40 : bv 32 := 0x0089b503.
Lemma F_26fb40 : fetch_word Plain.M.loaded_segments (0x26fb84 : word) = Some W_26fb40.
Proof. vm_refl. Qed.
Lemma D_26fb40 : decode_any W_26fb40 = Some (Load SZ8 true 10 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb44 : bv 32 := 0x40a40533.
Lemma F_26fb44 : fetch_word Plain.M.loaded_segments (0x26fb88 : word) = Some W_26fb44.
Proof. vm_refl. Qed.
Lemma D_26fb44 : decode_any W_26fb44 = Some (Op ALU_SUB 10 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb48 : bv 32 := 0xf29ff06f.
Lemma F_26fb48 : fetch_word Plain.M.loaded_segments (0x26fb8c : word) = Some W_26fb48.
Proof. vm_refl. Qed.
Lemma D_26fb48 : decode_any W_26fb48 = Some (Jal 0 2096936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb4c : bv 32 := 0xe0dfb0ef.
Lemma F_26fb4c : fetch_word Plain.M.loaded_segments (0x26fb90 : word) = Some W_26fb4c.
Proof. vm_refl. Qed.
Lemma D_26fb4c : decode_any W_26fb4c = Some (Jal 1 2080268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb50 : bv 32 := 0xfb010113.
Lemma F_26fb50 : fetch_word Plain.M.loaded_segments (0x26fb94 : word) = Some W_26fb50.
Proof. vm_refl. Qed.
Lemma D_26fb50 : decode_any W_26fb50 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb54 : bv 32 := 0x00113c23.
Lemma F_26fb54 : fetch_word Plain.M.loaded_segments (0x26fb98 : word) = Some W_26fb54.
Proof. vm_refl. Qed.
Lemma D_26fb54 : decode_any W_26fb54 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb58 : bv 32 := 0x00813823.
Lemma F_26fb58 : fetch_word Plain.M.loaded_segments (0x26fb9c : word) = Some W_26fb58.
Proof. vm_refl. Qed.
Lemma D_26fb58 : decode_any W_26fb58 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb5c : bv 32 := 0x05013023.
Lemma F_26fb5c : fetch_word Plain.M.loaded_segments (0x26fba0 : word) = Some W_26fb5c.
Proof. vm_refl. Qed.
Lemma D_26fb5c : decode_any W_26fb5c = Some (Store SZ8 2 16 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb60 : bv 32 := 0x05113423.
Lemma F_26fb60 : fetch_word Plain.M.loaded_segments (0x26fba4 : word) = Some W_26fb60.
Proof. vm_refl. Qed.
Lemma D_26fb60 : decode_any W_26fb60 = Some (Store SZ8 2 17 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb64 : bv 32 := 0x00068817.
Lemma F_26fb64 : fetch_word Plain.M.loaded_segments (0x26fba8 : word) = Some W_26fb64.
Proof. vm_refl. Qed.
Lemma D_26fb64 : decode_any W_26fb64 = Some (Auipc 16 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb68 : bv 32 := 0xff883403.
Lemma F_26fb68 : fetch_word Plain.M.loaded_segments (0x26fbac : word) = Some W_26fb68.
Proof. vm_refl. Qed.
Lemma D_26fb68 : decode_any W_26fb68 = Some (Load SZ8 true 8 16 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb6c : bv 32 := 0x02c13023.
Lemma F_26fb6c : fetch_word Plain.M.loaded_segments (0x26fbb0 : word) = Some W_26fb6c.
Proof. vm_refl. Qed.
Lemma D_26fb6c : decode_any W_26fb6c = Some (Store SZ8 2 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb70 : bv 32 := 0x02d13423.
Lemma F_26fb70 : fetch_word Plain.M.loaded_segments (0x26fbb4 : word) = Some W_26fb70.
Proof. vm_refl. Qed.
Lemma D_26fb70 : decode_any W_26fb70 = Some (Store SZ8 2 13 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb74 : bv 32 := 0x02e13823.
Lemma F_26fb74 : fetch_word Plain.M.loaded_segments (0x26fbb8 : word) = Some W_26fb74.
Proof. vm_refl. Qed.
Lemma D_26fb74 : decode_any W_26fb74 = Some (Store SZ8 2 14 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb78 : bv 32 := 0x02f13c23.
Lemma F_26fb78 : fetch_word Plain.M.loaded_segments (0x26fbbc : word) = Some W_26fb78.
Proof. vm_refl. Qed.
Lemma D_26fb78 : decode_any W_26fb78 = Some (Store SZ8 2 15 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb7c : bv 32 := 0x00043603.
Lemma F_26fb7c : fetch_word Plain.M.loaded_segments (0x26fbc0 : word) = Some W_26fb7c.
Proof. vm_refl. Qed.
Lemma D_26fb7c : decode_any W_26fb7c = Some (Load SZ8 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb80 : bv 32 := 0x02010693.
Lemma F_26fb80 : fetch_word Plain.M.loaded_segments (0x26fbc4 : word) = Some W_26fb80.
Proof. vm_refl. Qed.
Lemma D_26fb80 : decode_any W_26fb80 = Some (OpImm ALU_ADD 13 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb84 : bv 32 := 0x00c13423.
Lemma F_26fb84 : fetch_word Plain.M.loaded_segments (0x26fbc8 : word) = Some W_26fb84.
Proof. vm_refl. Qed.
Lemma D_26fb84 : decode_any W_26fb84 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb88 : bv 32 := 0x00d13023.
Lemma F_26fb88 : fetch_word Plain.M.loaded_segments (0x26fbcc : word) = Some W_26fb88.
Proof. vm_refl. Qed.
Lemma D_26fb88 : decode_any W_26fb88 = Some (Store SZ8 2 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb8c : bv 32 := 0x02010613.
Lemma F_26fb8c : fetch_word Plain.M.loaded_segments (0x26fbd0 : word) = Some W_26fb8c.
Proof. vm_refl. Qed.
Lemma D_26fb8c : decode_any W_26fb8c = Some (OpImm ALU_ADD 12 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb90 : bv 32 := 0x181000ef.
Lemma F_26fb90 : fetch_word Plain.M.loaded_segments (0x26fbd4 : word) = Some W_26fb90.
Proof. vm_refl. Qed.
Lemma D_26fb90 : decode_any W_26fb90 = Some (Jal 1 2432, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb94 : bv 32 := 0x00043583.
Lemma F_26fb94 : fetch_word Plain.M.loaded_segments (0x26fbd8 : word) = Some W_26fb94.
Proof. vm_refl. Qed.
Lemma D_26fb94 : decode_any W_26fb94 = Some (Load SZ8 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb98 : bv 32 := 0x00813603.
Lemma F_26fb98 : fetch_word Plain.M.loaded_segments (0x26fbdc : word) = Some W_26fb98.
Proof. vm_refl. Qed.
Lemma D_26fb98 : decode_any W_26fb98 = Some (Load SZ8 true 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fb9c : bv 32 := 0x00c59a63.
Lemma F_26fb9c : fetch_word Plain.M.loaded_segments (0x26fbe0 : word) = Some W_26fb9c.
Proof. vm_refl. Qed.
Lemma D_26fb9c : decode_any W_26fb9c = Some (Branch BC_NE 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fba0 : bv 32 := 0x01813083.
Lemma F_26fba0 : fetch_word Plain.M.loaded_segments (0x26fbe4 : word) = Some W_26fba0.
Proof. vm_refl. Qed.
Lemma D_26fba0 : decode_any W_26fba0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fba4 : bv 32 := 0x01013403.
Lemma F_26fba4 : fetch_word Plain.M.loaded_segments (0x26fbe8 : word) = Some W_26fba4.
Proof. vm_refl. Qed.
Lemma D_26fba4 : decode_any W_26fba4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fba8 : bv 32 := 0x05010113.
Lemma F_26fba8 : fetch_word Plain.M.loaded_segments (0x26fbec : word) = Some W_26fba8.
Proof. vm_refl. Qed.
Lemma D_26fba8 : decode_any W_26fba8 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fbac : bv 32 := 0x00008067.
Lemma F_26fbac : fetch_word Plain.M.loaded_segments (0x26fbf0 : word) = Some W_26fbac.
Proof. vm_refl. Qed.
Lemma D_26fbac : decode_any W_26fbac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fbb0 : bv 32 := 0xda9fb0ef.
Lemma F_26fbb0 : fetch_word Plain.M.loaded_segments (0x26fbf4 : word) = Some W_26fbb0.
Proof. vm_refl. Qed.
Lemma D_26fbb0 : decode_any W_26fbb0 = Some (Jal 1 2080168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fdd4 : bv 32 := 0x08852603.
Lemma F_26fdd4 : fetch_word Plain.M.loaded_segments (0x26fe18 : word) = Some W_26fdd4.
Proof. vm_refl. Qed.
Lemma D_26fdd4 : decode_any W_26fdd4 = Some (Load SZ4 true 12 10 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fdd8 : bv 32 := 0x00056583.
Lemma F_26fdd8 : fetch_word Plain.M.loaded_segments (0x26fe1c : word) = Some W_26fdd8.
Proof. vm_refl. Qed.
Lemma D_26fdd8 : decode_any W_26fdd8 = Some (Load SZ4 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fddc : bv 32 := 0xfff60693.
Lemma F_26fddc : fetch_word Plain.M.loaded_segments (0x26fe20 : word) = Some W_26fddc.
Proof. vm_refl. Qed.
Lemma D_26fddc : decode_any W_26fddc = Some (OpImm ALU_ADD 13 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fde0 : bv 32 := 0x00c6e633.
Lemma F_26fde0 : fetch_word Plain.M.loaded_segments (0x26fe24 : word) = Some W_26fde0.
Proof. vm_refl. Qed.
Lemma D_26fde0 : decode_any W_26fde0 = Some (Op ALU_OR 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fde4 : bv 32 := 0x0085f693.
Lemma F_26fde4 : fetch_word Plain.M.loaded_segments (0x26fe28 : word) = Some W_26fde4.
Proof. vm_refl. Qed.
Lemma D_26fde4 : decode_any W_26fde4 = Some (OpImm ALU_AND 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fde8 : bv 32 := 0x08c52423.
Lemma F_26fde8 : fetch_word Plain.M.loaded_segments (0x26fe2c : word) = Some W_26fde8.
Proof. vm_refl. Qed.
Lemma D_26fde8 : decode_any W_26fde8 = Some (Store SZ4 10 12 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fdec : bv 32 := 0x02069663.
Lemma F_26fdec : fetch_word Plain.M.loaded_segments (0x26fe30 : word) = Some W_26fdec.
Proof. vm_refl. Qed.
Lemma D_26fdec : decode_any W_26fdec = Some (Branch BC_NE 13 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fdf0 : bv 32 := 0x05853603.
Lemma F_26fdf0 : fetch_word Plain.M.loaded_segments (0x26fe34 : word) = Some W_26fdf0.
Proof. vm_refl. Qed.
Lemma D_26fdf0 : decode_any W_26fdf0 = Some (Load SZ8 true 12 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fdf4 : bv 32 := 0x06053683.
Lemma F_26fdf4 : fetch_word Plain.M.loaded_segments (0x26fe38 : word) = Some W_26fdf4.
Proof. vm_refl. Qed.
Lemma D_26fdf4 : decode_any W_26fdf4 = Some (Load SZ8 true 13 10 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fdf8 : bv 32 := 0x02c53c23.
Lemma F_26fdf8 : fetch_word Plain.M.loaded_segments (0x26fe3c : word) = Some W_26fdf8.
Proof. vm_refl. Qed.
Lemma D_26fdf8 : decode_any W_26fdf8 = Some (Store SZ8 10 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fdfc : bv 32 := 0x00d606b3.
Lemma F_26fdfc : fetch_word Plain.M.loaded_segments (0x26fe40 : word) = Some W_26fdfc.
Proof. vm_refl. Qed.
Lemma D_26fdfc : decode_any W_26fdfc = Some (Op ALU_ADD 13 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fe00 : bv 32 := 0x00053423.
Lemma F_26fe00 : fetch_word Plain.M.loaded_segments (0x26fe44 : word) = Some W_26fe00.
Proof. vm_refl. Qed.
Lemma D_26fe00 : decode_any W_26fe00 = Some (Store SZ8 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fe04 : bv 32 := 0x00053823.
Lemma F_26fe04 : fetch_word Plain.M.loaded_segments (0x26fe48 : word) = Some W_26fe04.
Proof. vm_refl. Qed.
Lemma D_26fe04 : decode_any W_26fe04 = Some (Store SZ8 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fe08 : bv 32 := 0x02d53023.
Lemma F_26fe08 : fetch_word Plain.M.loaded_segments (0x26fe4c : word) = Some W_26fe08.
Proof. vm_refl. Qed.
Lemma D_26fe08 : decode_any W_26fe08 = Some (Store SZ8 10 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fe0c : bv 32 := 0x02c53423.
Lemma F_26fe0c : fetch_word Plain.M.loaded_segments (0x26fe50 : word) = Some W_26fe0c.
Proof. vm_refl. Qed.
Lemma D_26fe0c : decode_any W_26fe0c = Some (Store SZ8 10 12 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fe10 : bv 32 := 0x00000513.
Lemma F_26fe10 : fetch_word Plain.M.loaded_segments (0x26fe54 : word) = Some W_26fe10.
Proof. vm_refl. Qed.
Lemma D_26fe10 : decode_any W_26fe10 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fe14 : bv 32 := 0x00008067.
Lemma F_26fe14 : fetch_word Plain.M.loaded_segments (0x26fe58 : word) = Some W_26fe14.
Proof. vm_refl. Qed.
Lemma D_26fe14 : decode_any W_26fe14 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fe18 : bv 32 := 0x0205e593.
Lemma F_26fe18 : fetch_word Plain.M.loaded_segments (0x26fe5c : word) = Some W_26fe18.
Proof. vm_refl. Qed.
Lemma D_26fe18 : decode_any W_26fe18 = Some (OpImm ALU_OR 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fe1c : bv 32 := 0x00b52023.
Lemma F_26fe1c : fetch_word Plain.M.loaded_segments (0x26fe60 : word) = Some W_26fe1c.
Proof. vm_refl. Qed.
Lemma D_26fe1c : decode_any W_26fe1c = Some (Store SZ4 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fe20 : bv 32 := 0xfff00513.
Lemma F_26fe20 : fetch_word Plain.M.loaded_segments (0x26fe64 : word) = Some W_26fe20.
Proof. vm_refl. Qed.
Lemma D_26fe20 : decode_any W_26fe20 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26fe24 : bv 32 := 0x00008067.
Lemma F_26fe24 : fetch_word Plain.M.loaded_segments (0x26fe68 : word) = Some W_26fe24.
Proof. vm_refl. Qed.
Lemma D_26fe24 : decode_any W_26fe24 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
