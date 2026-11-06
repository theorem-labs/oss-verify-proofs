(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)




(* [comment removed for export] *)
Definition W_6e45c : bv 32 := 0x02050c63.
Lemma F_6e45c : fetch_word Plain.M.loaded_segments (0x6e4b4 : word) = Some W_6e45c.
Proof. vm_refl. Qed.
Lemma D_6e45c : decode_any W_6e45c = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e460 : bv 32 := 0xff010113.
Lemma F_6e460 : fetch_word Plain.M.loaded_segments (0x6e4b8 : word) = Some W_6e460.
Proof. vm_refl. Qed.
Lemma D_6e460 : decode_any W_6e460 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e464 : bv 32 := 0x00113423.
Lemma F_6e464 : fetch_word Plain.M.loaded_segments (0x6e4bc : word) = Some W_6e464.
Proof. vm_refl. Qed.
Lemma D_6e464 : decode_any W_6e464 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e468 : bv 32 := 0x00456583.
Lemma F_6e468 : fetch_word Plain.M.loaded_segments (0x6e4c0 : word) = Some W_6e468.
Proof. vm_refl. Qed.
Lemma D_6e468 : decode_any W_6e468 = Some (Load SZ4 false 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e46c : bv 32 := 0x01056603.
Lemma F_6e46c : fetch_word Plain.M.loaded_segments (0x6e4c4 : word) = Some W_6e46c.
Proof. vm_refl. Qed.
Lemma D_6e46c : decode_any W_6e46c = Some (Load SZ4 false 12 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e470 : bv 32 := 0x03853503.
Lemma F_6e470 : fetch_word Plain.M.loaded_segments (0x6e4c8 : word) = Some W_6e470.
Proof. vm_refl. Qed.
Lemma D_6e470 : decode_any W_6e470 = Some (Load SZ8 true 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e474 : bv 32 := 0x02b60633.
Lemma F_6e474 : fetch_word Plain.M.loaded_segments (0x6e4cc : word) = Some W_6e474.
Proof. vm_refl. Qed.
Lemma D_6e474 : decode_any W_6e474 = Some (Mul M_MUL 12 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e478 : bv 32 := 0x00261613.
Lemma F_6e478 : fetch_word Plain.M.loaded_segments (0x6e4d0 : word) = Some W_6e478.
Proof. vm_refl. Qed.
Lemma D_6e478 : decode_any W_6e478 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e47c : bv 32 := 0x00000593.
Lemma F_6e47c : fetch_word Plain.M.loaded_segments (0x6e4d4 : word) = Some W_6e47c.
Proof. vm_refl. Qed.
Lemma D_6e47c : decode_any W_6e47c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e480 : bv 32 := 0x5599b0ef.
Lemma F_6e480 : fetch_word Plain.M.loaded_segments (0x6e4d8 : word) = Some W_6e480.
Proof. vm_refl. Qed.
Lemma D_6e480 : decode_any W_6e480 = Some (Jal 1 638296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e484 : bv 32 := 0x00000513.
Lemma F_6e484 : fetch_word Plain.M.loaded_segments (0x6e4dc : word) = Some W_6e484.
Proof. vm_refl. Qed.
Lemma D_6e484 : decode_any W_6e484 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e488 : bv 32 := 0x00813083.
Lemma F_6e488 : fetch_word Plain.M.loaded_segments (0x6e4e0 : word) = Some W_6e488.
Proof. vm_refl. Qed.
Lemma D_6e488 : decode_any W_6e488 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e48c : bv 32 := 0x01010113.
Lemma F_6e48c : fetch_word Plain.M.loaded_segments (0x6e4e4 : word) = Some W_6e48c.
Proof. vm_refl. Qed.
Lemma D_6e48c : decode_any W_6e48c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e490 : bv 32 := 0x00008067.
Lemma F_6e490 : fetch_word Plain.M.loaded_segments (0x6e4e8 : word) = Some W_6e490.
Proof. vm_refl. Qed.
Lemma D_6e490 : decode_any W_6e490 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e4c8 : bv 32 := 0xfe010113.
Lemma F_6e4c8 : fetch_word Plain.M.loaded_segments (0x6e520 : word) = Some W_6e4c8.
Proof. vm_refl. Qed.
Lemma D_6e4c8 : decode_any W_6e4c8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e4cc : bv 32 := 0x00113c23.
Lemma F_6e4cc : fetch_word Plain.M.loaded_segments (0x6e524 : word) = Some W_6e4cc.
Proof. vm_refl. Qed.
Lemma D_6e4cc : decode_any W_6e4cc = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e4d0 : bv 32 := 0x00813823.
Lemma F_6e4d0 : fetch_word Plain.M.loaded_segments (0x6e528 : word) = Some W_6e4d0.
Proof. vm_refl. Qed.
Lemma D_6e4d0 : decode_any W_6e4d0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e4d4 : bv 32 := 0x00913423.
Lemma F_6e4d4 : fetch_word Plain.M.loaded_segments (0x6e52c : word) = Some W_6e4d4.
Proof. vm_refl. Qed.
Lemma D_6e4d4 : decode_any W_6e4d4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e4d8 : bv 32 := 0x06050663.
Lemma F_6e4d8 : fetch_word Plain.M.loaded_segments (0x6e530 : word) = Some W_6e4d8.
Proof. vm_refl. Qed.
Lemma D_6e4d8 : decode_any W_6e4d8 = Some (Branch BC_EQ 10 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e4dc : bv 32 := 0x00050413.
Lemma F_6e4dc : fetch_word Plain.M.loaded_segments (0x6e534 : word) = Some W_6e4dc.
Proof. vm_refl. Qed.
Lemma D_6e4dc : decode_any W_6e4dc = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e4e0 : bv 32 := 0xd48ff0ef.
Lemma F_6e4e0 : fetch_word Plain.M.loaded_segments (0x6e538 : word) = Some W_6e4e0.
Proof. vm_refl. Qed.
Lemma D_6e4e0 : decode_any W_6e4e0 = Some (Jal 1 2094408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e4e4 : bv 32 := 0x02050e63.
Lemma F_6e4e4 : fetch_word Plain.M.loaded_segments (0x6e53c : word) = Some W_6e4e4.
Proof. vm_refl. Qed.
Lemma D_6e4e4 : decode_any W_6e4e4 = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e520 : bv 32 := 0x00446583.
Lemma F_6e520 : fetch_word Plain.M.loaded_segments (0x6e578 : word) = Some W_6e520.
Proof. vm_refl. Qed.
Lemma D_6e520 : decode_any W_6e520 = Some (Load SZ4 false 11 8 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e524 : bv 32 := 0x01046603.
Lemma F_6e524 : fetch_word Plain.M.loaded_segments (0x6e57c : word) = Some W_6e524.
Proof. vm_refl. Qed.
Lemma D_6e524 : decode_any W_6e524 = Some (Load SZ4 false 12 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e528 : bv 32 := 0x03843503.
Lemma F_6e528 : fetch_word Plain.M.loaded_segments (0x6e580 : word) = Some W_6e528.
Proof. vm_refl. Qed.
Lemma D_6e528 : decode_any W_6e528 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e52c : bv 32 := 0x02b60633.
Lemma F_6e52c : fetch_word Plain.M.loaded_segments (0x6e584 : word) = Some W_6e52c.
Proof. vm_refl. Qed.
Lemma D_6e52c : decode_any W_6e52c = Some (Mul M_MUL 12 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e530 : bv 32 := 0x00261613.
Lemma F_6e530 : fetch_word Plain.M.loaded_segments (0x6e588 : word) = Some W_6e530.
Proof. vm_refl. Qed.
Lemma D_6e530 : decode_any W_6e530 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e534 : bv 32 := 0x0ff00593.
Lemma F_6e534 : fetch_word Plain.M.loaded_segments (0x6e58c : word) = Some W_6e534.
Proof. vm_refl. Qed.
Lemma D_6e534 : decode_any W_6e534 = Some (OpImm ALU_ADD 11 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e538 : bv 32 := 0x4a19b0ef.
Lemma F_6e538 : fetch_word Plain.M.loaded_segments (0x6e590 : word) = Some W_6e538.
Proof. vm_refl. Qed.
Lemma D_6e538 : decode_any W_6e538 = Some (Jal 1 638112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e53c : bv 32 := 0x00000513.
Lemma F_6e53c : fetch_word Plain.M.loaded_segments (0x6e594 : word) = Some W_6e53c.
Proof. vm_refl. Qed.
Lemma D_6e53c : decode_any W_6e53c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e540 : bv 32 := 0x0440006f.
Lemma F_6e540 : fetch_word Plain.M.loaded_segments (0x6e598 : word) = Some W_6e540.
Proof. vm_refl. Qed.
Lemma D_6e540 : decode_any W_6e540 = Some (Jal 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e584 : bv 32 := 0x01813083.
Lemma F_6e584 : fetch_word Plain.M.loaded_segments (0x6e5dc : word) = Some W_6e584.
Proof. vm_refl. Qed.
Lemma D_6e584 : decode_any W_6e584 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e588 : bv 32 := 0x01013403.
Lemma F_6e588 : fetch_word Plain.M.loaded_segments (0x6e5e0 : word) = Some W_6e588.
Proof. vm_refl. Qed.
Lemma D_6e588 : decode_any W_6e588 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e58c : bv 32 := 0x00813483.
Lemma F_6e58c : fetch_word Plain.M.loaded_segments (0x6e5e4 : word) = Some W_6e58c.
Proof. vm_refl. Qed.
Lemma D_6e58c : decode_any W_6e58c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e590 : bv 32 := 0x02010113.
Lemma F_6e590 : fetch_word Plain.M.loaded_segments (0x6e5e8 : word) = Some W_6e590.
Proof. vm_refl. Qed.
Lemma D_6e590 : decode_any W_6e590 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e594 : bv 32 := 0x00008067.
Lemma F_6e594 : fetch_word Plain.M.loaded_segments (0x6e5ec : word) = Some W_6e594.
Proof. vm_refl. Qed.
Lemma D_6e594 : decode_any W_6e594 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ecc4 : bv 32 := 0xfd010113.
Lemma F_6ecc4 : fetch_word Plain.M.loaded_segments (0x6ed1c : word) = Some W_6ecc4.
Proof. vm_refl. Qed.
Lemma D_6ecc4 : decode_any W_6ecc4 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ecc8 : bv 32 := 0x02113423.
Lemma F_6ecc8 : fetch_word Plain.M.loaded_segments (0x6ed20 : word) = Some W_6ecc8.
Proof. vm_refl. Qed.
Lemma D_6ecc8 : decode_any W_6ecc8 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6eccc : bv 32 := 0x02813023.
Lemma F_6eccc : fetch_word Plain.M.loaded_segments (0x6ed24 : word) = Some W_6eccc.
Proof. vm_refl. Qed.
Lemma D_6eccc : decode_any W_6eccc = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ecd0 : bv 32 := 0x00913c23.
Lemma F_6ecd0 : fetch_word Plain.M.loaded_segments (0x6ed28 : word) = Some W_6ecd0.
Proof. vm_refl. Qed.
Lemma D_6ecd0 : decode_any W_6ecd0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ecd4 : bv 32 := 0x01213823.
Lemma F_6ecd4 : fetch_word Plain.M.loaded_segments (0x6ed2c : word) = Some W_6ecd4.
Proof. vm_refl. Qed.
Lemma D_6ecd4 : decode_any W_6ecd4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ecd8 : bv 32 := 0x06050063.
Lemma F_6ecd8 : fetch_word Plain.M.loaded_segments (0x6ed30 : word) = Some W_6ecd8.
Proof. vm_refl. Qed.
Lemma D_6ecd8 : decode_any W_6ecd8 = Some (Branch BC_EQ 10 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ecdc : bv 32 := 0x00050493.
Lemma F_6ecdc : fetch_word Plain.M.loaded_segments (0x6ed34 : word) = Some W_6ecdc.
Proof. vm_refl. Qed.
Lemma D_6ecdc : decode_any W_6ecdc = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ece0 : bv 32 := 0x00058913.
Lemma F_6ece0 : fetch_word Plain.M.loaded_segments (0x6ed38 : word) = Some W_6ece0.
Proof. vm_refl. Qed.
Lemma D_6ece0 : decode_any W_6ece0 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ece4 : bv 32 := 0x00c10593.
Lemma F_6ece4 : fetch_word Plain.M.loaded_segments (0x6ed3c : word) = Some W_6ece4.
Proof. vm_refl. Qed.
Lemma D_6ece4 : decode_any W_6ece4 = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ece8 : bv 32 := 0x00810613.
Lemma F_6ece8 : fetch_word Plain.M.loaded_segments (0x6ed40 : word) = Some W_6ece8.
Proof. vm_refl. Qed.
Lemma D_6ece8 : decode_any W_6ece8 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ecec : bv 32 := 0x00410693.
Lemma F_6ecec : fetch_word Plain.M.loaded_segments (0x6ed44 : word) = Some W_6ecec.
Proof. vm_refl. Qed.
Lemma D_6ecec : decode_any W_6ecec = Some (OpImm ALU_ADD 13 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ecf0 : bv 32 := 0x8b0fe0ef.
Lemma F_6ecf0 : fetch_word Plain.M.loaded_segments (0x6ed48 : word) = Some W_6ecf0.
Proof. vm_refl. Qed.
Lemma D_6ecf0 : decode_any W_6ecf0 = Some (Jal 1 2089136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ecf4 : bv 32 := 0x00412503.
Lemma F_6ecf4 : fetch_word Plain.M.loaded_segments (0x6ed4c : word) = Some W_6ecf4.
Proof. vm_refl. Qed.
Lemma D_6ecf4 : decode_any W_6ecf4 = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ecf8 : bv 32 := 0x02000593.
Lemma F_6ecf8 : fetch_word Plain.M.loaded_segments (0x6ed50 : word) = Some W_6ecf8.
Proof. vm_refl. Qed.
Lemma D_6ecf8 : decode_any W_6ecf8 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ecfc : bv 32 := 0x12b50463.
Lemma F_6ecfc : fetch_word Plain.M.loaded_segments (0x6ed54 : word) = Some W_6ecfc.
Proof. vm_refl. Qed.
Lemma D_6ecfc : decode_any W_6ecfc = Some (Branch BC_EQ 10 11 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ee24 : bv 32 := 0x00000513.
Lemma F_6ee24 : fetch_word Plain.M.loaded_segments (0x6ee7c : word) = Some W_6ee24.
Proof. vm_refl. Qed.
Lemma D_6ee24 : decode_any W_6ee24 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ee28 : bv 32 := 0x02813083.
Lemma F_6ee28 : fetch_word Plain.M.loaded_segments (0x6ee80 : word) = Some W_6ee28.
Proof. vm_refl. Qed.
Lemma D_6ee28 : decode_any W_6ee28 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ee2c : bv 32 := 0x02013403.
Lemma F_6ee2c : fetch_word Plain.M.loaded_segments (0x6ee84 : word) = Some W_6ee2c.
Proof. vm_refl. Qed.
Lemma D_6ee2c : decode_any W_6ee2c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ee30 : bv 32 := 0x01813483.
Lemma F_6ee30 : fetch_word Plain.M.loaded_segments (0x6ee88 : word) = Some W_6ee30.
Proof. vm_refl. Qed.
Lemma D_6ee30 : decode_any W_6ee30 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ee34 : bv 32 := 0x01013903.
Lemma F_6ee34 : fetch_word Plain.M.loaded_segments (0x6ee8c : word) = Some W_6ee34.
Proof. vm_refl. Qed.
Lemma D_6ee34 : decode_any W_6ee34 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ee38 : bv 32 := 0x03010113.
Lemma F_6ee38 : fetch_word Plain.M.loaded_segments (0x6ee90 : word) = Some W_6ee38.
Proof. vm_refl. Qed.
Lemma D_6ee38 : decode_any W_6ee38 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ee3c : bv 32 := 0x00008067.
Lemma F_6ee3c : fetch_word Plain.M.loaded_segments (0x6ee94 : word) = Some W_6ee3c.
Proof. vm_refl. Qed.
Lemma D_6ee3c : decode_any W_6ee3c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
