(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_9b434 : bv 32 := 0x00008067.
Lemma F_9b434 : fetch_word Plain.M.loaded_segments (0x9b48c : word) = Some W_9b434.
Proof. vm_refl. Qed.
Lemma D_9b434 : decode_any W_9b434 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b438 : bv 32 := 0xe8010113.
Lemma F_9b438 : fetch_word Plain.M.loaded_segments (0x9b490 : word) = Some W_9b438.
Proof. vm_refl. Qed.
Lemma D_9b438 : decode_any W_9b438 = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b43c : bv 32 := 0x16113c23.
Lemma F_9b43c : fetch_word Plain.M.loaded_segments (0x9b494 : word) = Some W_9b43c.
Proof. vm_refl. Qed.
Lemma D_9b43c : decode_any W_9b43c = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b440 : bv 32 := 0x16813823.
Lemma F_9b440 : fetch_word Plain.M.loaded_segments (0x9b498 : word) = Some W_9b440.
Proof. vm_refl. Qed.
Lemma D_9b440 : decode_any W_9b440 = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b444 : bv 32 := 0x16913423.
Lemma F_9b444 : fetch_word Plain.M.loaded_segments (0x9b49c : word) = Some W_9b444.
Proof. vm_refl. Qed.
Lemma D_9b444 : decode_any W_9b444 = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b448 : bv 32 := 0x17213023.
Lemma F_9b448 : fetch_word Plain.M.loaded_segments (0x9b4a0 : word) = Some W_9b448.
Proof. vm_refl. Qed.
Lemma D_9b448 : decode_any W_9b448 = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b44c : bv 32 := 0x00058413.
Lemma F_9b44c : fetch_word Plain.M.loaded_segments (0x9b4a4 : word) = Some W_9b44c.
Proof. vm_refl. Qed.
Lemma D_9b44c : decode_any W_9b44c = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b450 : bv 32 := 0x00050493.
Lemma F_9b450 : fetch_word Plain.M.loaded_segments (0x9b4a8 : word) = Some W_9b450.
Proof. vm_refl. Qed.
Lemma D_9b450 : decode_any W_9b450 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b454 : bv 32 := 0x03010513.
Lemma F_9b454 : fetch_word Plain.M.loaded_segments (0x9b4ac : word) = Some W_9b454.
Proof. vm_refl. Qed.
Lemma D_9b454 : decode_any W_9b454 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b458 : bv 32 := 0x13000613.
Lemma F_9b458 : fetch_word Plain.M.loaded_segments (0x9b4b0 : word) = Some W_9b458.
Proof. vm_refl. Qed.
Lemma D_9b458 : decode_any W_9b458 = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b45c : bv 32 := 0x00000593.
Lemma F_9b45c : fetch_word Plain.M.loaded_segments (0x9b4b4 : word) = Some W_9b45c.
Proof. vm_refl. Qed.
Lemma D_9b45c : decode_any W_9b45c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b460 : bv 32 := 0x554110ef.
Lemma F_9b460 : fetch_word Plain.M.loaded_segments (0x9b4b8 : word) = Some W_9b460.
Proof. vm_refl. Qed.
Lemma D_9b460 : decode_any W_9b460 = Some (Jal 1 70996, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b464 : bv 32 := 0x0001d517.
Lemma F_9b464 : fetch_word Plain.M.loaded_segments (0x9b4bc : word) = Some W_9b464.
Proof. vm_refl. Qed.
Lemma D_9b464 : decode_any W_9b464 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b468 : bv 32 := 0xdbc53503.
Lemma F_9b468 : fetch_word Plain.M.loaded_segments (0x9b4c0 : word) = Some W_9b468.
Proof. vm_refl. Qed.
Lemma D_9b468 : decode_any W_9b468 = Some (Load SZ8 true 10 10 3516, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b46c : bv 32 := 0x00953023.
Lemma F_9b46c : fetch_word Plain.M.loaded_segments (0x9b4c4 : word) = Some W_9b46c.
Proof. vm_refl. Qed.
Lemma D_9b46c : decode_any W_9b46c = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b470 : bv 32 := 0x0004b503.
Lemma F_9b470 : fetch_word Plain.M.loaded_segments (0x9b4c8 : word) = Some W_9b470.
Proof. vm_refl. Qed.
Lemma D_9b470 : decode_any W_9b470 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b474 : bv 32 := 0x00848493.
Lemma F_9b474 : fetch_word Plain.M.loaded_segments (0x9b4cc : word) = Some W_9b474.
Proof. vm_refl. Qed.
Lemma D_9b474 : decode_any W_9b474 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b478 : bv 32 := 0xfe051ce3.
Lemma F_9b478 : fetch_word Plain.M.loaded_segments (0x9b4d0 : word) = Some W_9b478.
Proof. vm_refl. Qed.
Lemma D_9b478 : decode_any W_9b478 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b47c : bv 32 := 0x00050517.
Lemma F_9b47c : fetch_word Plain.M.loaded_segments (0x9b4d4 : word) = Some W_9b47c.
Proof. vm_refl. Qed.
Lemma D_9b47c : decode_any W_9b47c = Some (Auipc 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b480 : bv 32 := 0xdfc50913.
Lemma F_9b480 : fetch_word Plain.M.loaded_segments (0x9b4d8 : word) = Some W_9b480.
Proof. vm_refl. Qed.
Lemma D_9b480 : decode_any W_9b480 = Some (OpImm ALU_ADD 18 10 3580, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b484 : bv 32 := 0x00993423.
Lemma F_9b484 : fetch_word Plain.M.loaded_segments (0x9b4dc : word) = Some W_9b484.
Proof. vm_refl. Qed.
Lemma D_9b484 : decode_any W_9b484 = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b488 : bv 32 := 0x0004b583.
Lemma F_9b488 : fetch_word Plain.M.loaded_segments (0x9b4e0 : word) = Some W_9b488.
Proof. vm_refl. Qed.
Lemma D_9b488 : decode_any W_9b488 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b48c : bv 32 := 0x04058c63.
Lemma F_9b48c : fetch_word Plain.M.loaded_segments (0x9b4e4 : word) = Some W_9b48c.
Proof. vm_refl. Qed.
Lemma D_9b48c : decode_any W_9b48c = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b490 : bv 32 := 0x01048493.
Lemma F_9b490 : fetch_word Plain.M.loaded_segments (0x9b4e8 : word) = Some W_9b490.
Proof. vm_refl. Qed.
Lemma D_9b490 : decode_any W_9b490 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b494 : bv 32 := 0x02500513.
Lemma F_9b494 : fetch_word Plain.M.loaded_segments (0x9b4ec : word) = Some W_9b494.
Proof. vm_refl. Qed.
Lemma D_9b494 : decode_any W_9b494 = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b498 : bv 32 := 0x03010613.
Lemma F_9b498 : fetch_word Plain.M.loaded_segments (0x9b4f0 : word) = Some W_9b498.
Proof. vm_refl. Qed.
Lemma D_9b498 : decode_any W_9b498 = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b49c : bv 32 := 0x0100006f.
Lemma F_9b49c : fetch_word Plain.M.loaded_segments (0x9b4f4 : word) = Some W_9b49c.
Proof. vm_refl. Qed.
Lemma D_9b49c : decode_any W_9b49c = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b4a0 : bv 32 := 0x0004b583.
Lemma F_9b4a0 : fetch_word Plain.M.loaded_segments (0x9b4f8 : word) = Some W_9b4a0.
Proof. vm_refl. Qed.
Lemma D_9b4a0 : decode_any W_9b4a0 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b4a4 : bv 32 := 0x01048493.
Lemma F_9b4a4 : fetch_word Plain.M.loaded_segments (0x9b4fc : word) = Some W_9b4a4.
Proof. vm_refl. Qed.
Lemma D_9b4a4 : decode_any W_9b4a4 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b4a8 : bv 32 := 0x00058e63.
Lemma F_9b4a8 : fetch_word Plain.M.loaded_segments (0x9b500 : word) = Some W_9b4a8.
Proof. vm_refl. Qed.
Lemma D_9b4a8 : decode_any W_9b4a8 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b4ac : bv 32 := 0xfeb56ae3.
Lemma F_9b4ac : fetch_word Plain.M.loaded_segments (0x9b504 : word) = Some W_9b4ac.
Proof. vm_refl. Qed.
Lemma D_9b4ac : decode_any W_9b4ac = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b4b0 : bv 32 := 0xff84b683.
Lemma F_9b4b0 : fetch_word Plain.M.loaded_segments (0x9b508 : word) = Some W_9b4b0.
Proof. vm_refl. Qed.
Lemma D_9b4b0 : decode_any W_9b4b0 = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b4b4 : bv 32 := 0x00359593.
Lemma F_9b4b4 : fetch_word Plain.M.loaded_segments (0x9b50c : word) = Some W_9b4b4.
Proof. vm_refl. Qed.
Lemma D_9b4b4 : decode_any W_9b4b4 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b4b8 : bv 32 := 0x00b605b3.
Lemma F_9b4b8 : fetch_word Plain.M.loaded_segments (0x9b510 : word) = Some W_9b4b8.
Proof. vm_refl. Qed.
Lemma D_9b4b8 : decode_any W_9b4b8 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b4bc : bv 32 := 0x00d5b023.
Lemma F_9b4bc : fetch_word Plain.M.loaded_segments (0x9b514 : word) = Some W_9b4bc.
Proof. vm_refl. Qed.
Lemma D_9b4bc : decode_any W_9b4bc = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b4c0 : bv 32 := 0xfe1ff06f.
Lemma F_9b4c0 : fetch_word Plain.M.loaded_segments (0x9b518 : word) = Some W_9b4c0.
Proof. vm_refl. Qed.
Lemma D_9b4c0 : decode_any W_9b4c0 = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b4c4 : bv 32 := 0x0b013583.
Lemma F_9b4c4 : fetch_word Plain.M.loaded_segments (0x9b51c : word) = Some W_9b4c4.
Proof. vm_refl. Qed.
Lemma D_9b4c4 : decode_any W_9b4c4 = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b4c8 : bv 32 := 0x13013503.
Lemma F_9b4c8 : fetch_word Plain.M.loaded_segments (0x9b520 : word) = Some W_9b4c8.
Proof. vm_refl. Qed.
Lemma D_9b4c8 : decode_any W_9b4c8 = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b4cc : bv 32 := 0x00050617.
Lemma F_9b4cc : fetch_word Plain.M.loaded_segments (0x9b524 : word) = Some W_9b4cc.
Proof. vm_refl. Qed.
Lemma D_9b4cc : decode_any W_9b4cc = Some (Auipc 12 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b4d0 : bv 32 := 0xe0b63a23.
Lemma F_9b4d0 : fetch_word Plain.M.loaded_segments (0x9b528 : word) = Some W_9b4d0.
Proof. vm_refl. Qed.
Lemma D_9b4d0 : decode_any W_9b4d0 = Some (Store SZ8 12 11 3604, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b4d4 : bv 32 := 0x00050c63.
Lemma F_9b4d4 : fetch_word Plain.M.loaded_segments (0x9b52c : word) = Some W_9b4d4.
Proof. vm_refl. Qed.
Lemma D_9b4d4 : decode_any W_9b4d4 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b4ec : bv 32 := 0x06013503.
Lemma F_9b4ec : fetch_word Plain.M.loaded_segments (0x9b544 : word) = Some W_9b4ec.
Proof. vm_refl. Qed.
Lemma D_9b4ec : decode_any W_9b4ec = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b4f0 : bv 32 := 0x02a93823.
Lemma F_9b4f0 : fetch_word Plain.M.loaded_segments (0x9b548 : word) = Some W_9b4f0.
Proof. vm_refl. Qed.
Lemma D_9b4f0 : decode_any W_9b4f0 = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b4f4 : bv 32 := 0x00041463.
Lemma F_9b4f4 : fetch_word Plain.M.loaded_segments (0x9b54c : word) = Some W_9b4f4.
Proof. vm_refl. Qed.
Lemma D_9b4f4 : decode_any W_9b4f4 = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b4fc : bv 32 := 0x00041663.
Lemma F_9b4fc : fetch_word Plain.M.loaded_segments (0x9b554 : word) = Some W_9b4fc.
Proof. vm_refl. Qed.
Lemma D_9b4fc : decode_any W_9b4fc = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b508 : bv 32 := 0x0001d517.
Lemma F_9b508 : fetch_word Plain.M.loaded_segments (0x9b560 : word) = Some W_9b508.
Proof. vm_refl. Qed.
Lemma D_9b508 : decode_any W_9b508 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b50c : bv 32 := 0xd2053583.
Lemma F_9b50c : fetch_word Plain.M.loaded_segments (0x9b564 : word) = Some W_9b50c.
Proof. vm_refl. Qed.
Lemma D_9b50c : decode_any W_9b50c = Some (Load SZ8 true 11 10 3360, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b510 : bv 32 := 0x0001d517.
Lemma F_9b510 : fetch_word Plain.M.loaded_segments (0x9b568 : word) = Some W_9b510.
Proof. vm_refl. Qed.
Lemma D_9b510 : decode_any W_9b510 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b514 : bv 32 := 0xd2053503.
Lemma F_9b514 : fetch_word Plain.M.loaded_segments (0x9b56c : word) = Some W_9b514.
Proof. vm_refl. Qed.
Lemma D_9b514 : decode_any W_9b514 = Some (Load SZ8 true 10 10 3360, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b518 : bv 32 := 0x0085b023.
Lemma F_9b518 : fetch_word Plain.M.loaded_segments (0x9b570 : word) = Some W_9b518.
Proof. vm_refl. Qed.
Lemma D_9b518 : decode_any W_9b518 = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b51c : bv 32 := 0x00140593.
Lemma F_9b51c : fetch_word Plain.M.loaded_segments (0x9b574 : word) = Some W_9b51c.
Proof. vm_refl. Qed.
Lemma D_9b51c : decode_any W_9b51c = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b520 : bv 32 := 0x00853023.
Lemma F_9b520 : fetch_word Plain.M.loaded_segments (0x9b578 : word) = Some W_9b520.
Proof. vm_refl. Qed.
Lemma D_9b520 : decode_any W_9b520 = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b524 : bv 32 := 0x02f00613.
Lemma F_9b524 : fetch_word Plain.M.loaded_segments (0x9b57c : word) = Some W_9b524.
Proof. vm_refl. Qed.
Lemma D_9b524 : decode_any W_9b524 = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b528 : bv 32 := 0x00c0006f.
Lemma F_9b528 : fetch_word Plain.M.loaded_segments (0x9b580 : word) = Some W_9b528.
Proof. vm_refl. Qed.
Lemma D_9b528 : decode_any W_9b528 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b52c : bv 32 := 0x00b53023.
Lemma F_9b52c : fetch_word Plain.M.loaded_segments (0x9b584 : word) = Some W_9b52c.
Proof. vm_refl. Qed.
Lemma D_9b52c : decode_any W_9b52c = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b530 : bv 32 := 0x00158593.
Lemma F_9b530 : fetch_word Plain.M.loaded_segments (0x9b588 : word) = Some W_9b530.
Proof. vm_refl. Qed.
Lemma D_9b530 : decode_any W_9b530 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b534 : bv 32 := 0xfff5c683.
Lemma F_9b534 : fetch_word Plain.M.loaded_segments (0x9b58c : word) = Some W_9b534.
Proof. vm_refl. Qed.
Lemma D_9b534 : decode_any W_9b534 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b538 : bv 32 := 0xfec68ae3.
Lemma F_9b538 : fetch_word Plain.M.loaded_segments (0x9b590 : word) = Some W_9b538.
Proof. vm_refl. Qed.
Lemma D_9b538 : decode_any W_9b538 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b53c : bv 32 := 0xfe069ae3.
Lemma F_9b53c : fetch_word Plain.M.loaded_segments (0x9b594 : word) = Some W_9b53c.
Proof. vm_refl. Qed.
Lemma D_9b53c : decode_any W_9b53c = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b540 : bv 32 := 0x03010513.
Lemma F_9b540 : fetch_word Plain.M.loaded_segments (0x9b598 : word) = Some W_9b540.
Proof. vm_refl. Qed.
Lemma D_9b540 : decode_any W_9b540 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b544 : bv 32 := 0x214000ef.
Lemma F_9b544 : fetch_word Plain.M.loaded_segments (0x9b59c : word) = Some W_9b544.
Proof. vm_refl. Qed.
Lemma D_9b544 : decode_any W_9b544 = Some (Jal 1 532, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b548 : bv 32 := 0x0f813503.
Lemma F_9b548 : fetch_word Plain.M.loaded_segments (0x9b5a0 : word) = Some W_9b548.
Proof. vm_refl. Qed.
Lemma D_9b548 : decode_any W_9b548 = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b54c : bv 32 := 0x1ad000ef.
Lemma F_9b54c : fetch_word Plain.M.loaded_segments (0x9b5a4 : word) = Some W_9b54c.
Proof. vm_refl. Qed.
Lemma D_9b54c : decode_any W_9b54c = Some (Jal 1 2476, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b550 : bv 32 := 0x08813503.
Lemma F_9b550 : fetch_word Plain.M.loaded_segments (0x9b5a8 : word) = Some W_9b550.
Proof. vm_refl. Qed.
Lemma D_9b550 : decode_any W_9b550 = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b554 : bv 32 := 0x09013583.
Lemma F_9b554 : fetch_word Plain.M.loaded_segments (0x9b5ac : word) = Some W_9b554.
Proof. vm_refl. Qed.
Lemma D_9b554 : decode_any W_9b554 = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b558 : bv 32 := 0x00b51c63.
Lemma F_9b558 : fetch_word Plain.M.loaded_segments (0x9b5b0 : word) = Some W_9b558.
Proof. vm_refl. Qed.
Lemma D_9b558 : decode_any W_9b558 = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b55c : bv 32 := 0x09813503.
Lemma F_9b55c : fetch_word Plain.M.loaded_segments (0x9b5b4 : word) = Some W_9b55c.
Proof. vm_refl. Qed.
Lemma D_9b55c : decode_any W_9b55c = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b560 : bv 32 := 0x0a013583.
Lemma F_9b560 : fetch_word Plain.M.loaded_segments (0x9b5b8 : word) = Some W_9b560.
Proof. vm_refl. Qed.
Lemma D_9b560 : decode_any W_9b560 = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b564 : bv 32 := 0x00b51663.
Lemma F_9b564 : fetch_word Plain.M.loaded_segments (0x9b5bc : word) = Some W_9b564.
Proof. vm_refl. Qed.
Lemma D_9b564 : decode_any W_9b564 = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b568 : bv 32 := 0x0e813503.
Lemma F_9b568 : fetch_word Plain.M.loaded_segments (0x9b5c0 : word) = Some W_9b568.
Proof. vm_refl. Qed.
Lemma D_9b568 : decode_any W_9b568 = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b56c : bv 32 := 0x0e050063.
Lemma F_9b56c : fetch_word Plain.M.loaded_segments (0x9b5c4 : word) = Some W_9b56c.
Proof. vm_refl. Qed.
Lemma D_9b56c : decode_any W_9b56c = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b64c : bv 32 := 0x17813083.
Lemma F_9b64c : fetch_word Plain.M.loaded_segments (0x9b6a4 : word) = Some W_9b64c.
Proof. vm_refl. Qed.
Lemma D_9b64c : decode_any W_9b64c = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b650 : bv 32 := 0x17013403.
Lemma F_9b650 : fetch_word Plain.M.loaded_segments (0x9b6a8 : word) = Some W_9b650.
Proof. vm_refl. Qed.
Lemma D_9b650 : decode_any W_9b650 = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b654 : bv 32 := 0x16813483.
Lemma F_9b654 : fetch_word Plain.M.loaded_segments (0x9b6ac : word) = Some W_9b654.
Proof. vm_refl. Qed.
Lemma D_9b654 : decode_any W_9b654 = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b658 : bv 32 := 0x16013903.
Lemma F_9b658 : fetch_word Plain.M.loaded_segments (0x9b6b0 : word) = Some W_9b658.
Proof. vm_refl. Qed.
Lemma D_9b658 : decode_any W_9b658 = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b65c : bv 32 := 0x18010113.
Lemma F_9b65c : fetch_word Plain.M.loaded_segments (0x9b6b4 : word) = Some W_9b65c.
Proof. vm_refl. Qed.
Lemma D_9b65c : decode_any W_9b65c = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b660 : bv 32 := 0x00008067.
Lemma F_9b660 : fetch_word Plain.M.loaded_segments (0x9b6b8 : word) = Some W_9b660.
Proof. vm_refl. Qed.
Lemma D_9b660 : decode_any W_9b660 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b664 : bv 32 := 0xfe010113.
Lemma F_9b664 : fetch_word Plain.M.loaded_segments (0x9b6bc : word) = Some W_9b664.
Proof. vm_refl. Qed.
Lemma D_9b664 : decode_any W_9b664 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b668 : bv 32 := 0x00113c23.
Lemma F_9b668 : fetch_word Plain.M.loaded_segments (0x9b6c0 : word) = Some W_9b668.
Proof. vm_refl. Qed.
Lemma D_9b668 : decode_any W_9b668 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b66c : bv 32 := 0x00813823.
Lemma F_9b66c : fetch_word Plain.M.loaded_segments (0x9b6c4 : word) = Some W_9b66c.
Proof. vm_refl. Qed.
Lemma D_9b66c : decode_any W_9b66c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b670 : bv 32 := 0x00913423.
Lemma F_9b670 : fetch_word Plain.M.loaded_segments (0x9b6c8 : word) = Some W_9b670.
Proof. vm_refl. Qed.
Lemma D_9b670 : decode_any W_9b670 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b674 : bv 32 := 0xdc1ff0ef.
Lemma F_9b674 : fetch_word Plain.M.loaded_segments (0x9b6cc : word) = Some W_9b674.
Proof. vm_refl. Qed.
Lemma D_9b674 : decode_any W_9b674 = Some (Jal 1 2096576, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b678 : bv 32 := 0x0001d517.
Lemma F_9b678 : fetch_word Plain.M.loaded_segments (0x9b6d0 : word) = Some W_9b678.
Proof. vm_refl. Qed.
Lemma D_9b678 : decode_any W_9b678 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b67c : bv 32 := 0x0001d597.
Lemma F_9b67c : fetch_word Plain.M.loaded_segments (0x9b6d4 : word) = Some W_9b67c.
Proof. vm_refl. Qed.
Lemma D_9b67c : decode_any W_9b67c = Some (Auipc 11 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b680 : bv 32 := 0xbc053403.
Lemma F_9b680 : fetch_word Plain.M.loaded_segments (0x9b6d8 : word) = Some W_9b680.
Proof. vm_refl. Qed.
Lemma D_9b680 : decode_any W_9b680 = Some (Load SZ8 true 8 10 3008, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b684 : bv 32 := 0xbc45b483.
Lemma F_9b684 : fetch_word Plain.M.loaded_segments (0x9b6dc : word) = Some W_9b684.
Proof. vm_refl. Qed.
Lemma D_9b684 : decode_any W_9b684 = Some (Load SZ8 true 9 11 3012, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b688 : bv 32 := 0x0084fa63.
Lemma F_9b688 : fetch_word Plain.M.loaded_segments (0x9b6e0 : word) = Some W_9b688.
Proof. vm_refl. Qed.
Lemma D_9b688 : decode_any W_9b688 = Some (Branch BC_GEU 9 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b68c : bv 32 := 0x0004b503.
Lemma F_9b68c : fetch_word Plain.M.loaded_segments (0x9b6e4 : word) = Some W_9b68c.
Proof. vm_refl. Qed.
Lemma D_9b68c : decode_any W_9b68c = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b690 : bv 32 := 0x000500e7.
Lemma F_9b690 : fetch_word Plain.M.loaded_segments (0x9b6e8 : word) = Some W_9b690.
Proof. vm_refl. Qed.
Lemma D_9b690 : decode_any W_9b690 = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b694 : bv 32 := 0x00848493.
Lemma F_9b694 : fetch_word Plain.M.loaded_segments (0x9b6ec : word) = Some W_9b694.
Proof. vm_refl. Qed.
Lemma D_9b694 : decode_any W_9b694 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b698 : bv 32 := 0xfe84eae3.
Lemma F_9b698 : fetch_word Plain.M.loaded_segments (0x9b6f0 : word) = Some W_9b698.
Proof. vm_refl. Qed.
Lemma D_9b698 : decode_any W_9b698 = Some (Branch BC_LTU 9 8 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b69c : bv 32 := 0x01813083.
Lemma F_9b69c : fetch_word Plain.M.loaded_segments (0x9b6f4 : word) = Some W_9b69c.
Proof. vm_refl. Qed.
Lemma D_9b69c : decode_any W_9b69c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b6a0 : bv 32 := 0x01013403.
Lemma F_9b6a0 : fetch_word Plain.M.loaded_segments (0x9b6f8 : word) = Some W_9b6a0.
Proof. vm_refl. Qed.
Lemma D_9b6a0 : decode_any W_9b6a0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b6a4 : bv 32 := 0x00813483.
Lemma F_9b6a4 : fetch_word Plain.M.loaded_segments (0x9b6fc : word) = Some W_9b6a4.
Proof. vm_refl. Qed.
Lemma D_9b6a4 : decode_any W_9b6a4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b6a8 : bv 32 := 0x02010113.
Lemma F_9b6a8 : fetch_word Plain.M.loaded_segments (0x9b700 : word) = Some W_9b6a8.
Proof. vm_refl. Qed.
Lemma D_9b6a8 : decode_any W_9b6a8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b6ac : bv 32 := 0x00008067.
Lemma F_9b6ac : fetch_word Plain.M.loaded_segments (0x9b704 : word) = Some W_9b6ac.
Proof. vm_refl. Qed.
Lemma D_9b6ac : decode_any W_9b6ac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b6b0 : bv 32 := 0xfe010113.
Lemma F_9b6b0 : fetch_word Plain.M.loaded_segments (0x9b708 : word) = Some W_9b6b0.
Proof. vm_refl. Qed.
Lemma D_9b6b0 : decode_any W_9b6b0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b6b4 : bv 32 := 0x00113c23.
Lemma F_9b6b4 : fetch_word Plain.M.loaded_segments (0x9b70c : word) = Some W_9b6b4.
Proof. vm_refl. Qed.
Lemma D_9b6b4 : decode_any W_9b6b4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b6b8 : bv 32 := 0x00813823.
Lemma F_9b6b8 : fetch_word Plain.M.loaded_segments (0x9b710 : word) = Some W_9b6b8.
Proof. vm_refl. Qed.
Lemma D_9b6b8 : decode_any W_9b6b8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b6bc : bv 32 := 0x00913423.
Lemma F_9b6bc : fetch_word Plain.M.loaded_segments (0x9b714 : word) = Some W_9b6bc.
Proof. vm_refl. Qed.
Lemma D_9b6bc : decode_any W_9b6bc = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b6c0 : bv 32 := 0x01213023.
Lemma F_9b6c0 : fetch_word Plain.M.loaded_segments (0x9b718 : word) = Some W_9b6c0.
Proof. vm_refl. Qed.
Lemma D_9b6c0 : decode_any W_9b6c0 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b6c4 : bv 32 := 0x00060413.
Lemma F_9b6c4 : fetch_word Plain.M.loaded_segments (0x9b71c : word) = Some W_9b6c4.
Proof. vm_refl. Qed.
Lemma D_9b6c4 : decode_any W_9b6c4 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b6c8 : bv 32 := 0x00058493.
Lemma F_9b6c8 : fetch_word Plain.M.loaded_segments (0x9b720 : word) = Some W_9b6c8.
Proof. vm_refl. Qed.
Lemma D_9b6c8 : decode_any W_9b6c8 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b6cc : bv 32 := 0x00050913.
Lemma F_9b6cc : fetch_word Plain.M.loaded_segments (0x9b724 : word) = Some W_9b6cc.
Proof. vm_refl. Qed.
Lemma D_9b6cc : decode_any W_9b6cc = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b6d0 : bv 32 := 0x00063583.
Lemma F_9b6d0 : fetch_word Plain.M.loaded_segments (0x9b728 : word) = Some W_9b6d0.
Proof. vm_refl. Qed.
Lemma D_9b6d0 : decode_any W_9b6d0 = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b6d4 : bv 32 := 0x00349513.
Lemma F_9b6d4 : fetch_word Plain.M.loaded_segments (0x9b72c : word) = Some W_9b6d4.
Proof. vm_refl. Qed.
Lemma D_9b6d4 : decode_any W_9b6d4 = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b6d8 : bv 32 := 0x00a60533.
Lemma F_9b6d8 : fetch_word Plain.M.loaded_segments (0x9b730 : word) = Some W_9b6d8.
Proof. vm_refl. Qed.
Lemma D_9b6d8 : decode_any W_9b6d8 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b6dc : bv 32 := 0x00850513.
Lemma F_9b6dc : fetch_word Plain.M.loaded_segments (0x9b734 : word) = Some W_9b6dc.
Proof. vm_refl. Qed.
Lemma D_9b6dc : decode_any W_9b6dc = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b6e0 : bv 32 := 0xd59ff0ef.
Lemma F_9b6e0 : fetch_word Plain.M.loaded_segments (0x9b738 : word) = Some W_9b6e0.
Proof. vm_refl. Qed.
Lemma D_9b6e0 : decode_any W_9b6e0 = Some (Jal 1 2096472, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b6e4 : bv 32 := 0x00000517.
Lemma F_9b6e4 : fetch_word Plain.M.loaded_segments (0x9b73c : word) = Some W_9b6e4.
Proof. vm_refl. Qed.
Lemma D_9b6e4 : decode_any W_9b6e4 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b6e8 : bv 32 := 0x02c50313.
Lemma F_9b6e8 : fetch_word Plain.M.loaded_segments (0x9b740 : word) = Some W_9b6e8.
Proof. vm_refl. Qed.
Lemma D_9b6e8 : decode_any W_9b6e8 = Some (OpImm ALU_ADD 6 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b6ec : bv 32 := 0x00090513.
Lemma F_9b6ec : fetch_word Plain.M.loaded_segments (0x9b744 : word) = Some W_9b6ec.
Proof. vm_refl. Qed.
Lemma D_9b6ec : decode_any W_9b6ec = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b6f0 : bv 32 := 0x00048593.
Lemma F_9b6f0 : fetch_word Plain.M.loaded_segments (0x9b748 : word) = Some W_9b6f0.
Proof. vm_refl. Qed.
Lemma D_9b6f0 : decode_any W_9b6f0 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b6f4 : bv 32 := 0x00040613.
Lemma F_9b6f4 : fetch_word Plain.M.loaded_segments (0x9b74c : word) = Some W_9b6f4.
Proof. vm_refl. Qed.
Lemma D_9b6f4 : decode_any W_9b6f4 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b6f8 : bv 32 := 0x01813083.
Lemma F_9b6f8 : fetch_word Plain.M.loaded_segments (0x9b750 : word) = Some W_9b6f8.
Proof. vm_refl. Qed.
Lemma D_9b6f8 : decode_any W_9b6f8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b6fc : bv 32 := 0x01013403.
Lemma F_9b6fc : fetch_word Plain.M.loaded_segments (0x9b754 : word) = Some W_9b6fc.
Proof. vm_refl. Qed.
Lemma D_9b6fc : decode_any W_9b6fc = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b700 : bv 32 := 0x00813483.
Lemma F_9b700 : fetch_word Plain.M.loaded_segments (0x9b758 : word) = Some W_9b700.
Proof. vm_refl. Qed.
Lemma D_9b700 : decode_any W_9b700 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b704 : bv 32 := 0x00013903.
Lemma F_9b704 : fetch_word Plain.M.loaded_segments (0x9b75c : word) = Some W_9b704.
Proof. vm_refl. Qed.
Lemma D_9b704 : decode_any W_9b704 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b708 : bv 32 := 0x02010113.
Lemma F_9b708 : fetch_word Plain.M.loaded_segments (0x9b760 : word) = Some W_9b708.
Proof. vm_refl. Qed.
Lemma D_9b708 : decode_any W_9b708 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b70c : bv 32 := 0x00030067.
Lemma F_9b70c : fetch_word Plain.M.loaded_segments (0x9b764 : word) = Some W_9b70c.
Proof. vm_refl. Qed.
Lemma D_9b70c : decode_any W_9b70c = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b710 : bv 32 := 0xfd010113.
Lemma F_9b710 : fetch_word Plain.M.loaded_segments (0x9b768 : word) = Some W_9b710.
Proof. vm_refl. Qed.
Lemma D_9b710 : decode_any W_9b710 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b714 : bv 32 := 0x02113423.
Lemma F_9b714 : fetch_word Plain.M.loaded_segments (0x9b76c : word) = Some W_9b714.
Proof. vm_refl. Qed.
Lemma D_9b714 : decode_any W_9b714 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b718 : bv 32 := 0x02813023.
Lemma F_9b718 : fetch_word Plain.M.loaded_segments (0x9b770 : word) = Some W_9b718.
Proof. vm_refl. Qed.
Lemma D_9b718 : decode_any W_9b718 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b71c : bv 32 := 0x00913c23.
Lemma F_9b71c : fetch_word Plain.M.loaded_segments (0x9b774 : word) = Some W_9b71c.
Proof. vm_refl. Qed.
Lemma D_9b71c : decode_any W_9b71c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b720 : bv 32 := 0x01213823.
Lemma F_9b720 : fetch_word Plain.M.loaded_segments (0x9b778 : word) = Some W_9b720.
Proof. vm_refl. Qed.
Lemma D_9b720 : decode_any W_9b720 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b724 : bv 32 := 0x01313423.
Lemma F_9b724 : fetch_word Plain.M.loaded_segments (0x9b77c : word) = Some W_9b724.
Proof. vm_refl. Qed.
Lemma D_9b724 : decode_any W_9b724 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b728 : bv 32 := 0x00060413.
Lemma F_9b728 : fetch_word Plain.M.loaded_segments (0x9b780 : word) = Some W_9b728.
Proof. vm_refl. Qed.
Lemma D_9b728 : decode_any W_9b728 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b72c : bv 32 := 0x00058493.
Lemma F_9b72c : fetch_word Plain.M.loaded_segments (0x9b784 : word) = Some W_9b72c.
Proof. vm_refl. Qed.
Lemma D_9b72c : decode_any W_9b72c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b730 : bv 32 := 0x00050913.
Lemma F_9b730 : fetch_word Plain.M.loaded_segments (0x9b788 : word) = Some W_9b730.
Proof. vm_refl. Qed.
Lemma D_9b730 : decode_any W_9b730 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b734 : bv 32 := 0x00359513.
Lemma F_9b734 : fetch_word Plain.M.loaded_segments (0x9b78c : word) = Some W_9b734.
Proof. vm_refl. Qed.
Lemma D_9b734 : decode_any W_9b734 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b738 : bv 32 := 0x00a60533.
Lemma F_9b738 : fetch_word Plain.M.loaded_segments (0x9b790 : word) = Some W_9b738.
Proof. vm_refl. Qed.
Lemma D_9b738 : decode_any W_9b738 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b73c : bv 32 := 0x00850993.
Lemma F_9b73c : fetch_word Plain.M.loaded_segments (0x9b794 : word) = Some W_9b73c.
Proof. vm_refl. Qed.
Lemma D_9b73c : decode_any W_9b73c = Some (OpImm ALU_ADD 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b740 : bv 32 := 0xf25ff0ef.
Lemma F_9b740 : fetch_word Plain.M.loaded_segments (0x9b798 : word) = Some W_9b740.
Proof. vm_refl. Qed.
Lemma D_9b740 : decode_any W_9b740 = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b744 : bv 32 := 0x00048513.
Lemma F_9b744 : fetch_word Plain.M.loaded_segments (0x9b79c : word) = Some W_9b744.
Proof. vm_refl. Qed.
Lemma D_9b744 : decode_any W_9b744 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b748 : bv 32 := 0x00040593.
Lemma F_9b748 : fetch_word Plain.M.loaded_segments (0x9b7a0 : word) = Some W_9b748.
Proof. vm_refl. Qed.
Lemma D_9b748 : decode_any W_9b748 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b74c : bv 32 := 0x00098613.
Lemma F_9b74c : fetch_word Plain.M.loaded_segments (0x9b7a4 : word) = Some W_9b74c.
Proof. vm_refl. Qed.
Lemma D_9b74c : decode_any W_9b74c = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b750 : bv 32 := 0x000900e7.
Lemma F_9b750 : fetch_word Plain.M.loaded_segments (0x9b7a8 : word) = Some W_9b750.
Proof. vm_refl. Qed.
Lemma D_9b750 : decode_any W_9b750 = Some (Jalr 1 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b758 : bv 32 := 0xfc010113.
Lemma F_9b758 : fetch_word Plain.M.loaded_segments (0x9b7b0 : word) = Some W_9b758.
Proof. vm_refl. Qed.
Lemma D_9b758 : decode_any W_9b758 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b75c : bv 32 := 0x02113c23.
Lemma F_9b75c : fetch_word Plain.M.loaded_segments (0x9b7b4 : word) = Some W_9b75c.
Proof. vm_refl. Qed.
Lemma D_9b75c : decode_any W_9b75c = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b760 : bv 32 := 0x02813823.
Lemma F_9b760 : fetch_word Plain.M.loaded_segments (0x9b7b8 : word) = Some W_9b760.
Proof. vm_refl. Qed.
Lemma D_9b760 : decode_any W_9b760 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b764 : bv 32 := 0x02913423.
Lemma F_9b764 : fetch_word Plain.M.loaded_segments (0x9b7bc : word) = Some W_9b764.
Proof. vm_refl. Qed.
Lemma D_9b764 : decode_any W_9b764 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b768 : bv 32 := 0x03213023.
Lemma F_9b768 : fetch_word Plain.M.loaded_segments (0x9b7c0 : word) = Some W_9b768.
Proof. vm_refl. Qed.
Lemma D_9b768 : decode_any W_9b768 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b76c : bv 32 := 0x01313c23.
Lemma F_9b76c : fetch_word Plain.M.loaded_segments (0x9b7c4 : word) = Some W_9b76c.
Proof. vm_refl. Qed.
Lemma D_9b76c : decode_any W_9b76c = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b770 : bv 32 := 0x01413823.
Lemma F_9b770 : fetch_word Plain.M.loaded_segments (0x9b7c8 : word) = Some W_9b770.
Proof. vm_refl. Qed.
Lemma D_9b770 : decode_any W_9b770 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b774 : bv 32 := 0x01513423.
Lemma F_9b774 : fetch_word Plain.M.loaded_segments (0x9b7cc : word) = Some W_9b774.
Proof. vm_refl. Qed.
Lemma D_9b774 : decode_any W_9b774 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b778 : bv 32 := 0x02853683.
Lemma F_9b778 : fetch_word Plain.M.loaded_segments (0x9b7d0 : word) = Some W_9b778.
Proof. vm_refl. Qed.
Lemma D_9b778 : decode_any W_9b778 = Some (Load SZ8 true 13 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b77c : bv 32 := 0x00050597.
Lemma F_9b77c : fetch_word Plain.M.loaded_segments (0x9b7d4 : word) = Some W_9b77c.
Proof. vm_refl. Qed.
Lemma D_9b77c : decode_any W_9b77c = Some (Auipc 11 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b78c : bv 32 := 0x0c068e63.
Lemma F_9b78c : fetch_word Plain.M.loaded_segments (0x9b7e4 : word) = Some W_9b78c.
Proof. vm_refl. Qed.
Lemma D_9b78c : decode_any W_9b78c = Some (Branch BC_EQ 13 0 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b794 : bv 32 := 0x00000893.
Lemma F_9b794 : fetch_word Plain.M.loaded_segments (0x9b7ec : word) = Some W_9b794.
Proof. vm_refl. Qed.
Lemma D_9b794 : decode_any W_9b794 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b798 : bv 32 := 0x0001e717.
Lemma F_9b798 : fetch_word Plain.M.loaded_segments (0x9b7f0 : word) = Some W_9b798.
Proof. vm_refl. Qed.
Lemma D_9b798 : decode_any W_9b798 = Some (Auipc 14 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b79c : bv 32 := 0x01853783.
Lemma F_9b79c : fetch_word Plain.M.loaded_segments (0x9b7f4 : word) = Some W_9b79c.
Proof. vm_refl. Qed.
Lemma D_9b79c : decode_any W_9b79c = Some (Load SZ8 true 15 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b7a0 : bv 32 := 0x02053503.
Lemma F_9b7a0 : fetch_word Plain.M.loaded_segments (0x9b7f8 : word) = Some W_9b7a0.
Proof. vm_refl. Qed.
Lemma D_9b7a0 : decode_any W_9b7a0 = Some (Load SZ8 true 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b7a4 : bv 32 := 0x00600813.
Lemma F_9b7a4 : fetch_word Plain.M.loaded_segments (0x9b7fc : word) = Some W_9b7a4.
Proof. vm_refl. Qed.
Lemma D_9b7a4 : decode_any W_9b7a4 = Some (OpImm ALU_ADD 16 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b7a8 : bv 32 := 0x0001d297.
Lemma F_9b7a8 : fetch_word Plain.M.loaded_segments (0x9b800 : word) = Some W_9b7a8.
Proof. vm_refl. Qed.
Lemma D_9b7a8 : decode_any W_9b7a8 = Some (Auipc 5 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b7ac : bv 32 := 0xda876f03.
Lemma F_9b7ac : fetch_word Plain.M.loaded_segments (0x9b804 : word) = Some W_9b7ac.
Proof. vm_refl. Qed.
Lemma D_9b7ac : decode_any W_9b7ac = Some (Load SZ4 false 30 14 3496, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b7b0 : bv 32 := 0x9102b283.
Lemma F_9b7b0 : fetch_word Plain.M.loaded_segments (0x9b808 : word) = Some W_9b7b0.
Proof. vm_refl. Qed.
Lemma D_9b7b0 : decode_any W_9b7b0 = Some (Load SZ8 true 5 5 2320, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b7b4 : bv 32 := 0x00200313.
Lemma F_9b7b4 : fetch_word Plain.M.loaded_segments (0x9b80c : word) = Some W_9b7b4.
Proof. vm_refl. Qed.
Lemma D_9b7b4 : decode_any W_9b7b4 = Some (OpImm ALU_ADD 6 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b7b8 : bv 32 := 0x00700393.
Lemma F_9b7b8 : fetch_word Plain.M.loaded_segments (0x9b810 : word) = Some W_9b7b8.
Proof. vm_refl. Qed.
Lemma D_9b7b8 : decode_any W_9b7b8 = Some (OpImm ALU_ADD 7 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b7bc : bv 32 := 0x6474ee37.
Lemma F_9b7bc : fetch_word Plain.M.loaded_segments (0x9b814 : word) = Some W_9b7bc.
Proof. vm_refl. Qed.
Lemma D_9b7bc : decode_any W_9b7bc = Some (Lui 28 411470, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b7c0 : bv 32 := 0x551e0e1b.
Lemma F_9b7c0 : fetch_word Plain.M.loaded_segments (0x9b818 : word) = Some W_9b7c0.
Proof. vm_refl. Qed.
Lemma D_9b7c0 : decode_any W_9b7c0 = Some (OpImm32 28 28 1361, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b7c4 : bv 32 := 0x00078e93.
Lemma F_9b7c4 : fetch_word Plain.M.loaded_segments (0x9b81c : word) = Some W_9b7c4.
Proof. vm_refl. Qed.
Lemma D_9b7c4 : decode_any W_9b7c4 = Some (OpImm ALU_ADD 29 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b7c8 : bv 32 := 0x0180006f.
Lemma F_9b7c8 : fetch_word Plain.M.loaded_segments (0x9b820 : word) = Some W_9b7c8.
Proof. vm_refl. Qed.
Lemma D_9b7c8 : decode_any W_9b7c8 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b7d4 : bv 32 := 0xfff68693.
Lemma F_9b7d4 : fetch_word Plain.M.loaded_segments (0x9b82c : word) = Some W_9b7d4.
Proof. vm_refl. Qed.
Lemma D_9b7d4 : decode_any W_9b7d4 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b7d8 : bv 32 := 0x00ae8eb3.
Lemma F_9b7d8 : fetch_word Plain.M.loaded_segments (0x9b830 : word) = Some W_9b7d8.
Proof. vm_refl. Qed.
Lemma D_9b7d8 : decode_any W_9b7d8 = Some (Op ALU_ADD 29 29 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b7dc : bv 32 := 0x04068a63.
Lemma F_9b7dc : fetch_word Plain.M.loaded_segments (0x9b834 : word) = Some W_9b7dc.
Proof. vm_refl. Qed.
Lemma D_9b7dc : decode_any W_9b7dc = Some (Branch BC_EQ 13 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b7e0 : bv 32 := 0x000ea403.
Lemma F_9b7e0 : fetch_word Plain.M.loaded_segments (0x9b838 : word) = Some W_9b7e0.
Proof. vm_refl. Qed.
Lemma D_9b7e0 : decode_any W_9b7e0 = Some (Load SZ4 true 8 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b7e4 : bv 32 := 0xff0404e3.
Lemma F_9b7e4 : fetch_word Plain.M.loaded_segments (0x9b83c : word) = Some W_9b7e4.
Proof. vm_refl. Qed.
Lemma D_9b7e4 : decode_any W_9b7e4 = Some (Branch BC_EQ 8 16 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b7e8 : bv 32 := 0x00028a63.
Lemma F_9b7e8 : fetch_word Plain.M.loaded_segments (0x9b840 : word) = Some W_9b7e8.
Proof. vm_refl. Qed.
Lemma D_9b7e8 : decode_any W_9b7e8 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b7fc : bv 32 := 0x000e8f93.
Lemma F_9b7fc : fetch_word Plain.M.loaded_segments (0x9b854 : word) = Some W_9b7fc.
Proof. vm_refl. Qed.
Lemma D_9b7fc : decode_any W_9b7fc = Some (OpImm ALU_ADD 31 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b800 : bv 32 := 0x00740463.
Lemma F_9b800 : fetch_word Plain.M.loaded_segments (0x9b858 : word) = Some W_9b800.
Proof. vm_refl. Qed.
Lemma D_9b800 : decode_any W_9b800 = Some (Branch BC_EQ 8 7 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b804 : bv 32 := 0x00088f93.
Lemma F_9b804 : fetch_word Plain.M.loaded_segments (0x9b85c : word) = Some W_9b804.
Proof. vm_refl. Qed.
Lemma D_9b804 : decode_any W_9b804 = Some (OpImm ALU_ADD 31 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b808 : bv 32 := 0x03c41063.
Lemma F_9b808 : fetch_word Plain.M.loaded_segments (0x9b860 : word) = Some W_9b808.
Proof. vm_refl. Qed.
Lemma D_9b808 : decode_any W_9b808 = Some (Branch BC_NE 8 28 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b80c : bv 32 := 0x028eb883.
Lemma F_9b80c : fetch_word Plain.M.loaded_segments (0x9b864 : word) = Some W_9b80c.
Proof. vm_refl. Qed.
Lemma D_9b80c : decode_any W_9b80c = Some (Load SZ8 true 17 29 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b810 : bv 32 := 0x011f7c63.
Lemma F_9b810 : fetch_word Plain.M.loaded_segments (0x9b868 : word) = Some W_9b810.
Proof. vm_refl. Qed.
Lemma D_9b810 : decode_any W_9b810 = Some (Branch BC_GEU 30 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b828 : bv 32 := 0x000f8893.
Lemma F_9b828 : fetch_word Plain.M.loaded_segments (0x9b880 : word) = Some W_9b828.
Proof. vm_refl. Qed.
Lemma D_9b828 : decode_any W_9b828 = Some (OpImm ALU_ADD 17 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b82c : bv 32 := 0xfa9ff06f.
Lemma F_9b82c : fetch_word Plain.M.loaded_segments (0x9b884 : word) = Some W_9b82c.
Proof. vm_refl. Qed.
Lemma D_9b82c : decode_any W_9b82c = Some (Jal 0 2097064, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b830 : bv 32 := 0x02088c63.
Lemma F_9b830 : fetch_word Plain.M.loaded_segments (0x9b888 : word) = Some W_9b830.
Proof. vm_refl. Qed.
Lemma D_9b830 : decode_any W_9b830 = Some (Branch BC_EQ 17 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b878 : bv 32 := 0xfff50793.
Lemma F_9b878 : fetch_word Plain.M.loaded_segments (0x9b8d0 : word) = Some W_9b878.
Proof. vm_refl. Qed.
Lemma D_9b878 : decode_any W_9b878 = Some (OpImm ALU_ADD 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b87c : bv 32 := 0x40e00733.
Lemma F_9b87c : fetch_word Plain.M.loaded_segments (0x9b8d4 : word) = Some W_9b87c.
Proof. vm_refl. Qed.
Lemma D_9b87c : decode_any W_9b87c = Some (Op ALU_SUB 14 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b884 : bv 32 := 0x00e7f733.
Lemma F_9b884 : fetch_word Plain.M.loaded_segments (0x9b8dc : word) = Some W_9b884.
Proof. vm_refl. Qed.
Lemma D_9b884 : decode_any W_9b884 = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b888 : bv 32 := 0x00700793.
Lemma F_9b888 : fetch_word Plain.M.loaded_segments (0x9b8e0 : word) = Some W_9b888.
Proof. vm_refl. Qed.
Lemma D_9b888 : decode_any W_9b888 = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b88c : bv 32 := 0x00d706b3.
Lemma F_9b88c : fetch_word Plain.M.loaded_segments (0x9b8e4 : word) = Some W_9b88c.
Proof. vm_refl. Qed.
Lemma D_9b88c : decode_any W_9b88c = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b898 : bv 32 := 0x00a7e663.
Lemma F_9b898 : fetch_word Plain.M.loaded_segments (0x9b8f0 : word) = Some W_9b898.
Proof. vm_refl. Qed.
Lemma D_9b898 : decode_any W_9b898 = Some (Branch BC_LTU 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b89c : bv 32 := 0x00800513.
Lemma F_9b89c : fetch_word Plain.M.loaded_segments (0x9b8f4 : word) = Some W_9b89c.
Proof. vm_refl. Qed.
Lemma D_9b89c : decode_any W_9b89c = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b8b4 : bv 32 := 0xff85f593.
Lemma F_9b8b4 : fetch_word Plain.M.loaded_segments (0x9b910 : word) = Some W_9b8b4.
Proof. vm_refl. Qed.
Lemma D_9b8b4 : decode_any W_9b8b4 = Some (OpImm ALU_AND 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b8b8 : bv 32 := 0x00b4bc23.
Lemma F_9b8b8 : fetch_word Plain.M.loaded_segments (0x9b914 : word) = Some W_9b8b8.
Proof. vm_refl. Qed.
Lemma D_9b8b8 : decode_any W_9b8b8 = Some (Store SZ8 9 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b8bc : bv 32 := 0x02a4b023.
Lemma F_9b8bc : fetch_word Plain.M.loaded_segments (0x9b918 : word) = Some W_9b8bc.
Proof. vm_refl. Qed.
Lemma D_9b8bc : decode_any W_9b8bc = Some (Store SZ8 9 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b8c0 : bv 32 := 0x02d5ea63.
Lemma F_9b8c0 : fetch_word Plain.M.loaded_segments (0x9b91c : word) = Some W_9b8c0.
Proof. vm_refl. Qed.
Lemma D_9b8c0 : decode_any W_9b8c0 = Some (Branch BC_LTU 11 13 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b90c : bv 32 := 0x0284b603.
Lemma F_9b90c : fetch_word Plain.M.loaded_segments (0x9b958 : word) = Some W_9b90c.
Proof. vm_refl. Qed.
Lemma D_9b90c : decode_any W_9b90c = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b938 : bv 32 := 0x0c890413.
Lemma F_9b938 : fetch_word Plain.M.loaded_segments (0x9b984 : word) = Some W_9b938.
Proof. vm_refl. Qed.
Lemma D_9b938 : decode_any W_9b938 = Some (OpImm ALU_ADD 8 18 200, 4%Z).
Proof. vm_refl. Qed.
