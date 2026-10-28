(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_aa574 : bv 32 := 0xf9010113.
Lemma F_aa574 : fetch_word Ubsan.M.loaded_segments (0xac404 : word) = Some W_aa574.
Proof. vm_refl. Qed.
Lemma D_aa574 : decode_any W_aa574 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa578 : bv 32 := 0x06113423.
Lemma F_aa578 : fetch_word Ubsan.M.loaded_segments (0xac408 : word) = Some W_aa578.
Proof. vm_refl. Qed.
Lemma D_aa578 : decode_any W_aa578 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa57c : bv 32 := 0x06813023.
Lemma F_aa57c : fetch_word Ubsan.M.loaded_segments (0xac40c : word) = Some W_aa57c.
Proof. vm_refl. Qed.
Lemma D_aa57c : decode_any W_aa57c = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa580 : bv 32 := 0x04913c23.
Lemma F_aa580 : fetch_word Ubsan.M.loaded_segments (0xac410 : word) = Some W_aa580.
Proof. vm_refl. Qed.
Lemma D_aa580 : decode_any W_aa580 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa584 : bv 32 := 0x05213823.
Lemma F_aa584 : fetch_word Ubsan.M.loaded_segments (0xac414 : word) = Some W_aa584.
Proof. vm_refl. Qed.
Lemma D_aa584 : decode_any W_aa584 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa588 : bv 32 := 0x05313423.
Lemma F_aa588 : fetch_word Ubsan.M.loaded_segments (0xac418 : word) = Some W_aa588.
Proof. vm_refl. Qed.
Lemma D_aa588 : decode_any W_aa588 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa58c : bv 32 := 0x05413023.
Lemma F_aa58c : fetch_word Ubsan.M.loaded_segments (0xac41c : word) = Some W_aa58c.
Proof. vm_refl. Qed.
Lemma D_aa58c : decode_any W_aa58c = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa590 : bv 32 := 0x03513c23.
Lemma F_aa590 : fetch_word Ubsan.M.loaded_segments (0xac420 : word) = Some W_aa590.
Proof. vm_refl. Qed.
Lemma D_aa590 : decode_any W_aa590 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa594 : bv 32 := 0x03613823.
Lemma F_aa594 : fetch_word Ubsan.M.loaded_segments (0xac424 : word) = Some W_aa594.
Proof. vm_refl. Qed.
Lemma D_aa594 : decode_any W_aa594 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa598 : bv 32 := 0x00060413.
Lemma F_aa598 : fetch_word Ubsan.M.loaded_segments (0xac428 : word) = Some W_aa598.
Proof. vm_refl. Qed.
Lemma D_aa598 : decode_any W_aa598 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa59c : bv 32 := 0x00050493.
Lemma F_aa59c : fetch_word Ubsan.M.loaded_segments (0xac42c : word) = Some W_aa59c.
Proof. vm_refl. Qed.
Lemma D_aa59c : decode_any W_aa59c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa5a0 : bv 32 := 0x00017517.
Lemma F_aa5a0 : fetch_word Ubsan.M.loaded_segments (0xac430 : word) = Some W_aa5a0.
Proof. vm_refl. Qed.
Lemma D_aa5a0 : decode_any W_aa5a0 = Some (Auipc 10 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa5a4 : bv 32 := 0x61853a83.
Lemma F_aa5a4 : fetch_word Ubsan.M.loaded_segments (0xac434 : word) = Some W_aa5a4.
Proof. vm_refl. Qed.
Lemma D_aa5a4 : decode_any W_aa5a4 = Some (Load SZ8 true 21 10 1560, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa5a8 : bv 32 := 0x000ab503.
Lemma F_aa5a8 : fetch_word Ubsan.M.loaded_segments (0xac438 : word) = Some W_aa5a8.
Proof. vm_refl. Qed.
Lemma D_aa5a8 : decode_any W_aa5a8 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa5ac : bv 32 := 0x02a13423.
Lemma F_aa5ac : fetch_word Ubsan.M.loaded_segments (0xac43c : word) = Some W_aa5ac.
Proof. vm_refl. Qed.
Lemma D_aa5ac : decode_any W_aa5ac = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa5b0 : bv 32 := 0x0284b503.
Lemma F_aa5b0 : fetch_word Ubsan.M.loaded_segments (0xac440 : word) = Some W_aa5b0.
Proof. vm_refl. Qed.
Lemma D_aa5b0 : decode_any W_aa5b0 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa5b4 : bv 32 := 0x0384b603.
Lemma F_aa5b4 : fetch_word Ubsan.M.loaded_segments (0xac444 : word) = Some W_aa5b4.
Proof. vm_refl. Qed.
Lemma D_aa5b4 : decode_any W_aa5b4 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa5b8 : bv 32 := 0x40c50b33.
Lemma F_aa5b8 : fetch_word Ubsan.M.loaded_segments (0xac448 : word) = Some W_aa5b8.
Proof. vm_refl. Qed.
Lemma D_aa5b8 : decode_any W_aa5b8 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa5bc : bv 32 := 0x00c546b3.
Lemma F_aa5bc : fetch_word Ubsan.M.loaded_segments (0xac44c : word) = Some W_aa5bc.
Proof. vm_refl. Qed.
Lemma D_aa5bc : decode_any W_aa5bc = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa5c0 : bv 32 := 0x00c13423.
Lemma F_aa5c0 : fetch_word Ubsan.M.loaded_segments (0xac450 : word) = Some W_aa5c0.
Proof. vm_refl. Qed.
Lemma D_aa5c0 : decode_any W_aa5c0 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa5c4 : bv 32 := 0x01613823.
Lemma F_aa5c4 : fetch_word Ubsan.M.loaded_segments (0xac454 : word) = Some W_aa5c4.
Proof. vm_refl. Qed.
Lemma D_aa5c4 : decode_any W_aa5c4 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa5c8 : bv 32 := 0x00b13c23.
Lemma F_aa5c8 : fetch_word Ubsan.M.loaded_segments (0xac458 : word) = Some W_aa5c8.
Proof. vm_refl. Qed.
Lemma D_aa5c8 : decode_any W_aa5c8 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa5cc : bv 32 := 0x02813023.
Lemma F_aa5cc : fetch_word Ubsan.M.loaded_segments (0xac45c : word) = Some W_aa5cc.
Proof. vm_refl. Qed.
Lemma D_aa5cc : decode_any W_aa5cc = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa5d0 : bv 32 := 0x008b0b33.
Lemma F_aa5d0 : fetch_word Ubsan.M.loaded_segments (0xac460 : word) = Some W_aa5d0.
Proof. vm_refl. Qed.
Lemma D_aa5d0 : decode_any W_aa5d0 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa5d4 : bv 32 := 0x00d03933.
Lemma F_aa5d4 : fetch_word Ubsan.M.loaded_segments (0xac464 : word) = Some W_aa5d4.
Proof. vm_refl. Qed.
Lemma D_aa5d4 : decode_any W_aa5d4 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa5d8 : bv 32 := 0x00c50663.
Lemma F_aa5d8 : fetch_word Ubsan.M.loaded_segments (0xac468 : word) = Some W_aa5d8.
Proof. vm_refl. Qed.
Lemma D_aa5d8 : decode_any W_aa5d8 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa5dc : bv 32 := 0x00810993.
Lemma F_aa5dc : fetch_word Ubsan.M.loaded_segments (0xac46c : word) = Some W_aa5dc.
Proof. vm_refl. Qed.
Lemma D_aa5dc : decode_any W_aa5dc = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa5e0 : bv 32 := 0x0080006f.
Lemma F_aa5e0 : fetch_word Ubsan.M.loaded_segments (0xac470 : word) = Some W_aa5e0.
Proof. vm_refl. Qed.
Lemma D_aa5e0 : decode_any W_aa5e0 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa5e4 : bv 32 := 0x01810993.
Lemma F_aa5e4 : fetch_word Ubsan.M.loaded_segments (0xac474 : word) = Some W_aa5e4.
Proof. vm_refl. Qed.
Lemma D_aa5e4 : decode_any W_aa5e4 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa5e8 : bv 32 := 0x0784a503.
Lemma F_aa5e8 : fetch_word Ubsan.M.loaded_segments (0xac478 : word) = Some W_aa5e8.
Proof. vm_refl. Qed.
Lemma D_aa5e8 : decode_any W_aa5e8 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa5ec : bv 32 := 0x00190913.
Lemma F_aa5ec : fetch_word Ubsan.M.loaded_segments (0xac47c : word) = Some W_aa5ec.
Proof. vm_refl. Qed.
Lemma D_aa5ec : decode_any W_aa5ec = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa5f0 : bv 32 := 0x04200893.
Lemma F_aa5f0 : fetch_word Ubsan.M.loaded_segments (0xac480 : word) = Some W_aa5f0.
Proof. vm_refl. Qed.
Lemma D_aa5f0 : decode_any W_aa5f0 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa5f4 : bv 32 := 0x00098593.
Lemma F_aa5f4 : fetch_word Ubsan.M.loaded_segments (0xac484 : word) = Some W_aa5f4.
Proof. vm_refl. Qed.
Lemma D_aa5f4 : decode_any W_aa5f4 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa5f8 : bv 32 := 0x00090613.
Lemma F_aa5f8 : fetch_word Ubsan.M.loaded_segments (0xac488 : word) = Some W_aa5f8.
Proof. vm_refl. Qed.
Lemma D_aa5f8 : decode_any W_aa5f8 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa5fc : bv 32 := 0x00000073.
Lemma F_aa5fc : fetch_word Ubsan.M.loaded_segments (0xac48c : word) = Some W_aa5fc.
Proof. vm_refl. Qed.
Lemma D_aa5fc : decode_any W_aa5fc = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_aa5fc : is_ecall W_aa5fc = true.
Proof. reflexivity. Qed.

Definition W_aa600 : bv 32 := 0xe91fa0ef.
Lemma F_aa600 : fetch_word Ubsan.M.loaded_segments (0xac490 : word) = Some W_aa600.
Proof. vm_refl. Qed.
Lemma D_aa600 : decode_any W_aa600 = Some (Jal 1 2076304, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa604 : bv 32 := 0x09651863.
Lemma F_aa604 : fetch_word Ubsan.M.loaded_segments (0xac494 : word) = Some W_aa604.
Proof. vm_refl. Qed.
Lemma D_aa604 : decode_any W_aa604 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa608 : bv 32 := 0x0584b503.
Lemma F_aa608 : fetch_word Ubsan.M.loaded_segments (0xac498 : word) = Some W_aa608.
Proof. vm_refl. Qed.
Lemma D_aa608 : decode_any W_aa608 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa60c : bv 32 := 0x0604b583.
Lemma F_aa60c : fetch_word Ubsan.M.loaded_segments (0xac49c : word) = Some W_aa60c.
Proof. vm_refl. Qed.
Lemma D_aa60c : decode_any W_aa60c = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa610 : bv 32 := 0x00b505b3.
Lemma F_aa610 : fetch_word Ubsan.M.loaded_segments (0xac4a0 : word) = Some W_aa610.
Proof. vm_refl. Qed.
Lemma D_aa610 : decode_any W_aa610 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa614 : bv 32 := 0x02b4b023.
Lemma F_aa614 : fetch_word Ubsan.M.loaded_segments (0xac4a4 : word) = Some W_aa614.
Proof. vm_refl. Qed.
Lemma D_aa614 : decode_any W_aa614 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa618 : bv 32 := 0x02a4b423.
Lemma F_aa618 : fetch_word Ubsan.M.loaded_segments (0xac4a8 : word) = Some W_aa618.
Proof. vm_refl. Qed.
Lemma D_aa618 : decode_any W_aa618 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa61c : bv 32 := 0x02a4bc23.
Lemma F_aa61c : fetch_word Ubsan.M.loaded_segments (0xac4ac : word) = Some W_aa61c.
Proof. vm_refl. Qed.
Lemma D_aa61c : decode_any W_aa61c = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa620 : bv 32 := 0x00040513.
Lemma F_aa620 : fetch_word Ubsan.M.loaded_segments (0xac4b0 : word) = Some W_aa620.
Proof. vm_refl. Qed.
Lemma D_aa620 : decode_any W_aa620 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa624 : bv 32 := 0x000ab583.
Lemma F_aa624 : fetch_word Ubsan.M.loaded_segments (0xac4b4 : word) = Some W_aa624.
Proof. vm_refl. Qed.
Lemma D_aa624 : decode_any W_aa624 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa628 : bv 32 := 0x02813603.
Lemma F_aa628 : fetch_word Ubsan.M.loaded_segments (0xac4b8 : word) = Some W_aa628.
Proof. vm_refl. Qed.
Lemma D_aa628 : decode_any W_aa628 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa62c : bv 32 := 0x0cc59a63.
Lemma F_aa62c : fetch_word Ubsan.M.loaded_segments (0xac4bc : word) = Some W_aa62c.
Proof. vm_refl. Qed.
Lemma D_aa62c : decode_any W_aa62c = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa630 : bv 32 := 0x06813083.
Lemma F_aa630 : fetch_word Ubsan.M.loaded_segments (0xac4c0 : word) = Some W_aa630.
Proof. vm_refl. Qed.
Lemma D_aa630 : decode_any W_aa630 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa634 : bv 32 := 0x06013403.
Lemma F_aa634 : fetch_word Ubsan.M.loaded_segments (0xac4c4 : word) = Some W_aa634.
Proof. vm_refl. Qed.
Lemma D_aa634 : decode_any W_aa634 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa638 : bv 32 := 0x05813483.
Lemma F_aa638 : fetch_word Ubsan.M.loaded_segments (0xac4c8 : word) = Some W_aa638.
Proof. vm_refl. Qed.
Lemma D_aa638 : decode_any W_aa638 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa63c : bv 32 := 0x05013903.
Lemma F_aa63c : fetch_word Ubsan.M.loaded_segments (0xac4cc : word) = Some W_aa63c.
Proof. vm_refl. Qed.
Lemma D_aa63c : decode_any W_aa63c = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa640 : bv 32 := 0x04813983.
Lemma F_aa640 : fetch_word Ubsan.M.loaded_segments (0xac4d0 : word) = Some W_aa640.
Proof. vm_refl. Qed.
Lemma D_aa640 : decode_any W_aa640 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa644 : bv 32 := 0x04013a03.
Lemma F_aa644 : fetch_word Ubsan.M.loaded_segments (0xac4d4 : word) = Some W_aa644.
Proof. vm_refl. Qed.
Lemma D_aa644 : decode_any W_aa644 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa648 : bv 32 := 0x03813a83.
Lemma F_aa648 : fetch_word Ubsan.M.loaded_segments (0xac4d8 : word) = Some W_aa648.
Proof. vm_refl. Qed.
Lemma D_aa648 : decode_any W_aa648 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa64c : bv 32 := 0x03013b03.
Lemma F_aa64c : fetch_word Ubsan.M.loaded_segments (0xac4dc : word) = Some W_aa64c.
Proof. vm_refl. Qed.
Lemma D_aa64c : decode_any W_aa64c = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa650 : bv 32 := 0x07010113.
Lemma F_aa650 : fetch_word Ubsan.M.loaded_segments (0xac4e0 : word) = Some W_aa650.
Proof. vm_refl. Qed.
Lemma D_aa650 : decode_any W_aa650 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa654 : bv 32 := 0x00008067.
Lemma F_aa654 : fetch_word Ubsan.M.loaded_segments (0xac4e4 : word) = Some W_aa654.
Proof. vm_refl. Qed.
Lemma D_aa654 : decode_any W_aa654 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa658 : bv 32 := 0x00800713.
Lemma F_aa658 : fetch_word Ubsan.M.loaded_segments (0xac4e8 : word) = Some W_aa658.
Proof. vm_refl. Qed.
Lemma D_aa658 : decode_any W_aa658 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa65c : bv 32 := 0x000a0593.
Lemma F_aa65c : fetch_word Ubsan.M.loaded_segments (0xac4ec : word) = Some W_aa65c.
Proof. vm_refl. Qed.
Lemma D_aa65c : decode_any W_aa65c = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa660 : bv 32 := 0x00e98733.
Lemma F_aa660 : fetch_word Ubsan.M.loaded_segments (0xac4f0 : word) = Some W_aa660.
Proof. vm_refl. Qed.
Lemma D_aa660 : decode_any W_aa660 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa664 : bv 32 := 0x00073783.
Lemma F_aa664 : fetch_word Ubsan.M.loaded_segments (0xac4f4 : word) = Some W_aa664.
Proof. vm_refl. Qed.
Lemma D_aa664 : decode_any W_aa664 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa668 : bv 32 := 0x40ab0b33.
Lemma F_aa668 : fetch_word Ubsan.M.loaded_segments (0xac4f8 : word) = Some W_aa668.
Proof. vm_refl. Qed.
Lemma D_aa668 : decode_any W_aa668 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa66c : bv 32 := 0x0784a503.
Lemma F_aa66c : fetch_word Ubsan.M.loaded_segments (0xac4fc : word) = Some W_aa66c.
Proof. vm_refl. Qed.
Lemma D_aa66c : decode_any W_aa66c = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa670 : bv 32 := 0x40c9093b.
Lemma F_aa670 : fetch_word Ubsan.M.loaded_segments (0xac500 : word) = Some W_aa670.
Proof. vm_refl. Qed.
Lemma D_aa670 : decode_any W_aa670 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa674 : bv 32 := 0x40d787b3.
Lemma F_aa674 : fetch_word Ubsan.M.loaded_segments (0xac504 : word) = Some W_aa674.
Proof. vm_refl. Qed.
Lemma D_aa674 : decode_any W_aa674 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa678 : bv 32 := 0x00f73023.
Lemma F_aa678 : fetch_word Ubsan.M.loaded_segments (0xac508 : word) = Some W_aa678.
Proof. vm_refl. Qed.
Lemma D_aa678 : decode_any W_aa678 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa67c : bv 32 := 0x04200893.
Lemma F_aa67c : fetch_word Ubsan.M.loaded_segments (0xac50c : word) = Some W_aa67c.
Proof. vm_refl. Qed.
Lemma D_aa67c : decode_any W_aa67c = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa680 : bv 32 := 0x00090613.
Lemma F_aa680 : fetch_word Ubsan.M.loaded_segments (0xac510 : word) = Some W_aa680.
Proof. vm_refl. Qed.
Lemma D_aa680 : decode_any W_aa680 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa684 : bv 32 := 0x00000073.
Lemma F_aa684 : fetch_word Ubsan.M.loaded_segments (0xac514 : word) = Some W_aa684.
Proof. vm_refl. Qed.
Lemma D_aa684 : decode_any W_aa684 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_aa684 : is_ecall W_aa684 = true.
Proof. reflexivity. Qed.

Definition W_aa688 : bv 32 := 0xe09fa0ef.
Lemma F_aa688 : fetch_word Ubsan.M.loaded_segments (0xac518 : word) = Some W_aa688.
Proof. vm_refl. Qed.
Lemma D_aa688 : decode_any W_aa688 = Some (Jal 1 2076168, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa68c : bv 32 := 0x000a0993.
Lemma F_aa68c : fetch_word Ubsan.M.loaded_segments (0xac51c : word) = Some W_aa68c.
Proof. vm_refl. Qed.
Lemma D_aa68c : decode_any W_aa68c = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa690 : bv 32 := 0xf7650ce3.
Lemma F_aa690 : fetch_word Ubsan.M.loaded_segments (0xac520 : word) = Some W_aa690.
Proof. vm_refl. Qed.
Lemma D_aa690 : decode_any W_aa690 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa694 : bv 32 := 0x02054c63.
Lemma F_aa694 : fetch_word Ubsan.M.loaded_segments (0xac524 : word) = Some W_aa694.
Proof. vm_refl. Qed.
Lemma D_aa694 : decode_any W_aa694 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa698 : bv 32 := 0x0089b583.
Lemma F_aa698 : fetch_word Ubsan.M.loaded_segments (0xac528 : word) = Some W_aa698.
Proof. vm_refl. Qed.
Lemma D_aa698 : decode_any W_aa698 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa69c : bv 32 := 0x00a5b633.
Lemma F_aa69c : fetch_word Ubsan.M.loaded_segments (0xac52c : word) = Some W_aa69c.
Proof. vm_refl. Qed.
Lemma D_aa69c : decode_any W_aa69c = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa6a0 : bv 32 := 0x00461a13.
Lemma F_aa6a0 : fetch_word Ubsan.M.loaded_segments (0xac530 : word) = Some W_aa6a0.
Proof. vm_refl. Qed.
Lemma D_aa6a0 : decode_any W_aa6a0 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa6a4 : bv 32 := 0x01498a33.
Lemma F_aa6a4 : fetch_word Ubsan.M.loaded_segments (0xac534 : word) = Some W_aa6a4.
Proof. vm_refl. Qed.
Lemma D_aa6a4 : decode_any W_aa6a4 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa6a8 : bv 32 := 0x000a3703.
Lemma F_aa6a8 : fetch_word Ubsan.M.loaded_segments (0xac538 : word) = Some W_aa6a8.
Proof. vm_refl. Qed.
Lemma D_aa6a8 : decode_any W_aa6a8 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa6ac : bv 32 := 0x40c006b3.
Lemma F_aa6ac : fetch_word Ubsan.M.loaded_segments (0xac53c : word) = Some W_aa6ac.
Proof. vm_refl. Qed.
Lemma D_aa6ac : decode_any W_aa6ac = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa6b0 : bv 32 := 0x00b6f6b3.
Lemma F_aa6b0 : fetch_word Ubsan.M.loaded_segments (0xac540 : word) = Some W_aa6b0.
Proof. vm_refl. Qed.
Lemma D_aa6b0 : decode_any W_aa6b0 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa6b4 : bv 32 := 0x40d506b3.
Lemma F_aa6b4 : fetch_word Ubsan.M.loaded_segments (0xac544 : word) = Some W_aa6b4.
Proof. vm_refl. Qed.
Lemma D_aa6b4 : decode_any W_aa6b4 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa6b8 : bv 32 := 0x00d70733.
Lemma F_aa6b8 : fetch_word Ubsan.M.loaded_segments (0xac548 : word) = Some W_aa6b8.
Proof. vm_refl. Qed.
Lemma D_aa6b8 : decode_any W_aa6b8 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa6bc : bv 32 := 0x00ea3023.
Lemma F_aa6bc : fetch_word Ubsan.M.loaded_segments (0xac54c : word) = Some W_aa6bc.
Proof. vm_refl. Qed.
Lemma D_aa6bc : decode_any W_aa6bc = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa6c0 : bv 32 := 0xf8a5fce3.
Lemma F_aa6c0 : fetch_word Ubsan.M.loaded_segments (0xac550 : word) = Some W_aa6c0.
Proof. vm_refl. Qed.
Lemma D_aa6c0 : decode_any W_aa6c0 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa6c4 : bv 32 := 0x01800713.
Lemma F_aa6c4 : fetch_word Ubsan.M.loaded_segments (0xac554 : word) = Some W_aa6c4.
Proof. vm_refl. Qed.
Lemma D_aa6c4 : decode_any W_aa6c4 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_aa6c8 : bv 32 := 0xf95ff06f.
Lemma F_aa6c8 : fetch_word Ubsan.M.loaded_segments (0xac558 : word) = Some W_aa6c8.
Proof. vm_refl. Qed.
Lemma D_aa6c8 : decode_any W_aa6c8 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaa14 : bv 32 := 0xff010113.
Lemma F_aaa14 : fetch_word Ubsan.M.loaded_segments (0xac8a4 : word) = Some W_aaa14.
Proof. vm_refl. Qed.
Lemma D_aaa14 : decode_any W_aaa14 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaa18 : bv 32 := 0x00113423.
Lemma F_aaa18 : fetch_word Ubsan.M.loaded_segments (0xac8a8 : word) = Some W_aaa18.
Proof. vm_refl. Qed.
Lemma D_aaa18 : decode_any W_aaa18 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaa1c : bv 32 := 0x00813023.
Lemma F_aaa1c : fetch_word Ubsan.M.loaded_segments (0xac8ac : word) = Some W_aaa1c.
Proof. vm_refl. Qed.
Lemma D_aaa1c : decode_any W_aaa1c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaa20 : bv 32 := 0x41c000ef.
Lemma F_aaa20 : fetch_word Ubsan.M.loaded_segments (0xac8b0 : word) = Some W_aaa20.
Proof. vm_refl. Qed.
Lemma D_aaa20 : decode_any W_aaa20 = Some (Jal 1 1052, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaa24 : bv 32 := 0x00053403.
Lemma F_aaa24 : fetch_word Ubsan.M.loaded_segments (0xac8b4 : word) = Some W_aaa24.
Proof. vm_refl. Qed.
Lemma D_aaa24 : decode_any W_aaa24 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaa28 : bv 32 := 0x12041663.
Lemma F_aaa28 : fetch_word Ubsan.M.loaded_segments (0xac8b8 : word) = Some W_aaa28.
Proof. vm_refl. Qed.
Lemma D_aaa28 : decode_any W_aaa28 = Some (Branch BC_NE 8 0 300, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaa2c : bv 32 := 0x0004a517.
Lemma F_aaa2c : fetch_word Ubsan.M.loaded_segments (0xac8bc : word) = Some W_aaa2c.
Proof. vm_refl. Qed.
Lemma D_aaa2c : decode_any W_aaa2c = Some (Auipc 10 74, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaa30 : bv 32 := 0x70c53403.
Lemma F_aaa30 : fetch_word Ubsan.M.loaded_segments (0xac8c0 : word) = Some W_aaa30.
Proof. vm_refl. Qed.
Lemma D_aaa30 : decode_any W_aaa30 = Some (Load SZ8 true 8 10 1804, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaa34 : bv 32 := 0x04040a63.
Lemma F_aaa34 : fetch_word Ubsan.M.loaded_segments (0xac8c4 : word) = Some W_aaa34.
Proof. vm_refl. Qed.
Lemma D_aaa34 : decode_any W_aaa34 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaa88 : bv 32 := 0x00018517.
Lemma F_aaa88 : fetch_word Ubsan.M.loaded_segments (0xac918 : word) = Some W_aaa88.
Proof. vm_refl. Qed.
Lemma D_aaa88 : decode_any W_aaa88 = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaa8c : bv 32 := 0x42853403.
Lemma F_aaa8c : fetch_word Ubsan.M.loaded_segments (0xac91c : word) = Some W_aaa8c.
Proof. vm_refl. Qed.
Lemma D_aaa8c : decode_any W_aaa8c = Some (Load SZ8 true 8 10 1064, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaa90 : bv 32 := 0x04040a63.
Lemma F_aaa90 : fetch_word Ubsan.M.loaded_segments (0xac920 : word) = Some W_aaa90.
Proof. vm_refl. Qed.
Lemma D_aaa90 : decode_any W_aaa90 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaa94 : bv 32 := 0x08c42503.
Lemma F_aaa94 : fetch_word Ubsan.M.loaded_segments (0xac924 : word) = Some W_aaa94.
Proof. vm_refl. Qed.
Lemma D_aaa94 : decode_any W_aaa94 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaa98 : bv 32 := 0x00054663.
Lemma F_aaa98 : fetch_word Ubsan.M.loaded_segments (0xac928 : word) = Some W_aaa98.
Proof. vm_refl. Qed.
Lemma D_aaa98 : decode_any W_aaa98 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaaa4 : bv 32 := 0x02843503.
Lemma F_aaaa4 : fetch_word Ubsan.M.loaded_segments (0xac934 : word) = Some W_aaaa4.
Proof. vm_refl. Qed.
Lemma D_aaaa4 : decode_any W_aaaa4 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaaa8 : bv 32 := 0x03843583.
Lemma F_aaaa8 : fetch_word Ubsan.M.loaded_segments (0xac938 : word) = Some W_aaaa8.
Proof. vm_refl. Qed.
Lemma D_aaaa8 : decode_any W_aaaa8 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaaac : bv 32 := 0x00b50c63.
Lemma F_aaaac : fetch_word Ubsan.M.loaded_segments (0xac93c : word) = Some W_aaaac.
Proof. vm_refl. Qed.
Lemma D_aaaac : decode_any W_aaaac = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaab0 : bv 32 := 0x04843683.
Lemma F_aaab0 : fetch_word Ubsan.M.loaded_segments (0xac940 : word) = Some W_aaab0.
Proof. vm_refl. Qed.
Lemma D_aaab0 : decode_any W_aaab0 = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaab4 : bv 32 := 0x00040513.
Lemma F_aaab4 : fetch_word Ubsan.M.loaded_segments (0xac944 : word) = Some W_aaab4.
Proof. vm_refl. Qed.
Lemma D_aaab4 : decode_any W_aaab4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaab8 : bv 32 := 0x00000593.
Lemma F_aaab8 : fetch_word Ubsan.M.loaded_segments (0xac948 : word) = Some W_aaab8.
Proof. vm_refl. Qed.
Lemma D_aaab8 : decode_any W_aaab8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaabc : bv 32 := 0x00000613.
Lemma F_aaabc : fetch_word Ubsan.M.loaded_segments (0xac94c : word) = Some W_aaabc.
Proof. vm_refl. Qed.
Lemma D_aaabc : decode_any W_aaabc = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaac0 : bv 32 := 0x000680e7.
Lemma F_aaac0 : fetch_word Ubsan.M.loaded_segments (0xac950 : word) = Some W_aaac0.
Proof. vm_refl. Qed.
Lemma D_aaac0 : decode_any W_aaac0 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaac4 : bv 32 := 0x00843503.
Lemma F_aaac4 : fetch_word Ubsan.M.loaded_segments (0xac954 : word) = Some W_aaac4.
Proof. vm_refl. Qed.
Lemma D_aaac4 : decode_any W_aaac4 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaac8 : bv 32 := 0x01043583.
Lemma F_aaac8 : fetch_word Ubsan.M.loaded_segments (0xac958 : word) = Some W_aaac8.
Proof. vm_refl. Qed.
Lemma D_aaac8 : decode_any W_aaac8 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaacc : bv 32 := 0x00b50c63.
Lemma F_aaacc : fetch_word Ubsan.M.loaded_segments (0xac95c : word) = Some W_aaacc.
Proof. vm_refl. Qed.
Lemma D_aaacc : decode_any W_aaacc = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaae4 : bv 32 := 0x00018517.
Lemma F_aaae4 : fetch_word Ubsan.M.loaded_segments (0xac974 : word) = Some W_aaae4.
Proof. vm_refl. Qed.
Lemma D_aaae4 : decode_any W_aaae4 = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaae8 : bv 32 := 0x2dc53403.
Lemma F_aaae8 : fetch_word Ubsan.M.loaded_segments (0xac978 : word) = Some W_aaae8.
Proof. vm_refl. Qed.
Lemma D_aaae8 : decode_any W_aaae8 = Some (Load SZ8 true 8 10 732, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaaec : bv 32 := 0x0a040e63.
Lemma F_aaaec : fetch_word Ubsan.M.loaded_segments (0xac97c : word) = Some W_aaaec.
Proof. vm_refl. Qed.
Lemma D_aaaec : decode_any W_aaaec = Some (Branch BC_EQ 8 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaaf0 : bv 32 := 0x08c42503.
Lemma F_aaaf0 : fetch_word Ubsan.M.loaded_segments (0xac980 : word) = Some W_aaaf0.
Proof. vm_refl. Qed.
Lemma D_aaaf0 : decode_any W_aaaf0 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaaf4 : bv 32 := 0x00054663.
Lemma F_aaaf4 : fetch_word Ubsan.M.loaded_segments (0xac984 : word) = Some W_aaaf4.
Proof. vm_refl. Qed.
Lemma D_aaaf4 : decode_any W_aaaf4 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_aab00 : bv 32 := 0x02843503.
Lemma F_aab00 : fetch_word Ubsan.M.loaded_segments (0xac990 : word) = Some W_aab00.
Proof. vm_refl. Qed.
Lemma D_aab00 : decode_any W_aab00 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_aab04 : bv 32 := 0x03843583.
Lemma F_aab04 : fetch_word Ubsan.M.loaded_segments (0xac994 : word) = Some W_aab04.
Proof. vm_refl. Qed.
Lemma D_aab04 : decode_any W_aab04 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_aab08 : bv 32 := 0x00b50c63.
Lemma F_aab08 : fetch_word Ubsan.M.loaded_segments (0xac998 : word) = Some W_aab08.
Proof. vm_refl. Qed.
Lemma D_aab08 : decode_any W_aab08 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_aab20 : bv 32 := 0x00843503.
Lemma F_aab20 : fetch_word Ubsan.M.loaded_segments (0xac9b0 : word) = Some W_aab20.
Proof. vm_refl. Qed.
Lemma D_aab20 : decode_any W_aab20 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_aab24 : bv 32 := 0x01043583.
Lemma F_aab24 : fetch_word Ubsan.M.loaded_segments (0xac9b4 : word) = Some W_aab24.
Proof. vm_refl. Qed.
Lemma D_aab24 : decode_any W_aab24 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_aab28 : bv 32 := 0x08b50063.
Lemma F_aab28 : fetch_word Ubsan.M.loaded_segments (0xac9b8 : word) = Some W_aab28.
Proof. vm_refl. Qed.
Lemma D_aab28 : decode_any W_aab28 = Some (Branch BC_EQ 10 11 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_aaba8 : bv 32 := 0x00813083.
Lemma F_aaba8 : fetch_word Ubsan.M.loaded_segments (0xaca38 : word) = Some W_aaba8.
Proof. vm_refl. Qed.
Lemma D_aaba8 : decode_any W_aaba8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_aabac : bv 32 := 0x00013403.
Lemma F_aabac : fetch_word Ubsan.M.loaded_segments (0xaca3c : word) = Some W_aabac.
Proof. vm_refl. Qed.
Lemma D_aabac : decode_any W_aabac = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aabb0 : bv 32 := 0x01010113.
Lemma F_aabb0 : fetch_word Ubsan.M.loaded_segments (0xaca40 : word) = Some W_aabb0.
Proof. vm_refl. Qed.
Lemma D_aabb0 : decode_any W_aabb0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_aabb4 : bv 32 := 0x00008067.
Lemma F_aabb4 : fetch_word Ubsan.M.loaded_segments (0xaca44 : word) = Some W_aabb4.
Proof. vm_refl. Qed.
Lemma D_aabb4 : decode_any W_aabb4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aae3c : bv 32 := 0xff010113.
Lemma F_aae3c : fetch_word Ubsan.M.loaded_segments (0xacccc : word) = Some W_aae3c.
Proof. vm_refl. Qed.
Lemma D_aae3c : decode_any W_aae3c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_aae40 : bv 32 := 0x00113423.
Lemma F_aae40 : fetch_word Ubsan.M.loaded_segments (0xaccd0 : word) = Some W_aae40.
Proof. vm_refl. Qed.
Lemma D_aae40 : decode_any W_aae40 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_aae44 : bv 32 := 0x00813023.
Lemma F_aae44 : fetch_word Ubsan.M.loaded_segments (0xaccd4 : word) = Some W_aae44.
Proof. vm_refl. Qed.
Lemma D_aae44 : decode_any W_aae44 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aae48 : bv 32 := 0x0004a517.
Lemma F_aae48 : fetch_word Ubsan.M.loaded_segments (0xaccd8 : word) = Some W_aae48.
Proof. vm_refl. Qed.
Lemma D_aae48 : decode_any W_aae48 = Some (Auipc 10 74, 4%Z).
Proof. vm_refl. Qed.

Definition W_aae4c : bv 32 := 0x2f850413.
Lemma F_aae4c : fetch_word Ubsan.M.loaded_segments (0xaccdc : word) = Some W_aae4c.
Proof. vm_refl. Qed.
Lemma D_aae4c : decode_any W_aae4c = Some (OpImm ALU_ADD 8 10 760, 4%Z).
Proof. vm_refl. Qed.

Definition W_aae50 : bv 32 := 0x00040513.
Lemma F_aae50 : fetch_word Ubsan.M.loaded_segments (0xacce0 : word) = Some W_aae50.
Proof. vm_refl. Qed.
Lemma D_aae50 : decode_any W_aae50 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aae54 : bv 32 := 0x0410b0ef.
Lemma F_aae54 : fetch_word Ubsan.M.loaded_segments (0xacce4 : word) = Some W_aae54.
Proof. vm_refl. Qed.
Lemma D_aae54 : decode_any W_aae54 = Some (Jal 1 47168, 4%Z).
Proof. vm_refl. Qed.

Definition W_aae58 : bv 32 := 0x00840513.
Lemma F_aae58 : fetch_word Ubsan.M.loaded_segments (0xacce8 : word) = Some W_aae58.
Proof. vm_refl. Qed.
Lemma D_aae58 : decode_any W_aae58 = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_aae5c : bv 32 := 0x00813083.
Lemma F_aae5c : fetch_word Ubsan.M.loaded_segments (0xaccec : word) = Some W_aae5c.
Proof. vm_refl. Qed.
Lemma D_aae5c : decode_any W_aae5c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_aae60 : bv 32 := 0x00013403.
Lemma F_aae60 : fetch_word Ubsan.M.loaded_segments (0xaccf0 : word) = Some W_aae60.
Proof. vm_refl. Qed.
Lemma D_aae60 : decode_any W_aae60 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aae64 : bv 32 := 0x01010113.
Lemma F_aae64 : fetch_word Ubsan.M.loaded_segments (0xaccf4 : word) = Some W_aae64.
Proof. vm_refl. Qed.
Lemma D_aae64 : decode_any W_aae64 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_aae68 : bv 32 := 0x00008067.
Lemma F_aae68 : fetch_word Ubsan.M.loaded_segments (0xaccf8 : word) = Some W_aae68.
Proof. vm_refl. Qed.
Lemma D_aae68 : decode_any W_aae68 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

