(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_ba524 : bv 32 := 0x0ff5f593.
Lemma F_ba524 : fetch_word Ubsan.M.loaded_segments (0xbdf4c : word) = Some W_ba524.
Proof. vm_refl. Qed.
Lemma D_ba524 : decode_any W_ba524 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba528 : bv 32 := 0x00757693.
Lemma F_ba528 : fetch_word Ubsan.M.loaded_segments (0xbdf50 : word) = Some W_ba528.
Proof. vm_refl. Qed.
Lemma D_ba528 : decode_any W_ba528 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba52c : bv 32 := 0x00c03733.
Lemma F_ba52c : fetch_word Ubsan.M.loaded_segments (0xbdf54 : word) = Some W_ba52c.
Proof. vm_refl. Qed.
Lemma D_ba52c : decode_any W_ba52c = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba530 : bv 32 := 0x02068c63.
Lemma F_ba530 : fetch_word Ubsan.M.loaded_segments (0xbdf58 : word) = Some W_ba530.
Proof. vm_refl. Qed.
Lemma D_ba530 : decode_any W_ba530 = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba534 : bv 32 := 0x02060a63.
Lemma F_ba534 : fetch_word Ubsan.M.loaded_segments (0xbdf5c : word) = Some W_ba534.
Proof. vm_refl. Qed.
Lemma D_ba534 : decode_any W_ba534 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba538 : bv 32 := 0x00150793.
Lemma F_ba538 : fetch_word Ubsan.M.loaded_segments (0xbdf60 : word) = Some W_ba538.
Proof. vm_refl. Qed.
Lemma D_ba538 : decode_any W_ba538 = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba53c : bv 32 := 0x00100813.
Lemma F_ba53c : fetch_word Ubsan.M.loaded_segments (0xbdf64 : word) = Some W_ba53c.
Proof. vm_refl. Qed.
Lemma D_ba53c : decode_any W_ba53c = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba540 : bv 32 := 0x00054703.
Lemma F_ba540 : fetch_word Ubsan.M.loaded_segments (0xbdf68 : word) = Some W_ba540.
Proof. vm_refl. Qed.
Lemma D_ba540 : decode_any W_ba540 = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba544 : bv 32 := 0x00060693.
Lemma F_ba544 : fetch_word Ubsan.M.loaded_segments (0xbdf6c : word) = Some W_ba544.
Proof. vm_refl. Qed.
Lemma D_ba544 : decode_any W_ba544 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba548 : bv 32 := 0x06b70e63.
Lemma F_ba548 : fetch_word Ubsan.M.loaded_segments (0xbdf70 : word) = Some W_ba548.
Proof. vm_refl. Qed.
Lemma D_ba548 : decode_any W_ba548 = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba54c : bv 32 := 0x00150513.
Lemma F_ba54c : fetch_word Ubsan.M.loaded_segments (0xbdf74 : word) = Some W_ba54c.
Proof. vm_refl. Qed.
Lemma D_ba54c : decode_any W_ba54c = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba550 : bv 32 := 0xfff68613.
Lemma F_ba550 : fetch_word Ubsan.M.loaded_segments (0xbdf78 : word) = Some W_ba550.
Proof. vm_refl. Qed.
Lemma D_ba550 : decode_any W_ba550 = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba554 : bv 32 := 0x0077f893.
Lemma F_ba554 : fetch_word Ubsan.M.loaded_segments (0xbdf7c : word) = Some W_ba554.
Proof. vm_refl. Qed.
Lemma D_ba554 : decode_any W_ba554 = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba558 : bv 32 := 0x00c03733.
Lemma F_ba558 : fetch_word Ubsan.M.loaded_segments (0xbdf80 : word) = Some W_ba558.
Proof. vm_refl. Qed.
Lemma D_ba558 : decode_any W_ba558 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba55c : bv 32 := 0x00088663.
Lemma F_ba55c : fetch_word Ubsan.M.loaded_segments (0xbdf84 : word) = Some W_ba55c.
Proof. vm_refl. Qed.
Lemma D_ba55c : decode_any W_ba55c = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba560 : bv 32 := 0x00178793.
Lemma F_ba560 : fetch_word Ubsan.M.loaded_segments (0xbdf88 : word) = Some W_ba560.
Proof. vm_refl. Qed.
Lemma D_ba560 : decode_any W_ba560 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba564 : bv 32 := 0xfd069ee3.
Lemma F_ba564 : fetch_word Ubsan.M.loaded_segments (0xbdf8c : word) = Some W_ba564.
Proof. vm_refl. Qed.
Lemma D_ba564 : decode_any W_ba564 = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba568 : bv 32 := 0x06070863.
Lemma F_ba568 : fetch_word Ubsan.M.loaded_segments (0xbdf90 : word) = Some W_ba568.
Proof. vm_refl. Qed.
Lemma D_ba568 : decode_any W_ba568 = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba56c : bv 32 := 0x00054683.
Lemma F_ba56c : fetch_word Ubsan.M.loaded_segments (0xbdf94 : word) = Some W_ba56c.
Proof. vm_refl. Qed.
Lemma D_ba56c : decode_any W_ba56c = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba570 : bv 32 := 0x04b68663.
Lemma F_ba570 : fetch_word Ubsan.M.loaded_segments (0xbdf98 : word) = Some W_ba570.
Proof. vm_refl. Qed.
Lemma D_ba570 : decode_any W_ba570 = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba574 : bv 32 := 0x00800693.
Lemma F_ba574 : fetch_word Ubsan.M.loaded_segments (0xbdf9c : word) = Some W_ba574.
Proof. vm_refl. Qed.
Lemma D_ba574 : decode_any W_ba574 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba578 : bv 32 := 0x04d66263.
Lemma F_ba578 : fetch_word Ubsan.M.loaded_segments (0xbdfa0 : word) = Some W_ba578.
Proof. vm_refl. Qed.
Lemma D_ba578 : decode_any W_ba578 = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba57c : bv 32 := 0xfff56697.
Lemma F_ba57c : fetch_word Ubsan.M.loaded_segments (0xbdfa4 : word) = Some W_ba57c.
Proof. vm_refl. Qed.
Lemma D_ba57c : decode_any W_ba57c = Some (Auipc 13 1048406, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba580 : bv 32 := 0xb5c6b683.
Lemma F_ba580 : fetch_word Ubsan.M.loaded_segments (0xbdfa8 : word) = Some W_ba580.
Proof. vm_refl. Qed.
Lemma D_ba580 : decode_any W_ba580 = Some (Load SZ8 true 13 13 2908, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba584 : bv 32 := 0xfff56717.
Lemma F_ba584 : fetch_word Ubsan.M.loaded_segments (0xbdfac : word) = Some W_ba584.
Proof. vm_refl. Qed.
Lemma D_ba584 : decode_any W_ba584 = Some (Auipc 14 1048406, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba588 : bv 32 := 0xb4473703.
Lemma F_ba588 : fetch_word Ubsan.M.loaded_segments (0xbdfb0 : word) = Some W_ba588.
Proof. vm_refl. Qed.
Lemma D_ba588 : decode_any W_ba588 = Some (Load SZ8 true 14 14 2884, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba58c : bv 32 := 0x00168793.
Lemma F_ba58c : fetch_word Ubsan.M.loaded_segments (0xbdfb4 : word) = Some W_ba58c.
Proof. vm_refl. Qed.
Lemma D_ba58c : decode_any W_ba58c = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba590 : bv 32 := 0x02f587b3.
Lemma F_ba590 : fetch_word Ubsan.M.loaded_segments (0xbdfb8 : word) = Some W_ba590.
Proof. vm_refl. Qed.
Lemma D_ba590 : decode_any W_ba590 = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba594 : bv 32 := 0x00700813.
Lemma F_ba594 : fetch_word Ubsan.M.loaded_segments (0xbdfbc : word) = Some W_ba594.
Proof. vm_refl. Qed.
Lemma D_ba594 : decode_any W_ba594 = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba598 : bv 32 := 0x00053883.
Lemma F_ba598 : fetch_word Ubsan.M.loaded_segments (0xbdfc0 : word) = Some W_ba598.
Proof. vm_refl. Qed.
Lemma D_ba598 : decode_any W_ba598 = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba59c : bv 32 := 0x00f8c8b3.
Lemma F_ba59c : fetch_word Ubsan.M.loaded_segments (0xbdfc4 : word) = Some W_ba59c.
Proof. vm_refl. Qed.
Lemma D_ba59c : decode_any W_ba59c = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba5a0 : bv 32 := 0x411682b3.
Lemma F_ba5a0 : fetch_word Ubsan.M.loaded_segments (0xbdfc8 : word) = Some W_ba5a0.
Proof. vm_refl. Qed.
Lemma D_ba5a0 : decode_any W_ba5a0 = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba5a4 : bv 32 := 0x0112e8b3.
Lemma F_ba5a4 : fetch_word Ubsan.M.loaded_segments (0xbdfcc : word) = Some W_ba5a4.
Proof. vm_refl. Qed.
Lemma D_ba5a4 : decode_any W_ba5a4 = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba5a8 : bv 32 := 0x00e8f8b3.
Lemma F_ba5a8 : fetch_word Ubsan.M.loaded_segments (0xbdfd0 : word) = Some W_ba5a8.
Proof. vm_refl. Qed.
Lemma D_ba5a8 : decode_any W_ba5a8 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba5ac : bv 32 := 0x02e89a63.
Lemma F_ba5ac : fetch_word Ubsan.M.loaded_segments (0xbdfd4 : word) = Some W_ba5ac.
Proof. vm_refl. Qed.
Lemma D_ba5ac : decode_any W_ba5ac = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba5b0 : bv 32 := 0xff860613.
Lemma F_ba5b0 : fetch_word Ubsan.M.loaded_segments (0xbdfd8 : word) = Some W_ba5b0.
Proof. vm_refl. Qed.
Lemma D_ba5b0 : decode_any W_ba5b0 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba5b4 : bv 32 := 0x00850513.
Lemma F_ba5b4 : fetch_word Ubsan.M.loaded_segments (0xbdfdc : word) = Some W_ba5b4.
Proof. vm_refl. Qed.
Lemma D_ba5b4 : decode_any W_ba5b4 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba5b8 : bv 32 := 0xfec860e3.
Lemma F_ba5b8 : fetch_word Ubsan.M.loaded_segments (0xbdfe0 : word) = Some W_ba5b8.
Proof. vm_refl. Qed.
Lemma D_ba5b8 : decode_any W_ba5b8 = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba5bc : bv 32 := 0x00060693.
Lemma F_ba5bc : fetch_word Ubsan.M.loaded_segments (0xbdfe4 : word) = Some W_ba5bc.
Proof. vm_refl. Qed.
Lemma D_ba5bc : decode_any W_ba5bc = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba5c0 : bv 32 := 0x00060c63.
Lemma F_ba5c0 : fetch_word Ubsan.M.loaded_segments (0xbdfe8 : word) = Some W_ba5c0.
Proof. vm_refl. Qed.
Lemma D_ba5c0 : decode_any W_ba5c0 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba5c4 : bv 32 := 0x00054603.
Lemma F_ba5c4 : fetch_word Ubsan.M.loaded_segments (0xbdfec : word) = Some W_ba5c4.
Proof. vm_refl. Qed.
Lemma D_ba5c4 : decode_any W_ba5c4 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba5c8 : bv 32 := 0x00b60a63.
Lemma F_ba5c8 : fetch_word Ubsan.M.loaded_segments (0xbdff0 : word) = Some W_ba5c8.
Proof. vm_refl. Qed.
Lemma D_ba5c8 : decode_any W_ba5c8 = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba5cc : bv 32 := 0xfff68693.
Lemma F_ba5cc : fetch_word Ubsan.M.loaded_segments (0xbdff4 : word) = Some W_ba5cc.
Proof. vm_refl. Qed.
Lemma D_ba5cc : decode_any W_ba5cc = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba5d0 : bv 32 := 0x00150513.
Lemma F_ba5d0 : fetch_word Ubsan.M.loaded_segments (0xbdff8 : word) = Some W_ba5d0.
Proof. vm_refl. Qed.
Lemma D_ba5d0 : decode_any W_ba5d0 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba5d4 : bv 32 := 0xfe0698e3.
Lemma F_ba5d4 : fetch_word Ubsan.M.loaded_segments (0xbdffc : word) = Some W_ba5d4.
Proof. vm_refl. Qed.
Lemma D_ba5d4 : decode_any W_ba5d4 = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba5dc : bv 32 := 0x00008067.
Lemma F_ba5dc : fetch_word Ubsan.M.loaded_segments (0xbe004 : word) = Some W_ba5dc.
Proof. vm_refl. Qed.
Lemma D_ba5dc : decode_any W_ba5dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba5e0 : bv 32 := 0x00060693.
Lemma F_ba5e0 : fetch_word Ubsan.M.loaded_segments (0xbe008 : word) = Some W_ba5e0.
Proof. vm_refl. Qed.
Lemma D_ba5e0 : decode_any W_ba5e0 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba5e4 : bv 32 := 0x00054603.
Lemma F_ba5e4 : fetch_word Ubsan.M.loaded_segments (0xbe00c : word) = Some W_ba5e4.
Proof. vm_refl. Qed.
Lemma D_ba5e4 : decode_any W_ba5e4 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba5e8 : bv 32 := 0xfeb612e3.
Lemma F_ba5e8 : fetch_word Ubsan.M.loaded_segments (0xbe010 : word) = Some W_ba5e8.
Proof. vm_refl. Qed.
Lemma D_ba5e8 : decode_any W_ba5e8 = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba5ec : bv 32 := 0xff1ff06f.
Lemma F_ba5ec : fetch_word Ubsan.M.loaded_segments (0xbe014 : word) = Some W_ba5ec.
Proof. vm_refl. Qed.
Lemma D_ba5ec : decode_any W_ba5ec = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba620 : bv 32 := 0x0035f693.
Lemma F_ba620 : fetch_word Ubsan.M.loaded_segments (0xbe048 : word) = Some W_ba620.
Proof. vm_refl. Qed.
Lemma D_ba620 : decode_any W_ba620 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba624 : bv 32 := 0x10068863.
Lemma F_ba624 : fetch_word Ubsan.M.loaded_segments (0xbe04c : word) = Some W_ba624.
Proof. vm_refl. Qed.
Lemma D_ba624 : decode_any W_ba624 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba628 : bv 32 := 0x02060e63.
Lemma F_ba628 : fetch_word Ubsan.M.loaded_segments (0xbe050 : word) = Some W_ba628.
Proof. vm_refl. Qed.
Lemma D_ba628 : decode_any W_ba628 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba62c : bv 32 := 0x00158713.
Lemma F_ba62c : fetch_word Ubsan.M.loaded_segments (0xbe054 : word) = Some W_ba62c.
Proof. vm_refl. Qed.
Lemma D_ba62c : decode_any W_ba62c = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba630 : bv 32 := 0x00100793.
Lemma F_ba630 : fetch_word Ubsan.M.loaded_segments (0xbe058 : word) = Some W_ba630.
Proof. vm_refl. Qed.
Lemma D_ba630 : decode_any W_ba630 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba634 : bv 32 := 0x00050693.
Lemma F_ba634 : fetch_word Ubsan.M.loaded_segments (0xbe05c : word) = Some W_ba634.
Proof. vm_refl. Qed.
Lemma D_ba634 : decode_any W_ba634 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba638 : bv 32 := 0x0005c883.
Lemma F_ba638 : fetch_word Ubsan.M.loaded_segments (0xbe060 : word) = Some W_ba638.
Proof. vm_refl. Qed.
Lemma D_ba638 : decode_any W_ba638 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba63c : bv 32 := 0x00060813.
Lemma F_ba63c : fetch_word Ubsan.M.loaded_segments (0xbe064 : word) = Some W_ba63c.
Proof. vm_refl. Qed.
Lemma D_ba63c : decode_any W_ba63c = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba640 : bv 32 := 0x00158593.
Lemma F_ba640 : fetch_word Ubsan.M.loaded_segments (0xbe068 : word) = Some W_ba640.
Proof. vm_refl. Qed.
Lemma D_ba640 : decode_any W_ba640 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba644 : bv 32 := 0x00377293.
Lemma F_ba644 : fetch_word Ubsan.M.loaded_segments (0xbe06c : word) = Some W_ba644.
Proof. vm_refl. Qed.
Lemma D_ba644 : decode_any W_ba644 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba648 : bv 32 := 0x01168023.
Lemma F_ba648 : fetch_word Ubsan.M.loaded_segments (0xbe070 : word) = Some W_ba648.
Proof. vm_refl. Qed.
Lemma D_ba648 : decode_any W_ba648 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba64c : bv 32 := 0x00168693.
Lemma F_ba64c : fetch_word Ubsan.M.loaded_segments (0xbe074 : word) = Some W_ba64c.
Proof. vm_refl. Qed.
Lemma D_ba64c : decode_any W_ba64c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba650 : bv 32 := 0xfff60613.
Lemma F_ba650 : fetch_word Ubsan.M.loaded_segments (0xbe078 : word) = Some W_ba650.
Proof. vm_refl. Qed.
Lemma D_ba650 : decode_any W_ba650 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba654 : bv 32 := 0x00028a63.
Lemma F_ba654 : fetch_word Ubsan.M.loaded_segments (0xbe07c : word) = Some W_ba654.
Proof. vm_refl. Qed.
Lemma D_ba654 : decode_any W_ba654 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba658 : bv 32 := 0x00170713.
Lemma F_ba658 : fetch_word Ubsan.M.loaded_segments (0xbe080 : word) = Some W_ba658.
Proof. vm_refl. Qed.
Lemma D_ba658 : decode_any W_ba658 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba65c : bv 32 := 0xfcf81ee3.
Lemma F_ba65c : fetch_word Ubsan.M.loaded_segments (0xbe084 : word) = Some W_ba65c.
Proof. vm_refl. Qed.
Lemma D_ba65c : decode_any W_ba65c = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba660 : bv 32 := 0x0080006f.
Lemma F_ba660 : fetch_word Ubsan.M.loaded_segments (0xbe088 : word) = Some W_ba660.
Proof. vm_refl. Qed.
Lemma D_ba660 : decode_any W_ba660 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba664 : bv 32 := 0x00050693.
Lemma F_ba664 : fetch_word Ubsan.M.loaded_segments (0xbe08c : word) = Some W_ba664.
Proof. vm_refl. Qed.
Lemma D_ba664 : decode_any W_ba664 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba668 : bv 32 := 0x0036f793.
Lemma F_ba668 : fetch_word Ubsan.M.loaded_segments (0xbe090 : word) = Some W_ba668.
Proof. vm_refl. Qed.
Lemma D_ba668 : decode_any W_ba668 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba66c : bv 32 := 0x0c078a63.
Lemma F_ba66c : fetch_word Ubsan.M.loaded_segments (0xbe094 : word) = Some W_ba66c.
Proof. vm_refl. Qed.
Lemma D_ba66c : decode_any W_ba66c = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba670 : bv 32 := 0x02000713.
Lemma F_ba670 : fetch_word Ubsan.M.loaded_segments (0xbe098 : word) = Some W_ba670.
Proof. vm_refl. Qed.
Lemma D_ba670 : decode_any W_ba670 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba674 : bv 32 := 0x02e67063.
Lemma F_ba674 : fetch_word Ubsan.M.loaded_segments (0xbe09c : word) = Some W_ba674.
Proof. vm_refl. Qed.
Lemma D_ba674 : decode_any W_ba674 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba678 : bv 32 := 0x01000713.
Lemma F_ba678 : fetch_word Ubsan.M.loaded_segments (0xbe0a0 : word) = Some W_ba678.
Proof. vm_refl. Qed.
Lemma D_ba678 : decode_any W_ba678 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba67c : bv 32 := 0x24e67863.
Lemma F_ba67c : fetch_word Ubsan.M.loaded_segments (0xbe0a4 : word) = Some W_ba67c.
Proof. vm_refl. Qed.
Lemma D_ba67c : decode_any W_ba67c = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba680 : bv 32 := 0x00867713.
Lemma F_ba680 : fetch_word Ubsan.M.loaded_segments (0xbe0a8 : word) = Some W_ba680.
Proof. vm_refl. Qed.
Lemma D_ba680 : decode_any W_ba680 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba684 : bv 32 := 0x2c071e63.
Lemma F_ba684 : fetch_word Ubsan.M.loaded_segments (0xbe0ac : word) = Some W_ba684.
Proof. vm_refl. Qed.
Lemma D_ba684 : decode_any W_ba684 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba688 : bv 32 := 0x00467713.
Lemma F_ba688 : fetch_word Ubsan.M.loaded_segments (0xbe0b0 : word) = Some W_ba688.
Proof. vm_refl. Qed.
Lemma D_ba688 : decode_any W_ba688 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba68c : bv 32 := 0x32071463.
Lemma F_ba68c : fetch_word Ubsan.M.loaded_segments (0xbe0b4 : word) = Some W_ba68c.
Proof. vm_refl. Qed.
Lemma D_ba68c : decode_any W_ba68c = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba690 : bv 32 := 0x3500006f.
Lemma F_ba690 : fetch_word Ubsan.M.loaded_segments (0xbe0b8 : word) = Some W_ba690.
Proof. vm_refl. Qed.
Lemma D_ba690 : decode_any W_ba690 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba694 : bv 32 := 0x0005a703.
Lemma F_ba694 : fetch_word Ubsan.M.loaded_segments (0xbe0bc : word) = Some W_ba694.
Proof. vm_refl. Qed.
Lemma D_ba694 : decode_any W_ba694 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba698 : bv 32 := 0x00300813.
Lemma F_ba698 : fetch_word Ubsan.M.loaded_segments (0xbe0c0 : word) = Some W_ba698.
Proof. vm_refl. Qed.
Lemma D_ba698 : decode_any W_ba698 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba69c : bv 32 := 0x11078e63.
Lemma F_ba69c : fetch_word Ubsan.M.loaded_segments (0xbe0c4 : word) = Some W_ba69c.
Proof. vm_refl. Qed.
Lemma D_ba69c : decode_any W_ba69c = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba6a0 : bv 32 := 0x00200813.
Lemma F_ba6a0 : fetch_word Ubsan.M.loaded_segments (0xbe0c8 : word) = Some W_ba6a0.
Proof. vm_refl. Qed.
Lemma D_ba6a0 : decode_any W_ba6a0 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba6a4 : bv 32 := 0x19079c63.
Lemma F_ba6a4 : fetch_word Ubsan.M.loaded_segments (0xbe0cc : word) = Some W_ba6a4.
Proof. vm_refl. Qed.
Lemma D_ba6a4 : decode_any W_ba6a4 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba6a8 : bv 32 := 0x00875793.
Lemma F_ba6a8 : fetch_word Ubsan.M.loaded_segments (0xbe0d0 : word) = Some W_ba6a8.
Proof. vm_refl. Qed.
Lemma D_ba6a8 : decode_any W_ba6a8 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba6ac : bv 32 := 0xffe60613.
Lemma F_ba6ac : fetch_word Ubsan.M.loaded_segments (0xbe0d4 : word) = Some W_ba6ac.
Proof. vm_refl. Qed.
Lemma D_ba6ac : decode_any W_ba6ac = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba6b0 : bv 32 := 0x00e68023.
Lemma F_ba6b0 : fetch_word Ubsan.M.loaded_segments (0xbe0d8 : word) = Some W_ba6b0.
Proof. vm_refl. Qed.
Lemma D_ba6b0 : decode_any W_ba6b0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba6b4 : bv 32 := 0x00f680a3.
Lemma F_ba6b4 : fetch_word Ubsan.M.loaded_segments (0xbe0dc : word) = Some W_ba6b4.
Proof. vm_refl. Qed.
Lemma D_ba6b4 : decode_any W_ba6b4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba6b8 : bv 32 := 0x00268693.
Lemma F_ba6b8 : fetch_word Ubsan.M.loaded_segments (0xbe0e0 : word) = Some W_ba6b8.
Proof. vm_refl. Qed.
Lemma D_ba6b8 : decode_any W_ba6b8 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba6bc : bv 32 := 0x01058593.
Lemma F_ba6bc : fetch_word Ubsan.M.loaded_segments (0xbe0e4 : word) = Some W_ba6bc.
Proof. vm_refl. Qed.
Lemma D_ba6bc : decode_any W_ba6bc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba6c0 : bv 32 := 0x01100793.
Lemma F_ba6c0 : fetch_word Ubsan.M.loaded_segments (0xbe0e8 : word) = Some W_ba6c0.
Proof. vm_refl. Qed.
Lemma D_ba6c0 : decode_any W_ba6c0 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba6c4 : bv 32 := 0x0107581b.
Lemma F_ba6c4 : fetch_word Ubsan.M.loaded_segments (0xbe0ec : word) = Some W_ba6c4.
Proof. vm_refl. Qed.
Lemma D_ba6c4 : decode_any W_ba6c4 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba6c8 : bv 32 := 0xff45a883.
Lemma F_ba6c8 : fetch_word Ubsan.M.loaded_segments (0xbe0f0 : word) = Some W_ba6c8.
Proof. vm_refl. Qed.
Lemma D_ba6c8 : decode_any W_ba6c8 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba6cc : bv 32 := 0xff85a283.
Lemma F_ba6cc : fetch_word Ubsan.M.loaded_segments (0xbe0f4 : word) = Some W_ba6cc.
Proof. vm_refl. Qed.
Lemma D_ba6cc : decode_any W_ba6cc = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba6d0 : bv 32 := 0xffc5a303.
Lemma F_ba6d0 : fetch_word Ubsan.M.loaded_segments (0xbe0f8 : word) = Some W_ba6d0.
Proof. vm_refl. Qed.
Lemma D_ba6d0 : decode_any W_ba6d0 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba6d4 : bv 32 := 0x0005a703.
Lemma F_ba6d4 : fetch_word Ubsan.M.loaded_segments (0xbe0fc : word) = Some W_ba6d4.
Proof. vm_refl. Qed.
Lemma D_ba6d4 : decode_any W_ba6d4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba6d8 : bv 32 := 0x01089393.
Lemma F_ba6d8 : fetch_word Ubsan.M.loaded_segments (0xbe100 : word) = Some W_ba6d8.
Proof. vm_refl. Qed.
Lemma D_ba6d8 : decode_any W_ba6d8 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba6dc : bv 32 := 0x0108d89b.
Lemma F_ba6dc : fetch_word Ubsan.M.loaded_segments (0xbe104 : word) = Some W_ba6dc.
Proof. vm_refl. Qed.
Lemma D_ba6dc : decode_any W_ba6dc = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba6e0 : bv 32 := 0x0103e833.
Lemma F_ba6e0 : fetch_word Ubsan.M.loaded_segments (0xbe108 : word) = Some W_ba6e0.
Proof. vm_refl. Qed.
Lemma D_ba6e0 : decode_any W_ba6e0 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba6e4 : bv 32 := 0x01029393.
Lemma F_ba6e4 : fetch_word Ubsan.M.loaded_segments (0xbe10c : word) = Some W_ba6e4.
Proof. vm_refl. Qed.
Lemma D_ba6e4 : decode_any W_ba6e4 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba6e8 : bv 32 := 0x0102d29b.
Lemma F_ba6e8 : fetch_word Ubsan.M.loaded_segments (0xbe110 : word) = Some W_ba6e8.
Proof. vm_refl. Qed.
Lemma D_ba6e8 : decode_any W_ba6e8 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba6ec : bv 32 := 0x0113e8b3.
Lemma F_ba6ec : fetch_word Ubsan.M.loaded_segments (0xbe114 : word) = Some W_ba6ec.
Proof. vm_refl. Qed.
Lemma D_ba6ec : decode_any W_ba6ec = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba6f0 : bv 32 := 0x01031393.
Lemma F_ba6f0 : fetch_word Ubsan.M.loaded_segments (0xbe118 : word) = Some W_ba6f0.
Proof. vm_refl. Qed.
Lemma D_ba6f0 : decode_any W_ba6f0 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba6f4 : bv 32 := 0x0103531b.
Lemma F_ba6f4 : fetch_word Ubsan.M.loaded_segments (0xbe11c : word) = Some W_ba6f4.
Proof. vm_refl. Qed.
Lemma D_ba6f4 : decode_any W_ba6f4 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba6f8 : bv 32 := 0x0053e2b3.
Lemma F_ba6f8 : fetch_word Ubsan.M.loaded_segments (0xbe120 : word) = Some W_ba6f8.
Proof. vm_refl. Qed.
Lemma D_ba6f8 : decode_any W_ba6f8 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba6fc : bv 32 := 0x01071393.
Lemma F_ba6fc : fetch_word Ubsan.M.loaded_segments (0xbe124 : word) = Some W_ba6fc.
Proof. vm_refl. Qed.
Lemma D_ba6fc : decode_any W_ba6fc = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba700 : bv 32 := 0x0063e333.
Lemma F_ba700 : fetch_word Ubsan.M.loaded_segments (0xbe128 : word) = Some W_ba700.
Proof. vm_refl. Qed.
Lemma D_ba700 : decode_any W_ba700 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba704 : bv 32 := 0xff060613.
Lemma F_ba704 : fetch_word Ubsan.M.loaded_segments (0xbe12c : word) = Some W_ba704.
Proof. vm_refl. Qed.
Lemma D_ba704 : decode_any W_ba704 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba708 : bv 32 := 0x0106a023.
Lemma F_ba708 : fetch_word Ubsan.M.loaded_segments (0xbe130 : word) = Some W_ba708.
Proof. vm_refl. Qed.
Lemma D_ba708 : decode_any W_ba708 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba70c : bv 32 := 0x0116a223.
Lemma F_ba70c : fetch_word Ubsan.M.loaded_segments (0xbe134 : word) = Some W_ba70c.
Proof. vm_refl. Qed.
Lemma D_ba70c : decode_any W_ba70c = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba710 : bv 32 := 0x0056a423.
Lemma F_ba710 : fetch_word Ubsan.M.loaded_segments (0xbe138 : word) = Some W_ba710.
Proof. vm_refl. Qed.
Lemma D_ba710 : decode_any W_ba710 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba714 : bv 32 := 0x0066a623.
Lemma F_ba714 : fetch_word Ubsan.M.loaded_segments (0xbe13c : word) = Some W_ba714.
Proof. vm_refl. Qed.
Lemma D_ba714 : decode_any W_ba714 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba718 : bv 32 := 0x01068693.
Lemma F_ba718 : fetch_word Ubsan.M.loaded_segments (0xbe140 : word) = Some W_ba718.
Proof. vm_refl. Qed.
Lemma D_ba718 : decode_any W_ba718 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba71c : bv 32 := 0x01058593.
Lemma F_ba71c : fetch_word Ubsan.M.loaded_segments (0xbe144 : word) = Some W_ba71c.
Proof. vm_refl. Qed.
Lemma D_ba71c : decode_any W_ba71c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba720 : bv 32 := 0xfac7e2e3.
Lemma F_ba720 : fetch_word Ubsan.M.loaded_segments (0xbe148 : word) = Some W_ba720.
Proof. vm_refl. Qed.
Lemma D_ba720 : decode_any W_ba720 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba724 : bv 32 := 0xff258593.
Lemma F_ba724 : fetch_word Ubsan.M.loaded_segments (0xbe14c : word) = Some W_ba724.
Proof. vm_refl. Qed.
Lemma D_ba724 : decode_any W_ba724 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba728 : bv 32 := 0x01000713.
Lemma F_ba728 : fetch_word Ubsan.M.loaded_segments (0xbe150 : word) = Some W_ba728.
Proof. vm_refl. Qed.
Lemma D_ba728 : decode_any W_ba728 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba72c : bv 32 := 0xf4e66ae3.
Lemma F_ba72c : fetch_word Ubsan.M.loaded_segments (0xbe154 : word) = Some W_ba72c.
Proof. vm_refl. Qed.
Lemma D_ba72c : decode_any W_ba72c = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba730 : bv 32 := 0x19c0006f.
Lemma F_ba730 : fetch_word Ubsan.M.loaded_segments (0xbe158 : word) = Some W_ba730.
Proof. vm_refl. Qed.
Lemma D_ba730 : decode_any W_ba730 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba734 : bv 32 := 0x00050693.
Lemma F_ba734 : fetch_word Ubsan.M.loaded_segments (0xbe15c : word) = Some W_ba734.
Proof. vm_refl. Qed.
Lemma D_ba734 : decode_any W_ba734 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba738 : bv 32 := 0x00357793.
Lemma F_ba738 : fetch_word Ubsan.M.loaded_segments (0xbe160 : word) = Some W_ba738.
Proof. vm_refl. Qed.
Lemma D_ba738 : decode_any W_ba738 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba73c : bv 32 := 0xf2079ae3.
Lemma F_ba73c : fetch_word Ubsan.M.loaded_segments (0xbe164 : word) = Some W_ba73c.
Proof. vm_refl. Qed.
Lemma D_ba73c : decode_any W_ba73c = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba740 : bv 32 := 0x01000713.
Lemma F_ba740 : fetch_word Ubsan.M.loaded_segments (0xbe168 : word) = Some W_ba740.
Proof. vm_refl. Qed.
Lemma D_ba740 : decode_any W_ba740 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba744 : bv 32 := 0x02e66c63.
Lemma F_ba744 : fetch_word Ubsan.M.loaded_segments (0xbe16c : word) = Some W_ba744.
Proof. vm_refl. Qed.
Lemma D_ba744 : decode_any W_ba744 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba748 : bv 32 := 0x00f00713.
Lemma F_ba748 : fetch_word Ubsan.M.loaded_segments (0xbe170 : word) = Some W_ba748.
Proof. vm_refl. Qed.
Lemma D_ba748 : decode_any W_ba748 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba74c : bv 32 := 0x0005a783.
Lemma F_ba74c : fetch_word Ubsan.M.loaded_segments (0xbe174 : word) = Some W_ba74c.
Proof. vm_refl. Qed.
Lemma D_ba74c : decode_any W_ba74c = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba750 : bv 32 := 0x0045a803.
Lemma F_ba750 : fetch_word Ubsan.M.loaded_segments (0xbe178 : word) = Some W_ba750.
Proof. vm_refl. Qed.
Lemma D_ba750 : decode_any W_ba750 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba754 : bv 32 := 0x0085a883.
Lemma F_ba754 : fetch_word Ubsan.M.loaded_segments (0xbe17c : word) = Some W_ba754.
Proof. vm_refl. Qed.
Lemma D_ba754 : decode_any W_ba754 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba758 : bv 32 := 0x00c5a283.
Lemma F_ba758 : fetch_word Ubsan.M.loaded_segments (0xbe180 : word) = Some W_ba758.
Proof. vm_refl. Qed.
Lemma D_ba758 : decode_any W_ba758 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba75c : bv 32 := 0x01058593.
Lemma F_ba75c : fetch_word Ubsan.M.loaded_segments (0xbe184 : word) = Some W_ba75c.
Proof. vm_refl. Qed.
Lemma D_ba75c : decode_any W_ba75c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba760 : bv 32 := 0xff060613.
Lemma F_ba760 : fetch_word Ubsan.M.loaded_segments (0xbe188 : word) = Some W_ba760.
Proof. vm_refl. Qed.
Lemma D_ba760 : decode_any W_ba760 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba764 : bv 32 := 0x00f6a023.
Lemma F_ba764 : fetch_word Ubsan.M.loaded_segments (0xbe18c : word) = Some W_ba764.
Proof. vm_refl. Qed.
Lemma D_ba764 : decode_any W_ba764 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba768 : bv 32 := 0x0106a223.
Lemma F_ba768 : fetch_word Ubsan.M.loaded_segments (0xbe190 : word) = Some W_ba768.
Proof. vm_refl. Qed.
Lemma D_ba768 : decode_any W_ba768 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba76c : bv 32 := 0x0116a423.
Lemma F_ba76c : fetch_word Ubsan.M.loaded_segments (0xbe194 : word) = Some W_ba76c.
Proof. vm_refl. Qed.
Lemma D_ba76c : decode_any W_ba76c = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba770 : bv 32 := 0x0056a623.
Lemma F_ba770 : fetch_word Ubsan.M.loaded_segments (0xbe198 : word) = Some W_ba770.
Proof. vm_refl. Qed.
Lemma D_ba770 : decode_any W_ba770 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba774 : bv 32 := 0x01068693.
Lemma F_ba774 : fetch_word Ubsan.M.loaded_segments (0xbe19c : word) = Some W_ba774.
Proof. vm_refl. Qed.
Lemma D_ba774 : decode_any W_ba774 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba778 : bv 32 := 0xfcc76ae3.
Lemma F_ba778 : fetch_word Ubsan.M.loaded_segments (0xbe1a0 : word) = Some W_ba778.
Proof. vm_refl. Qed.
Lemma D_ba778 : decode_any W_ba778 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba77c : bv 32 := 0x00800713.
Lemma F_ba77c : fetch_word Ubsan.M.loaded_segments (0xbe1a4 : word) = Some W_ba77c.
Proof. vm_refl. Qed.
Lemma D_ba77c : decode_any W_ba77c = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba780 : bv 32 := 0x00e66e63.
Lemma F_ba780 : fetch_word Ubsan.M.loaded_segments (0xbe1a8 : word) = Some W_ba780.
Proof. vm_refl. Qed.
Lemma D_ba780 : decode_any W_ba780 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba784 : bv 32 := 0x0005a703.
Lemma F_ba784 : fetch_word Ubsan.M.loaded_segments (0xbe1ac : word) = Some W_ba784.
Proof. vm_refl. Qed.
Lemma D_ba784 : decode_any W_ba784 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba788 : bv 32 := 0x0045a783.
Lemma F_ba788 : fetch_word Ubsan.M.loaded_segments (0xbe1b0 : word) = Some W_ba788.
Proof. vm_refl. Qed.
Lemma D_ba788 : decode_any W_ba788 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba78c : bv 32 := 0x00e6a023.
Lemma F_ba78c : fetch_word Ubsan.M.loaded_segments (0xbe1b4 : word) = Some W_ba78c.
Proof. vm_refl. Qed.
Lemma D_ba78c : decode_any W_ba78c = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba790 : bv 32 := 0x00f6a223.
Lemma F_ba790 : fetch_word Ubsan.M.loaded_segments (0xbe1b8 : word) = Some W_ba790.
Proof. vm_refl. Qed.
Lemma D_ba790 : decode_any W_ba790 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba794 : bv 32 := 0x00868693.
Lemma F_ba794 : fetch_word Ubsan.M.loaded_segments (0xbe1bc : word) = Some W_ba794.
Proof. vm_refl. Qed.
Lemma D_ba794 : decode_any W_ba794 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba798 : bv 32 := 0x00858593.
Lemma F_ba798 : fetch_word Ubsan.M.loaded_segments (0xbe1c0 : word) = Some W_ba798.
Proof. vm_refl. Qed.
Lemma D_ba798 : decode_any W_ba798 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba79c : bv 32 := 0x00467713.
Lemma F_ba79c : fetch_word Ubsan.M.loaded_segments (0xbe1c4 : word) = Some W_ba79c.
Proof. vm_refl. Qed.
Lemma D_ba79c : decode_any W_ba79c = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba7a0 : bv 32 := 0x24070063.
Lemma F_ba7a0 : fetch_word Ubsan.M.loaded_segments (0xbe1c8 : word) = Some W_ba7a0.
Proof. vm_refl. Qed.
Lemma D_ba7a0 : decode_any W_ba7a0 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba7a4 : bv 32 := 0x0005a703.
Lemma F_ba7a4 : fetch_word Ubsan.M.loaded_segments (0xbe1cc : word) = Some W_ba7a4.
Proof. vm_refl. Qed.
Lemma D_ba7a4 : decode_any W_ba7a4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba7a8 : bv 32 := 0x00458593.
Lemma F_ba7a8 : fetch_word Ubsan.M.loaded_segments (0xbe1d0 : word) = Some W_ba7a8.
Proof. vm_refl. Qed.
Lemma D_ba7a8 : decode_any W_ba7a8 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba7ac : bv 32 := 0x00e6a023.
Lemma F_ba7ac : fetch_word Ubsan.M.loaded_segments (0xbe1d4 : word) = Some W_ba7ac.
Proof. vm_refl. Qed.
Lemma D_ba7ac : decode_any W_ba7ac = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba7b0 : bv 32 := 0x00468693.
Lemma F_ba7b0 : fetch_word Ubsan.M.loaded_segments (0xbe1d8 : word) = Some W_ba7b0.
Proof. vm_refl. Qed.
Lemma D_ba7b0 : decode_any W_ba7b0 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba7b4 : bv 32 := 0x22c0006f.
Lemma F_ba7b4 : fetch_word Ubsan.M.loaded_segments (0xbe1dc : word) = Some W_ba7b4.
Proof. vm_refl. Qed.
Lemma D_ba7b4 : decode_any W_ba7b4 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba7b8 : bv 32 := 0x00e68023.
Lemma F_ba7b8 : fetch_word Ubsan.M.loaded_segments (0xbe1e0 : word) = Some W_ba7b8.
Proof. vm_refl. Qed.
Lemma D_ba7b8 : decode_any W_ba7b8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba7bc : bv 32 := 0x00168693.
Lemma F_ba7bc : fetch_word Ubsan.M.loaded_segments (0xbe1e4 : word) = Some W_ba7bc.
Proof. vm_refl. Qed.
Lemma D_ba7bc : decode_any W_ba7bc = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba7c0 : bv 32 := 0xfff60613.
Lemma F_ba7c0 : fetch_word Ubsan.M.loaded_segments (0xbe1e8 : word) = Some W_ba7c0.
Proof. vm_refl. Qed.
Lemma D_ba7c0 : decode_any W_ba7c0 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba7c4 : bv 32 := 0x01058593.
Lemma F_ba7c4 : fetch_word Ubsan.M.loaded_segments (0xbe1ec : word) = Some W_ba7c4.
Proof. vm_refl. Qed.
Lemma D_ba7c4 : decode_any W_ba7c4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba7c8 : bv 32 := 0x01200793.
Lemma F_ba7c8 : fetch_word Ubsan.M.loaded_segments (0xbe1f0 : word) = Some W_ba7c8.
Proof. vm_refl. Qed.
Lemma D_ba7c8 : decode_any W_ba7c8 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba7cc : bv 32 := 0x0087581b.
Lemma F_ba7cc : fetch_word Ubsan.M.loaded_segments (0xbe1f4 : word) = Some W_ba7cc.
Proof. vm_refl. Qed.
Lemma D_ba7cc : decode_any W_ba7cc = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba7d0 : bv 32 := 0xff45a883.
Lemma F_ba7d0 : fetch_word Ubsan.M.loaded_segments (0xbe1f8 : word) = Some W_ba7d0.
Proof. vm_refl. Qed.
Lemma D_ba7d0 : decode_any W_ba7d0 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba7d4 : bv 32 := 0xff85a283.
Lemma F_ba7d4 : fetch_word Ubsan.M.loaded_segments (0xbe1fc : word) = Some W_ba7d4.
Proof. vm_refl. Qed.
Lemma D_ba7d4 : decode_any W_ba7d4 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba7d8 : bv 32 := 0xffc5a303.
Lemma F_ba7d8 : fetch_word Ubsan.M.loaded_segments (0xbe200 : word) = Some W_ba7d8.
Proof. vm_refl. Qed.
Lemma D_ba7d8 : decode_any W_ba7d8 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba7dc : bv 32 := 0x0005a703.
Lemma F_ba7dc : fetch_word Ubsan.M.loaded_segments (0xbe204 : word) = Some W_ba7dc.
Proof. vm_refl. Qed.
Lemma D_ba7dc : decode_any W_ba7dc = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba7e0 : bv 32 := 0x01889393.
Lemma F_ba7e0 : fetch_word Ubsan.M.loaded_segments (0xbe208 : word) = Some W_ba7e0.
Proof. vm_refl. Qed.
Lemma D_ba7e0 : decode_any W_ba7e0 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba7e4 : bv 32 := 0x0088d89b.
Lemma F_ba7e4 : fetch_word Ubsan.M.loaded_segments (0xbe20c : word) = Some W_ba7e4.
Proof. vm_refl. Qed.
Lemma D_ba7e4 : decode_any W_ba7e4 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba7e8 : bv 32 := 0x0103e833.
Lemma F_ba7e8 : fetch_word Ubsan.M.loaded_segments (0xbe210 : word) = Some W_ba7e8.
Proof. vm_refl. Qed.
Lemma D_ba7e8 : decode_any W_ba7e8 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba7ec : bv 32 := 0x01829393.
Lemma F_ba7ec : fetch_word Ubsan.M.loaded_segments (0xbe214 : word) = Some W_ba7ec.
Proof. vm_refl. Qed.
Lemma D_ba7ec : decode_any W_ba7ec = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba7f0 : bv 32 := 0x0082d29b.
Lemma F_ba7f0 : fetch_word Ubsan.M.loaded_segments (0xbe218 : word) = Some W_ba7f0.
Proof. vm_refl. Qed.
Lemma D_ba7f0 : decode_any W_ba7f0 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba7f4 : bv 32 := 0x0113e8b3.
Lemma F_ba7f4 : fetch_word Ubsan.M.loaded_segments (0xbe21c : word) = Some W_ba7f4.
Proof. vm_refl. Qed.
Lemma D_ba7f4 : decode_any W_ba7f4 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba7f8 : bv 32 := 0x01831393.
Lemma F_ba7f8 : fetch_word Ubsan.M.loaded_segments (0xbe220 : word) = Some W_ba7f8.
Proof. vm_refl. Qed.
Lemma D_ba7f8 : decode_any W_ba7f8 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba7fc : bv 32 := 0x0083531b.
Lemma F_ba7fc : fetch_word Ubsan.M.loaded_segments (0xbe224 : word) = Some W_ba7fc.
Proof. vm_refl. Qed.
Lemma D_ba7fc : decode_any W_ba7fc = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba800 : bv 32 := 0x0053e2b3.
Lemma F_ba800 : fetch_word Ubsan.M.loaded_segments (0xbe228 : word) = Some W_ba800.
Proof. vm_refl. Qed.
Lemma D_ba800 : decode_any W_ba800 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba804 : bv 32 := 0x01871393.
Lemma F_ba804 : fetch_word Ubsan.M.loaded_segments (0xbe22c : word) = Some W_ba804.
Proof. vm_refl. Qed.
Lemma D_ba804 : decode_any W_ba804 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba808 : bv 32 := 0x0063e333.
Lemma F_ba808 : fetch_word Ubsan.M.loaded_segments (0xbe230 : word) = Some W_ba808.
Proof. vm_refl. Qed.
Lemma D_ba808 : decode_any W_ba808 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba80c : bv 32 := 0xff060613.
Lemma F_ba80c : fetch_word Ubsan.M.loaded_segments (0xbe234 : word) = Some W_ba80c.
Proof. vm_refl. Qed.
Lemma D_ba80c : decode_any W_ba80c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba810 : bv 32 := 0x0106a023.
Lemma F_ba810 : fetch_word Ubsan.M.loaded_segments (0xbe238 : word) = Some W_ba810.
Proof. vm_refl. Qed.
Lemma D_ba810 : decode_any W_ba810 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba814 : bv 32 := 0x0116a223.
Lemma F_ba814 : fetch_word Ubsan.M.loaded_segments (0xbe23c : word) = Some W_ba814.
Proof. vm_refl. Qed.
Lemma D_ba814 : decode_any W_ba814 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba818 : bv 32 := 0x0056a423.
Lemma F_ba818 : fetch_word Ubsan.M.loaded_segments (0xbe240 : word) = Some W_ba818.
Proof. vm_refl. Qed.
Lemma D_ba818 : decode_any W_ba818 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba81c : bv 32 := 0x0066a623.
Lemma F_ba81c : fetch_word Ubsan.M.loaded_segments (0xbe244 : word) = Some W_ba81c.
Proof. vm_refl. Qed.
Lemma D_ba81c : decode_any W_ba81c = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba820 : bv 32 := 0x01068693.
Lemma F_ba820 : fetch_word Ubsan.M.loaded_segments (0xbe248 : word) = Some W_ba820.
Proof. vm_refl. Qed.
Lemma D_ba820 : decode_any W_ba820 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba824 : bv 32 := 0x01058593.
Lemma F_ba824 : fetch_word Ubsan.M.loaded_segments (0xbe24c : word) = Some W_ba824.
Proof. vm_refl. Qed.
Lemma D_ba824 : decode_any W_ba824 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba828 : bv 32 := 0xfac7e2e3.
Lemma F_ba828 : fetch_word Ubsan.M.loaded_segments (0xbe250 : word) = Some W_ba828.
Proof. vm_refl. Qed.
Lemma D_ba828 : decode_any W_ba828 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba82c : bv 32 := 0xff158593.
Lemma F_ba82c : fetch_word Ubsan.M.loaded_segments (0xbe254 : word) = Some W_ba82c.
Proof. vm_refl. Qed.
Lemma D_ba82c : decode_any W_ba82c = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba830 : bv 32 := 0x01000713.
Lemma F_ba830 : fetch_word Ubsan.M.loaded_segments (0xbe258 : word) = Some W_ba830.
Proof. vm_refl. Qed.
Lemma D_ba830 : decode_any W_ba830 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba834 : bv 32 := 0xe4e666e3.
Lemma F_ba834 : fetch_word Ubsan.M.loaded_segments (0xbe25c : word) = Some W_ba834.
Proof. vm_refl. Qed.
Lemma D_ba834 : decode_any W_ba834 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba838 : bv 32 := 0x0940006f.
Lemma F_ba838 : fetch_word Ubsan.M.loaded_segments (0xbe260 : word) = Some W_ba838.
Proof. vm_refl. Qed.
Lemma D_ba838 : decode_any W_ba838 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba83c : bv 32 := 0x00875793.
Lemma F_ba83c : fetch_word Ubsan.M.loaded_segments (0xbe264 : word) = Some W_ba83c.
Proof. vm_refl. Qed.
Lemma D_ba83c : decode_any W_ba83c = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba840 : bv 32 := 0x01075813.
Lemma F_ba840 : fetch_word Ubsan.M.loaded_segments (0xbe268 : word) = Some W_ba840.
Proof. vm_refl. Qed.
Lemma D_ba840 : decode_any W_ba840 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba844 : bv 32 := 0xffd60613.
Lemma F_ba844 : fetch_word Ubsan.M.loaded_segments (0xbe26c : word) = Some W_ba844.
Proof. vm_refl. Qed.
Lemma D_ba844 : decode_any W_ba844 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba848 : bv 32 := 0x00e68023.
Lemma F_ba848 : fetch_word Ubsan.M.loaded_segments (0xbe270 : word) = Some W_ba848.
Proof. vm_refl. Qed.
Lemma D_ba848 : decode_any W_ba848 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba84c : bv 32 := 0x00f680a3.
Lemma F_ba84c : fetch_word Ubsan.M.loaded_segments (0xbe274 : word) = Some W_ba84c.
Proof. vm_refl. Qed.
Lemma D_ba84c : decode_any W_ba84c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba850 : bv 32 := 0x01068123.
Lemma F_ba850 : fetch_word Ubsan.M.loaded_segments (0xbe278 : word) = Some W_ba850.
Proof. vm_refl. Qed.
Lemma D_ba850 : decode_any W_ba850 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba854 : bv 32 := 0x00368693.
Lemma F_ba854 : fetch_word Ubsan.M.loaded_segments (0xbe27c : word) = Some W_ba854.
Proof. vm_refl. Qed.
Lemma D_ba854 : decode_any W_ba854 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba858 : bv 32 := 0x01058593.
Lemma F_ba858 : fetch_word Ubsan.M.loaded_segments (0xbe280 : word) = Some W_ba858.
Proof. vm_refl. Qed.
Lemma D_ba858 : decode_any W_ba858 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba85c : bv 32 := 0x01000793.
Lemma F_ba85c : fetch_word Ubsan.M.loaded_segments (0xbe284 : word) = Some W_ba85c.
Proof. vm_refl. Qed.
Lemma D_ba85c : decode_any W_ba85c = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba860 : bv 32 := 0x0187581b.
Lemma F_ba860 : fetch_word Ubsan.M.loaded_segments (0xbe288 : word) = Some W_ba860.
Proof. vm_refl. Qed.
Lemma D_ba860 : decode_any W_ba860 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba864 : bv 32 := 0xff45a883.
Lemma F_ba864 : fetch_word Ubsan.M.loaded_segments (0xbe28c : word) = Some W_ba864.
Proof. vm_refl. Qed.
Lemma D_ba864 : decode_any W_ba864 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba868 : bv 32 := 0xff85a283.
Lemma F_ba868 : fetch_word Ubsan.M.loaded_segments (0xbe290 : word) = Some W_ba868.
Proof. vm_refl. Qed.
Lemma D_ba868 : decode_any W_ba868 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba86c : bv 32 := 0xffc5a303.
Lemma F_ba86c : fetch_word Ubsan.M.loaded_segments (0xbe294 : word) = Some W_ba86c.
Proof. vm_refl. Qed.
Lemma D_ba86c : decode_any W_ba86c = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba870 : bv 32 := 0x0005a703.
Lemma F_ba870 : fetch_word Ubsan.M.loaded_segments (0xbe298 : word) = Some W_ba870.
Proof. vm_refl. Qed.
Lemma D_ba870 : decode_any W_ba870 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba874 : bv 32 := 0x00889393.
Lemma F_ba874 : fetch_word Ubsan.M.loaded_segments (0xbe29c : word) = Some W_ba874.
Proof. vm_refl. Qed.
Lemma D_ba874 : decode_any W_ba874 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba878 : bv 32 := 0x0188d89b.
Lemma F_ba878 : fetch_word Ubsan.M.loaded_segments (0xbe2a0 : word) = Some W_ba878.
Proof. vm_refl. Qed.
Lemma D_ba878 : decode_any W_ba878 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba87c : bv 32 := 0x0103e833.
Lemma F_ba87c : fetch_word Ubsan.M.loaded_segments (0xbe2a4 : word) = Some W_ba87c.
Proof. vm_refl. Qed.
Lemma D_ba87c : decode_any W_ba87c = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba880 : bv 32 := 0x00829393.
Lemma F_ba880 : fetch_word Ubsan.M.loaded_segments (0xbe2a8 : word) = Some W_ba880.
Proof. vm_refl. Qed.
Lemma D_ba880 : decode_any W_ba880 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba884 : bv 32 := 0x0182d29b.
Lemma F_ba884 : fetch_word Ubsan.M.loaded_segments (0xbe2ac : word) = Some W_ba884.
Proof. vm_refl. Qed.
Lemma D_ba884 : decode_any W_ba884 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba888 : bv 32 := 0x0113e8b3.
Lemma F_ba888 : fetch_word Ubsan.M.loaded_segments (0xbe2b0 : word) = Some W_ba888.
Proof. vm_refl. Qed.
Lemma D_ba888 : decode_any W_ba888 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba88c : bv 32 := 0x00831393.
Lemma F_ba88c : fetch_word Ubsan.M.loaded_segments (0xbe2b4 : word) = Some W_ba88c.
Proof. vm_refl. Qed.
Lemma D_ba88c : decode_any W_ba88c = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba890 : bv 32 := 0x0183531b.
Lemma F_ba890 : fetch_word Ubsan.M.loaded_segments (0xbe2b8 : word) = Some W_ba890.
Proof. vm_refl. Qed.
Lemma D_ba890 : decode_any W_ba890 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba894 : bv 32 := 0x0053e2b3.
Lemma F_ba894 : fetch_word Ubsan.M.loaded_segments (0xbe2bc : word) = Some W_ba894.
Proof. vm_refl. Qed.
Lemma D_ba894 : decode_any W_ba894 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba898 : bv 32 := 0x00871393.
Lemma F_ba898 : fetch_word Ubsan.M.loaded_segments (0xbe2c0 : word) = Some W_ba898.
Proof. vm_refl. Qed.
Lemma D_ba898 : decode_any W_ba898 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba89c : bv 32 := 0x0063e333.
Lemma F_ba89c : fetch_word Ubsan.M.loaded_segments (0xbe2c4 : word) = Some W_ba89c.
Proof. vm_refl. Qed.
Lemma D_ba89c : decode_any W_ba89c = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba8a0 : bv 32 := 0xff060613.
Lemma F_ba8a0 : fetch_word Ubsan.M.loaded_segments (0xbe2c8 : word) = Some W_ba8a0.
Proof. vm_refl. Qed.
Lemma D_ba8a0 : decode_any W_ba8a0 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba8a4 : bv 32 := 0x0106a023.
Lemma F_ba8a4 : fetch_word Ubsan.M.loaded_segments (0xbe2cc : word) = Some W_ba8a4.
Proof. vm_refl. Qed.
Lemma D_ba8a4 : decode_any W_ba8a4 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba8a8 : bv 32 := 0x0116a223.
Lemma F_ba8a8 : fetch_word Ubsan.M.loaded_segments (0xbe2d0 : word) = Some W_ba8a8.
Proof. vm_refl. Qed.
Lemma D_ba8a8 : decode_any W_ba8a8 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba8ac : bv 32 := 0x0056a423.
Lemma F_ba8ac : fetch_word Ubsan.M.loaded_segments (0xbe2d4 : word) = Some W_ba8ac.
Proof. vm_refl. Qed.
Lemma D_ba8ac : decode_any W_ba8ac = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba8b0 : bv 32 := 0x0066a623.
Lemma F_ba8b0 : fetch_word Ubsan.M.loaded_segments (0xbe2d8 : word) = Some W_ba8b0.
Proof. vm_refl. Qed.
Lemma D_ba8b0 : decode_any W_ba8b0 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba8b4 : bv 32 := 0x01068693.
Lemma F_ba8b4 : fetch_word Ubsan.M.loaded_segments (0xbe2dc : word) = Some W_ba8b4.
Proof. vm_refl. Qed.
Lemma D_ba8b4 : decode_any W_ba8b4 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba8b8 : bv 32 := 0x01058593.
Lemma F_ba8b8 : fetch_word Ubsan.M.loaded_segments (0xbe2e0 : word) = Some W_ba8b8.
Proof. vm_refl. Qed.
Lemma D_ba8b8 : decode_any W_ba8b8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba8bc : bv 32 := 0xfac7e2e3.
Lemma F_ba8bc : fetch_word Ubsan.M.loaded_segments (0xbe2e4 : word) = Some W_ba8bc.
Proof. vm_refl. Qed.
Lemma D_ba8bc : decode_any W_ba8bc = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba8c0 : bv 32 := 0xff358593.
Lemma F_ba8c0 : fetch_word Ubsan.M.loaded_segments (0xbe2e8 : word) = Some W_ba8c0.
Proof. vm_refl. Qed.
Lemma D_ba8c0 : decode_any W_ba8c0 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba8c4 : bv 32 := 0x01000713.
Lemma F_ba8c4 : fetch_word Ubsan.M.loaded_segments (0xbe2ec : word) = Some W_ba8c4.
Proof. vm_refl. Qed.
Lemma D_ba8c4 : decode_any W_ba8c4 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba8c8 : bv 32 := 0xdae66ce3.
Lemma F_ba8c8 : fetch_word Ubsan.M.loaded_segments (0xbe2f0 : word) = Some W_ba8c8.
Proof. vm_refl. Qed.
Lemma D_ba8c8 : decode_any W_ba8c8 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba8cc : bv 32 := 0x0005c703.
Lemma F_ba8cc : fetch_word Ubsan.M.loaded_segments (0xbe2f4 : word) = Some W_ba8cc.
Proof. vm_refl. Qed.
Lemma D_ba8cc : decode_any W_ba8cc = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba8d0 : bv 32 := 0x0015c783.
Lemma F_ba8d0 : fetch_word Ubsan.M.loaded_segments (0xbe2f8 : word) = Some W_ba8d0.
Proof. vm_refl. Qed.
Lemma D_ba8d0 : decode_any W_ba8d0 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba8d4 : bv 32 := 0x0025c803.
Lemma F_ba8d4 : fetch_word Ubsan.M.loaded_segments (0xbe2fc : word) = Some W_ba8d4.
Proof. vm_refl. Qed.
Lemma D_ba8d4 : decode_any W_ba8d4 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba8d8 : bv 32 := 0x0035c883.
Lemma F_ba8d8 : fetch_word Ubsan.M.loaded_segments (0xbe300 : word) = Some W_ba8d8.
Proof. vm_refl. Qed.
Lemma D_ba8d8 : decode_any W_ba8d8 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba8dc : bv 32 := 0x0045c283.
Lemma F_ba8dc : fetch_word Ubsan.M.loaded_segments (0xbe304 : word) = Some W_ba8dc.
Proof. vm_refl. Qed.
Lemma D_ba8dc : decode_any W_ba8dc = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba8e0 : bv 32 := 0x0055c303.
Lemma F_ba8e0 : fetch_word Ubsan.M.loaded_segments (0xbe308 : word) = Some W_ba8e0.
Proof. vm_refl. Qed.
Lemma D_ba8e0 : decode_any W_ba8e0 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba8e4 : bv 32 := 0x0065c383.
Lemma F_ba8e4 : fetch_word Ubsan.M.loaded_segments (0xbe30c : word) = Some W_ba8e4.
Proof. vm_refl. Qed.
Lemma D_ba8e4 : decode_any W_ba8e4 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba8e8 : bv 32 := 0x0075ce03.
Lemma F_ba8e8 : fetch_word Ubsan.M.loaded_segments (0xbe310 : word) = Some W_ba8e8.
Proof. vm_refl. Qed.
Lemma D_ba8e8 : decode_any W_ba8e8 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba8ec : bv 32 := 0x00e68023.
Lemma F_ba8ec : fetch_word Ubsan.M.loaded_segments (0xbe314 : word) = Some W_ba8ec.
Proof. vm_refl. Qed.
Lemma D_ba8ec : decode_any W_ba8ec = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba8f0 : bv 32 := 0x00f680a3.
Lemma F_ba8f0 : fetch_word Ubsan.M.loaded_segments (0xbe318 : word) = Some W_ba8f0.
Proof. vm_refl. Qed.
Lemma D_ba8f0 : decode_any W_ba8f0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba8f4 : bv 32 := 0x01068123.
Lemma F_ba8f4 : fetch_word Ubsan.M.loaded_segments (0xbe31c : word) = Some W_ba8f4.
Proof. vm_refl. Qed.
Lemma D_ba8f4 : decode_any W_ba8f4 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba8f8 : bv 32 := 0x011681a3.
Lemma F_ba8f8 : fetch_word Ubsan.M.loaded_segments (0xbe320 : word) = Some W_ba8f8.
Proof. vm_refl. Qed.
Lemma D_ba8f8 : decode_any W_ba8f8 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba8fc : bv 32 := 0x0085c703.
Lemma F_ba8fc : fetch_word Ubsan.M.loaded_segments (0xbe324 : word) = Some W_ba8fc.
Proof. vm_refl. Qed.
Lemma D_ba8fc : decode_any W_ba8fc = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba900 : bv 32 := 0x0095c783.
Lemma F_ba900 : fetch_word Ubsan.M.loaded_segments (0xbe328 : word) = Some W_ba900.
Proof. vm_refl. Qed.
Lemma D_ba900 : decode_any W_ba900 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba904 : bv 32 := 0x00a5c803.
Lemma F_ba904 : fetch_word Ubsan.M.loaded_segments (0xbe32c : word) = Some W_ba904.
Proof. vm_refl. Qed.
Lemma D_ba904 : decode_any W_ba904 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba908 : bv 32 := 0x00b5c883.
Lemma F_ba908 : fetch_word Ubsan.M.loaded_segments (0xbe330 : word) = Some W_ba908.
Proof. vm_refl. Qed.
Lemma D_ba908 : decode_any W_ba908 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba90c : bv 32 := 0x00568223.
Lemma F_ba90c : fetch_word Ubsan.M.loaded_segments (0xbe334 : word) = Some W_ba90c.
Proof. vm_refl. Qed.
Lemma D_ba90c : decode_any W_ba90c = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba910 : bv 32 := 0x006682a3.
Lemma F_ba910 : fetch_word Ubsan.M.loaded_segments (0xbe338 : word) = Some W_ba910.
Proof. vm_refl. Qed.
Lemma D_ba910 : decode_any W_ba910 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba914 : bv 32 := 0x00768323.
Lemma F_ba914 : fetch_word Ubsan.M.loaded_segments (0xbe33c : word) = Some W_ba914.
Proof. vm_refl. Qed.
Lemma D_ba914 : decode_any W_ba914 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba918 : bv 32 := 0x01c683a3.
Lemma F_ba918 : fetch_word Ubsan.M.loaded_segments (0xbe340 : word) = Some W_ba918.
Proof. vm_refl. Qed.
Lemma D_ba918 : decode_any W_ba918 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba91c : bv 32 := 0x00c5c283.
Lemma F_ba91c : fetch_word Ubsan.M.loaded_segments (0xbe344 : word) = Some W_ba91c.
Proof. vm_refl. Qed.
Lemma D_ba91c : decode_any W_ba91c = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba920 : bv 32 := 0x00d5c303.
Lemma F_ba920 : fetch_word Ubsan.M.loaded_segments (0xbe348 : word) = Some W_ba920.
Proof. vm_refl. Qed.
Lemma D_ba920 : decode_any W_ba920 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba924 : bv 32 := 0x00e5c383.
Lemma F_ba924 : fetch_word Ubsan.M.loaded_segments (0xbe34c : word) = Some W_ba924.
Proof. vm_refl. Qed.
Lemma D_ba924 : decode_any W_ba924 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba928 : bv 32 := 0x00f5ce03.
Lemma F_ba928 : fetch_word Ubsan.M.loaded_segments (0xbe350 : word) = Some W_ba928.
Proof. vm_refl. Qed.
Lemma D_ba928 : decode_any W_ba928 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba92c : bv 32 := 0x01058593.
Lemma F_ba92c : fetch_word Ubsan.M.loaded_segments (0xbe354 : word) = Some W_ba92c.
Proof. vm_refl. Qed.
Lemma D_ba92c : decode_any W_ba92c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba930 : bv 32 := 0x00e68423.
Lemma F_ba930 : fetch_word Ubsan.M.loaded_segments (0xbe358 : word) = Some W_ba930.
Proof. vm_refl. Qed.
Lemma D_ba930 : decode_any W_ba930 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba934 : bv 32 := 0x00f684a3.
Lemma F_ba934 : fetch_word Ubsan.M.loaded_segments (0xbe35c : word) = Some W_ba934.
Proof. vm_refl. Qed.
Lemma D_ba934 : decode_any W_ba934 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba938 : bv 32 := 0x01068523.
Lemma F_ba938 : fetch_word Ubsan.M.loaded_segments (0xbe360 : word) = Some W_ba938.
Proof. vm_refl. Qed.
Lemma D_ba938 : decode_any W_ba938 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba93c : bv 32 := 0x011685a3.
Lemma F_ba93c : fetch_word Ubsan.M.loaded_segments (0xbe364 : word) = Some W_ba93c.
Proof. vm_refl. Qed.
Lemma D_ba93c : decode_any W_ba93c = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba940 : bv 32 := 0x01068713.
Lemma F_ba940 : fetch_word Ubsan.M.loaded_segments (0xbe368 : word) = Some W_ba940.
Proof. vm_refl. Qed.
Lemma D_ba940 : decode_any W_ba940 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba944 : bv 32 := 0x00568623.
Lemma F_ba944 : fetch_word Ubsan.M.loaded_segments (0xbe36c : word) = Some W_ba944.
Proof. vm_refl. Qed.
Lemma D_ba944 : decode_any W_ba944 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba948 : bv 32 := 0x006686a3.
Lemma F_ba948 : fetch_word Ubsan.M.loaded_segments (0xbe370 : word) = Some W_ba948.
Proof. vm_refl. Qed.
Lemma D_ba948 : decode_any W_ba948 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba94c : bv 32 := 0x00768723.
Lemma F_ba94c : fetch_word Ubsan.M.loaded_segments (0xbe374 : word) = Some W_ba94c.
Proof. vm_refl. Qed.
Lemma D_ba94c : decode_any W_ba94c = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba950 : bv 32 := 0x01c687a3.
Lemma F_ba950 : fetch_word Ubsan.M.loaded_segments (0xbe378 : word) = Some W_ba950.
Proof. vm_refl. Qed.
Lemma D_ba950 : decode_any W_ba950 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba954 : bv 32 := 0x00070693.
Lemma F_ba954 : fetch_word Ubsan.M.loaded_segments (0xbe37c : word) = Some W_ba954.
Proof. vm_refl. Qed.
Lemma D_ba954 : decode_any W_ba954 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba958 : bv 32 := 0x00867713.
Lemma F_ba958 : fetch_word Ubsan.M.loaded_segments (0xbe380 : word) = Some W_ba958.
Proof. vm_refl. Qed.
Lemma D_ba958 : decode_any W_ba958 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba95c : bv 32 := 0xd20706e3.
Lemma F_ba95c : fetch_word Ubsan.M.loaded_segments (0xbe384 : word) = Some W_ba95c.
Proof. vm_refl. Qed.
Lemma D_ba95c : decode_any W_ba95c = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba960 : bv 32 := 0x0005c703.
Lemma F_ba960 : fetch_word Ubsan.M.loaded_segments (0xbe388 : word) = Some W_ba960.
Proof. vm_refl. Qed.
Lemma D_ba960 : decode_any W_ba960 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba964 : bv 32 := 0x0015c783.
Lemma F_ba964 : fetch_word Ubsan.M.loaded_segments (0xbe38c : word) = Some W_ba964.
Proof. vm_refl. Qed.
Lemma D_ba964 : decode_any W_ba964 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba968 : bv 32 := 0x0025c803.
Lemma F_ba968 : fetch_word Ubsan.M.loaded_segments (0xbe390 : word) = Some W_ba968.
Proof. vm_refl. Qed.
Lemma D_ba968 : decode_any W_ba968 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba96c : bv 32 := 0x0035c883.
Lemma F_ba96c : fetch_word Ubsan.M.loaded_segments (0xbe394 : word) = Some W_ba96c.
Proof. vm_refl. Qed.
Lemma D_ba96c : decode_any W_ba96c = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba970 : bv 32 := 0x0045c283.
Lemma F_ba970 : fetch_word Ubsan.M.loaded_segments (0xbe398 : word) = Some W_ba970.
Proof. vm_refl. Qed.
Lemma D_ba970 : decode_any W_ba970 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba974 : bv 32 := 0x0055c303.
Lemma F_ba974 : fetch_word Ubsan.M.loaded_segments (0xbe39c : word) = Some W_ba974.
Proof. vm_refl. Qed.
Lemma D_ba974 : decode_any W_ba974 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba978 : bv 32 := 0x0065c383.
Lemma F_ba978 : fetch_word Ubsan.M.loaded_segments (0xbe3a0 : word) = Some W_ba978.
Proof. vm_refl. Qed.
Lemma D_ba978 : decode_any W_ba978 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba97c : bv 32 := 0x0075ce03.
Lemma F_ba97c : fetch_word Ubsan.M.loaded_segments (0xbe3a4 : word) = Some W_ba97c.
Proof. vm_refl. Qed.
Lemma D_ba97c : decode_any W_ba97c = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba980 : bv 32 := 0x00858593.
Lemma F_ba980 : fetch_word Ubsan.M.loaded_segments (0xbe3a8 : word) = Some W_ba980.
Proof. vm_refl. Qed.
Lemma D_ba980 : decode_any W_ba980 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba984 : bv 32 := 0x00e68023.
Lemma F_ba984 : fetch_word Ubsan.M.loaded_segments (0xbe3ac : word) = Some W_ba984.
Proof. vm_refl. Qed.
Lemma D_ba984 : decode_any W_ba984 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba988 : bv 32 := 0x00f680a3.
Lemma F_ba988 : fetch_word Ubsan.M.loaded_segments (0xbe3b0 : word) = Some W_ba988.
Proof. vm_refl. Qed.
Lemma D_ba988 : decode_any W_ba988 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba98c : bv 32 := 0x01068123.
Lemma F_ba98c : fetch_word Ubsan.M.loaded_segments (0xbe3b4 : word) = Some W_ba98c.
Proof. vm_refl. Qed.
Lemma D_ba98c : decode_any W_ba98c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba990 : bv 32 := 0x011681a3.
Lemma F_ba990 : fetch_word Ubsan.M.loaded_segments (0xbe3b8 : word) = Some W_ba990.
Proof. vm_refl. Qed.
Lemma D_ba990 : decode_any W_ba990 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba994 : bv 32 := 0x00868713.
Lemma F_ba994 : fetch_word Ubsan.M.loaded_segments (0xbe3bc : word) = Some W_ba994.
Proof. vm_refl. Qed.
Lemma D_ba994 : decode_any W_ba994 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba998 : bv 32 := 0x00568223.
Lemma F_ba998 : fetch_word Ubsan.M.loaded_segments (0xbe3c0 : word) = Some W_ba998.
Proof. vm_refl. Qed.
Lemma D_ba998 : decode_any W_ba998 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba99c : bv 32 := 0x006682a3.
Lemma F_ba99c : fetch_word Ubsan.M.loaded_segments (0xbe3c4 : word) = Some W_ba99c.
Proof. vm_refl. Qed.
Lemma D_ba99c : decode_any W_ba99c = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba9a0 : bv 32 := 0x00768323.
Lemma F_ba9a0 : fetch_word Ubsan.M.loaded_segments (0xbe3c8 : word) = Some W_ba9a0.
Proof. vm_refl. Qed.
Lemma D_ba9a0 : decode_any W_ba9a0 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba9a4 : bv 32 := 0x01c683a3.
Lemma F_ba9a4 : fetch_word Ubsan.M.loaded_segments (0xbe3cc : word) = Some W_ba9a4.
Proof. vm_refl. Qed.
Lemma D_ba9a4 : decode_any W_ba9a4 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba9a8 : bv 32 := 0x00070693.
Lemma F_ba9a8 : fetch_word Ubsan.M.loaded_segments (0xbe3d0 : word) = Some W_ba9a8.
Proof. vm_refl. Qed.
Lemma D_ba9a8 : decode_any W_ba9a8 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba9ac : bv 32 := 0x00467713.
Lemma F_ba9ac : fetch_word Ubsan.M.loaded_segments (0xbe3d4 : word) = Some W_ba9ac.
Proof. vm_refl. Qed.
Lemma D_ba9ac : decode_any W_ba9ac = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba9b0 : bv 32 := 0x02070863.
Lemma F_ba9b0 : fetch_word Ubsan.M.loaded_segments (0xbe3d8 : word) = Some W_ba9b0.
Proof. vm_refl. Qed.
Lemma D_ba9b0 : decode_any W_ba9b0 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba9b4 : bv 32 := 0x0005c703.
Lemma F_ba9b4 : fetch_word Ubsan.M.loaded_segments (0xbe3dc : word) = Some W_ba9b4.
Proof. vm_refl. Qed.
Lemma D_ba9b4 : decode_any W_ba9b4 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba9b8 : bv 32 := 0x0015c783.
Lemma F_ba9b8 : fetch_word Ubsan.M.loaded_segments (0xbe3e0 : word) = Some W_ba9b8.
Proof. vm_refl. Qed.
Lemma D_ba9b8 : decode_any W_ba9b8 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba9bc : bv 32 := 0x0025c803.
Lemma F_ba9bc : fetch_word Ubsan.M.loaded_segments (0xbe3e4 : word) = Some W_ba9bc.
Proof. vm_refl. Qed.
Lemma D_ba9bc : decode_any W_ba9bc = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba9c0 : bv 32 := 0x0035c883.
Lemma F_ba9c0 : fetch_word Ubsan.M.loaded_segments (0xbe3e8 : word) = Some W_ba9c0.
Proof. vm_refl. Qed.
Lemma D_ba9c0 : decode_any W_ba9c0 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba9c4 : bv 32 := 0x00458593.
Lemma F_ba9c4 : fetch_word Ubsan.M.loaded_segments (0xbe3ec : word) = Some W_ba9c4.
Proof. vm_refl. Qed.
Lemma D_ba9c4 : decode_any W_ba9c4 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba9c8 : bv 32 := 0x00468293.
Lemma F_ba9c8 : fetch_word Ubsan.M.loaded_segments (0xbe3f0 : word) = Some W_ba9c8.
Proof. vm_refl. Qed.
Lemma D_ba9c8 : decode_any W_ba9c8 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba9cc : bv 32 := 0x00e68023.
Lemma F_ba9cc : fetch_word Ubsan.M.loaded_segments (0xbe3f4 : word) = Some W_ba9cc.
Proof. vm_refl. Qed.
Lemma D_ba9cc : decode_any W_ba9cc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba9d0 : bv 32 := 0x00f680a3.
Lemma F_ba9d0 : fetch_word Ubsan.M.loaded_segments (0xbe3f8 : word) = Some W_ba9d0.
Proof. vm_refl. Qed.
Lemma D_ba9d0 : decode_any W_ba9d0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba9d4 : bv 32 := 0x01068123.
Lemma F_ba9d4 : fetch_word Ubsan.M.loaded_segments (0xbe3fc : word) = Some W_ba9d4.
Proof. vm_refl. Qed.
Lemma D_ba9d4 : decode_any W_ba9d4 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba9d8 : bv 32 := 0x011681a3.
Lemma F_ba9d8 : fetch_word Ubsan.M.loaded_segments (0xbe400 : word) = Some W_ba9d8.
Proof. vm_refl. Qed.
Lemma D_ba9d8 : decode_any W_ba9d8 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba9dc : bv 32 := 0x00028693.
Lemma F_ba9dc : fetch_word Ubsan.M.loaded_segments (0xbe404 : word) = Some W_ba9dc.
Proof. vm_refl. Qed.
Lemma D_ba9dc : decode_any W_ba9dc = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba9e0 : bv 32 := 0x00267713.
Lemma F_ba9e0 : fetch_word Ubsan.M.loaded_segments (0xbe408 : word) = Some W_ba9e0.
Proof. vm_refl. Qed.
Lemma D_ba9e0 : decode_any W_ba9e0 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba9e4 : bv 32 := 0x00071863.
Lemma F_ba9e4 : fetch_word Ubsan.M.loaded_segments (0xbe40c : word) = Some W_ba9e4.
Proof. vm_refl. Qed.
Lemma D_ba9e4 : decode_any W_ba9e4 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba9e8 : bv 32 := 0x00167613.
Lemma F_ba9e8 : fetch_word Ubsan.M.loaded_segments (0xbe410 : word) = Some W_ba9e8.
Proof. vm_refl. Qed.
Lemma D_ba9e8 : decode_any W_ba9e8 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba9ec : bv 32 := 0x02061663.
Lemma F_ba9ec : fetch_word Ubsan.M.loaded_segments (0xbe414 : word) = Some W_ba9ec.
Proof. vm_refl. Qed.
Lemma D_ba9ec : decode_any W_ba9ec = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba9f0 : bv 32 := 0x00008067.
Lemma F_ba9f0 : fetch_word Ubsan.M.loaded_segments (0xbe418 : word) = Some W_ba9f0.
Proof. vm_refl. Qed.
Lemma D_ba9f0 : decode_any W_ba9f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba9f4 : bv 32 := 0x0005c703.
Lemma F_ba9f4 : fetch_word Ubsan.M.loaded_segments (0xbe41c : word) = Some W_ba9f4.
Proof. vm_refl. Qed.
Lemma D_ba9f4 : decode_any W_ba9f4 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba9f8 : bv 32 := 0x0015c783.
Lemma F_ba9f8 : fetch_word Ubsan.M.loaded_segments (0xbe420 : word) = Some W_ba9f8.
Proof. vm_refl. Qed.
Lemma D_ba9f8 : decode_any W_ba9f8 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ba9fc : bv 32 := 0x00258593.
Lemma F_ba9fc : fetch_word Ubsan.M.loaded_segments (0xbe424 : word) = Some W_ba9fc.
Proof. vm_refl. Qed.
Lemma D_ba9fc : decode_any W_ba9fc = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_baa00 : bv 32 := 0x00268813.
Lemma F_baa00 : fetch_word Ubsan.M.loaded_segments (0xbe428 : word) = Some W_baa00.
Proof. vm_refl. Qed.
Lemma D_baa00 : decode_any W_baa00 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_baa04 : bv 32 := 0x00e68023.
Lemma F_baa04 : fetch_word Ubsan.M.loaded_segments (0xbe42c : word) = Some W_baa04.
Proof. vm_refl. Qed.
Lemma D_baa04 : decode_any W_baa04 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_baa08 : bv 32 := 0x00f680a3.
Lemma F_baa08 : fetch_word Ubsan.M.loaded_segments (0xbe430 : word) = Some W_baa08.
Proof. vm_refl. Qed.
Lemma D_baa08 : decode_any W_baa08 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_baa0c : bv 32 := 0x00080693.
Lemma F_baa0c : fetch_word Ubsan.M.loaded_segments (0xbe434 : word) = Some W_baa0c.
Proof. vm_refl. Qed.
Lemma D_baa0c : decode_any W_baa0c = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_baa10 : bv 32 := 0x00167613.
Lemma F_baa10 : fetch_word Ubsan.M.loaded_segments (0xbe438 : word) = Some W_baa10.
Proof. vm_refl. Qed.
Lemma D_baa10 : decode_any W_baa10 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_baa14 : bv 32 := 0xfc060ee3.
Lemma F_baa14 : fetch_word Ubsan.M.loaded_segments (0xbe43c : word) = Some W_baa14.
Proof. vm_refl. Qed.
Lemma D_baa14 : decode_any W_baa14 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_baa18 : bv 32 := 0x0005c583.
Lemma F_baa18 : fetch_word Ubsan.M.loaded_segments (0xbe440 : word) = Some W_baa18.
Proof. vm_refl. Qed.
Lemma D_baa18 : decode_any W_baa18 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_baa1c : bv 32 := 0x00b68023.
Lemma F_baa1c : fetch_word Ubsan.M.loaded_segments (0xbe444 : word) = Some W_baa1c.
Proof. vm_refl. Qed.
Lemma D_baa1c : decode_any W_baa1c = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_baa20 : bv 32 := 0x00008067.
Lemma F_baa20 : fetch_word Ubsan.M.loaded_segments (0xbe448 : word) = Some W_baa20.
Proof. vm_refl. Qed.
Lemma D_baa20 : decode_any W_baa20 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_baba0 : bv 32 := 0x0e060a63.
Lemma F_baba0 : fetch_word Ubsan.M.loaded_segments (0xbe5c8 : word) = Some W_baba0.
Proof. vm_refl. Qed.
Lemma D_baba0 : decode_any W_baba0 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_baba4 : bv 32 := 0x00b50023.
Lemma F_baba4 : fetch_word Ubsan.M.loaded_segments (0xbe5cc : word) = Some W_baba4.
Proof. vm_refl. Qed.
Lemma D_baba4 : decode_any W_baba4 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_baba8 : bv 32 := 0x00c506b3.
Lemma F_baba8 : fetch_word Ubsan.M.loaded_segments (0xbe5d0 : word) = Some W_baba8.
Proof. vm_refl. Qed.
Lemma D_baba8 : decode_any W_baba8 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_babac : bv 32 := 0x00300713.
Lemma F_babac : fetch_word Ubsan.M.loaded_segments (0xbe5d4 : word) = Some W_babac.
Proof. vm_refl. Qed.
Lemma D_babac : decode_any W_babac = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_babb0 : bv 32 := 0xfeb68fa3.
Lemma F_babb0 : fetch_word Ubsan.M.loaded_segments (0xbe5d8 : word) = Some W_babb0.
Proof. vm_refl. Qed.
Lemma D_babb0 : decode_any W_babb0 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_babb4 : bv 32 := 0x0ee66063.
Lemma F_babb4 : fetch_word Ubsan.M.loaded_segments (0xbe5dc : word) = Some W_babb4.
Proof. vm_refl. Qed.
Lemma D_babb4 : decode_any W_babb4 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_babb8 : bv 32 := 0x00b500a3.
Lemma F_babb8 : fetch_word Ubsan.M.loaded_segments (0xbe5e0 : word) = Some W_babb8.
Proof. vm_refl. Qed.
Lemma D_babb8 : decode_any W_babb8 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_babbc : bv 32 := 0x00b50123.
Lemma F_babbc : fetch_word Ubsan.M.loaded_segments (0xbe5e4 : word) = Some W_babbc.
Proof. vm_refl. Qed.
Lemma D_babbc : decode_any W_babbc = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_babc0 : bv 32 := 0x00700713.
Lemma F_babc0 : fetch_word Ubsan.M.loaded_segments (0xbe5e8 : word) = Some W_babc0.
Proof. vm_refl. Qed.
Lemma D_babc0 : decode_any W_babc0 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_babc4 : bv 32 := 0xfeb68ea3.
Lemma F_babc4 : fetch_word Ubsan.M.loaded_segments (0xbe5ec : word) = Some W_babc4.
Proof. vm_refl. Qed.
Lemma D_babc4 : decode_any W_babc4 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_babc8 : bv 32 := 0xfeb68f23.
Lemma F_babc8 : fetch_word Ubsan.M.loaded_segments (0xbe5f0 : word) = Some W_babc8.
Proof. vm_refl. Qed.
Lemma D_babc8 : decode_any W_babc8 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_babcc : bv 32 := 0x0ce66463.
Lemma F_babcc : fetch_word Ubsan.M.loaded_segments (0xbe5f4 : word) = Some W_babcc.
Proof. vm_refl. Qed.
Lemma D_babcc : decode_any W_babcc = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_babd0 : bv 32 := 0x00b501a3.
Lemma F_babd0 : fetch_word Ubsan.M.loaded_segments (0xbe5f8 : word) = Some W_babd0.
Proof. vm_refl. Qed.
Lemma D_babd0 : decode_any W_babd0 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_babd4 : bv 32 := 0x00900793.
Lemma F_babd4 : fetch_word Ubsan.M.loaded_segments (0xbe5fc : word) = Some W_babd4.
Proof. vm_refl. Qed.
Lemma D_babd4 : decode_any W_babd4 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_babd8 : bv 32 := 0xfeb68e23.
Lemma F_babd8 : fetch_word Ubsan.M.loaded_segments (0xbe600 : word) = Some W_babd8.
Proof. vm_refl. Qed.
Lemma D_babd8 : decode_any W_babd8 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_babdc : bv 32 := 0x0af66c63.
Lemma F_babdc : fetch_word Ubsan.M.loaded_segments (0xbe604 : word) = Some W_babdc.
Proof. vm_refl. Qed.
Lemma D_babdc : decode_any W_babdc = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_babe0 : bv 32 := 0x40a006bb.
Lemma F_babe0 : fetch_word Ubsan.M.loaded_segments (0xbe608 : word) = Some W_babe0.
Proof. vm_refl. Qed.
Lemma D_babe0 : decode_any W_babe0 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_babe4 : bv 32 := 0x03859813.
Lemma F_babe4 : fetch_word Ubsan.M.loaded_segments (0xbe60c : word) = Some W_babe4.
Proof. vm_refl. Qed.
Lemma D_babe4 : decode_any W_babe4 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_babe8 : bv 32 := 0x101015b7.
Lemma F_babe8 : fetch_word Ubsan.M.loaded_segments (0xbe610 : word) = Some W_babe8.
Proof. vm_refl. Qed.
Lemma D_babe8 : decode_any W_babe8 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_babec : bv 32 := 0x0036f693.
Lemma F_babec : fetch_word Ubsan.M.loaded_segments (0xbe614 : word) = Some W_babec.
Proof. vm_refl. Qed.
Lemma D_babec : decode_any W_babec = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_babf0 : bv 32 := 0x00459713.
Lemma F_babf0 : fetch_word Ubsan.M.loaded_segments (0xbe618 : word) = Some W_babf0.
Proof. vm_refl. Qed.
Lemma D_babf0 : decode_any W_babf0 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_babf4 : bv 32 := 0x40d60633.
Lemma F_babf4 : fetch_word Ubsan.M.loaded_segments (0xbe61c : word) = Some W_babf4.
Proof. vm_refl. Qed.
Lemma D_babf4 : decode_any W_babf4 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_babf8 : bv 32 := 0x00d505b3.
Lemma F_babf8 : fetch_word Ubsan.M.loaded_segments (0xbe620 : word) = Some W_babf8.
Proof. vm_refl. Qed.
Lemma D_babf8 : decode_any W_babf8 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_babfc : bv 32 := 0x10070693.
Lemma F_babfc : fetch_word Ubsan.M.loaded_segments (0xbe624 : word) = Some W_babfc.
Proof. vm_refl. Qed.
Lemma D_babfc : decode_any W_babfc = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac00 : bv 32 := 0xffc67713.
Lemma F_bac00 : fetch_word Ubsan.M.loaded_segments (0xbe628 : word) = Some W_bac00.
Proof. vm_refl. Qed.
Lemma D_bac00 : decode_any W_bac00 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac04 : bv 32 := 0x02d83633.
Lemma F_bac04 : fetch_word Ubsan.M.loaded_segments (0xbe62c : word) = Some W_bac04.
Proof. vm_refl. Qed.
Lemma D_bac04 : decode_any W_bac04 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac08 : bv 32 := 0x00c5a023.
Lemma F_bac08 : fetch_word Ubsan.M.loaded_segments (0xbe630 : word) = Some W_bac08.
Proof. vm_refl. Qed.
Lemma D_bac08 : decode_any W_bac08 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac0c : bv 32 := 0x00e586b3.
Lemma F_bac0c : fetch_word Ubsan.M.loaded_segments (0xbe634 : word) = Some W_bac0c.
Proof. vm_refl. Qed.
Lemma D_bac0c : decode_any W_bac0c = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac10 : bv 32 := 0xfec6ae23.
Lemma F_bac10 : fetch_word Ubsan.M.loaded_segments (0xbe638 : word) = Some W_bac10.
Proof. vm_refl. Qed.
Lemma D_bac10 : decode_any W_bac10 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac14 : bv 32 := 0x08f76063.
Lemma F_bac14 : fetch_word Ubsan.M.loaded_segments (0xbe63c : word) = Some W_bac14.
Proof. vm_refl. Qed.
Lemma D_bac14 : decode_any W_bac14 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac18 : bv 32 := 0x00c5a223.
Lemma F_bac18 : fetch_word Ubsan.M.loaded_segments (0xbe640 : word) = Some W_bac18.
Proof. vm_refl. Qed.
Lemma D_bac18 : decode_any W_bac18 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac1c : bv 32 := 0x00c5a423.
Lemma F_bac1c : fetch_word Ubsan.M.loaded_segments (0xbe644 : word) = Some W_bac1c.
Proof. vm_refl. Qed.
Lemma D_bac1c : decode_any W_bac1c = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac20 : bv 32 := 0x01900793.
Lemma F_bac20 : fetch_word Ubsan.M.loaded_segments (0xbe648 : word) = Some W_bac20.
Proof. vm_refl. Qed.
Lemma D_bac20 : decode_any W_bac20 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac24 : bv 32 := 0xfec6aa23.
Lemma F_bac24 : fetch_word Ubsan.M.loaded_segments (0xbe64c : word) = Some W_bac24.
Proof. vm_refl. Qed.
Lemma D_bac24 : decode_any W_bac24 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac28 : bv 32 := 0xfec6ac23.
Lemma F_bac28 : fetch_word Ubsan.M.loaded_segments (0xbe650 : word) = Some W_bac28.
Proof. vm_refl. Qed.
Lemma D_bac28 : decode_any W_bac28 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac2c : bv 32 := 0x06f76463.
Lemma F_bac2c : fetch_word Ubsan.M.loaded_segments (0xbe654 : word) = Some W_bac2c.
Proof. vm_refl. Qed.
Lemma D_bac2c : decode_any W_bac2c = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac30 : bv 32 := 0x00c5a623.
Lemma F_bac30 : fetch_word Ubsan.M.loaded_segments (0xbe658 : word) = Some W_bac30.
Proof. vm_refl. Qed.
Lemma D_bac30 : decode_any W_bac30 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac34 : bv 32 := 0x00c5a823.
Lemma F_bac34 : fetch_word Ubsan.M.loaded_segments (0xbe65c : word) = Some W_bac34.
Proof. vm_refl. Qed.
Lemma D_bac34 : decode_any W_bac34 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac38 : bv 32 := 0x00c5aa23.
Lemma F_bac38 : fetch_word Ubsan.M.loaded_segments (0xbe660 : word) = Some W_bac38.
Proof. vm_refl. Qed.
Lemma D_bac38 : decode_any W_bac38 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac3c : bv 32 := 0x00c5ac23.
Lemma F_bac3c : fetch_word Ubsan.M.loaded_segments (0xbe664 : word) = Some W_bac3c.
Proof. vm_refl. Qed.
Lemma D_bac3c : decode_any W_bac3c = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac40 : bv 32 := 0x0045f793.
Lemma F_bac40 : fetch_word Ubsan.M.loaded_segments (0xbe668 : word) = Some W_bac40.
Proof. vm_refl. Qed.
Lemma D_bac40 : decode_any W_bac40 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac44 : bv 32 := 0x02000813.
Lemma F_bac44 : fetch_word Ubsan.M.loaded_segments (0xbe66c : word) = Some W_bac44.
Proof. vm_refl. Qed.
Lemma D_bac44 : decode_any W_bac44 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac48 : bv 32 := 0x01878793.
Lemma F_bac48 : fetch_word Ubsan.M.loaded_segments (0xbe670 : word) = Some W_bac48.
Proof. vm_refl. Qed.
Lemma D_bac48 : decode_any W_bac48 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac4c : bv 32 := 0x40f70733.
Lemma F_bac4c : fetch_word Ubsan.M.loaded_segments (0xbe674 : word) = Some W_bac4c.
Proof. vm_refl. Qed.
Lemma D_bac4c : decode_any W_bac4c = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac50 : bv 32 := 0xfec6a223.
Lemma F_bac50 : fetch_word Ubsan.M.loaded_segments (0xbe678 : word) = Some W_bac50.
Proof. vm_refl. Qed.
Lemma D_bac50 : decode_any W_bac50 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac54 : bv 32 := 0xfec6a423.
Lemma F_bac54 : fetch_word Ubsan.M.loaded_segments (0xbe67c : word) = Some W_bac54.
Proof. vm_refl. Qed.
Lemma D_bac54 : decode_any W_bac54 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac58 : bv 32 := 0xfec6a623.
Lemma F_bac58 : fetch_word Ubsan.M.loaded_segments (0xbe680 : word) = Some W_bac58.
Proof. vm_refl. Qed.
Lemma D_bac58 : decode_any W_bac58 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac5c : bv 32 := 0xfec6a823.
Lemma F_bac5c : fetch_word Ubsan.M.loaded_segments (0xbe684 : word) = Some W_bac5c.
Proof. vm_refl. Qed.
Lemma D_bac5c : decode_any W_bac5c = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac60 : bv 32 := 0x03076a63.
Lemma F_bac60 : fetch_word Ubsan.M.loaded_segments (0xbe688 : word) = Some W_bac60.
Proof. vm_refl. Qed.
Lemma D_bac60 : decode_any W_bac60 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac64 : bv 32 := 0x02061613.
Lemma F_bac64 : fetch_word Ubsan.M.loaded_segments (0xbe68c : word) = Some W_bac64.
Proof. vm_refl. Qed.
Lemma D_bac64 : decode_any W_bac64 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac68 : bv 32 := 0x00f585b3.
Lemma F_bac68 : fetch_word Ubsan.M.loaded_segments (0xbe690 : word) = Some W_bac68.
Proof. vm_refl. Qed.
Lemma D_bac68 : decode_any W_bac68 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac6c : bv 32 := 0x02065693.
Lemma F_bac6c : fetch_word Ubsan.M.loaded_segments (0xbe694 : word) = Some W_bac6c.
Proof. vm_refl. Qed.
Lemma D_bac6c : decode_any W_bac6c = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac70 : bv 32 := 0x00d66633.
Lemma F_bac70 : fetch_word Ubsan.M.loaded_segments (0xbe698 : word) = Some W_bac70.
Proof. vm_refl. Qed.
Lemma D_bac70 : decode_any W_bac70 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac74 : bv 32 := 0x01f00693.
Lemma F_bac74 : fetch_word Ubsan.M.loaded_segments (0xbe69c : word) = Some W_bac74.
Proof. vm_refl. Qed.
Lemma D_bac74 : decode_any W_bac74 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac78 : bv 32 := 0x00c5b023.
Lemma F_bac78 : fetch_word Ubsan.M.loaded_segments (0xbe6a0 : word) = Some W_bac78.
Proof. vm_refl. Qed.
Lemma D_bac78 : decode_any W_bac78 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac7c : bv 32 := 0x00c5b423.
Lemma F_bac7c : fetch_word Ubsan.M.loaded_segments (0xbe6a4 : word) = Some W_bac7c.
Proof. vm_refl. Qed.
Lemma D_bac7c : decode_any W_bac7c = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac80 : bv 32 := 0x00c5b823.
Lemma F_bac80 : fetch_word Ubsan.M.loaded_segments (0xbe6a8 : word) = Some W_bac80.
Proof. vm_refl. Qed.
Lemma D_bac80 : decode_any W_bac80 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac84 : bv 32 := 0x00c5bc23.
Lemma F_bac84 : fetch_word Ubsan.M.loaded_segments (0xbe6ac : word) = Some W_bac84.
Proof. vm_refl. Qed.
Lemma D_bac84 : decode_any W_bac84 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac88 : bv 32 := 0xfe070713.
Lemma F_bac88 : fetch_word Ubsan.M.loaded_segments (0xbe6b0 : word) = Some W_bac88.
Proof. vm_refl. Qed.
Lemma D_bac88 : decode_any W_bac88 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac8c : bv 32 := 0x02058593.
Lemma F_bac8c : fetch_word Ubsan.M.loaded_segments (0xbe6b4 : word) = Some W_bac8c.
Proof. vm_refl. Qed.
Lemma D_bac8c : decode_any W_bac8c = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac90 : bv 32 := 0xfee6e4e3.
Lemma F_bac90 : fetch_word Ubsan.M.loaded_segments (0xbe6b8 : word) = Some W_bac90.
Proof. vm_refl. Qed.
Lemma D_bac90 : decode_any W_bac90 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bac94 : bv 32 := 0x00008067.
Lemma F_bac94 : fetch_word Ubsan.M.loaded_segments (0xbe6bc : word) = Some W_bac94.
Proof. vm_refl. Qed.
Lemma D_bac94 : decode_any W_bac94 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

