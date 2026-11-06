(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_7c61c : bv 32 := 0xfc010113.
Lemma F_7c61c : fetch_word AsanUbsan.M.loaded_segments (0x7c66c : word) = Some W_7c61c.
Proof. vm_refl. Qed.
Lemma D_7c61c : decode_any W_7c61c = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c620 : bv 32 := 0x02113c23.
Lemma F_7c620 : fetch_word AsanUbsan.M.loaded_segments (0x7c670 : word) = Some W_7c620.
Proof. vm_refl. Qed.
Lemma D_7c620 : decode_any W_7c620 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c624 : bv 32 := 0x02813823.
Lemma F_7c624 : fetch_word AsanUbsan.M.loaded_segments (0x7c674 : word) = Some W_7c624.
Proof. vm_refl. Qed.
Lemma D_7c624 : decode_any W_7c624 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c628 : bv 32 := 0x02913423.
Lemma F_7c628 : fetch_word AsanUbsan.M.loaded_segments (0x7c678 : word) = Some W_7c628.
Proof. vm_refl. Qed.
Lemma D_7c628 : decode_any W_7c628 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c62c : bv 32 := 0x03213023.
Lemma F_7c62c : fetch_word AsanUbsan.M.loaded_segments (0x7c67c : word) = Some W_7c62c.
Proof. vm_refl. Qed.
Lemma D_7c62c : decode_any W_7c62c = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c630 : bv 32 := 0x01313c23.
Lemma F_7c630 : fetch_word AsanUbsan.M.loaded_segments (0x7c680 : word) = Some W_7c630.
Proof. vm_refl. Qed.
Lemma D_7c630 : decode_any W_7c630 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c634 : bv 32 := 0x01413823.
Lemma F_7c634 : fetch_word AsanUbsan.M.loaded_segments (0x7c684 : word) = Some W_7c634.
Proof. vm_refl. Qed.
Lemma D_7c634 : decode_any W_7c634 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c638 : bv 32 := 0x01513423.
Lemma F_7c638 : fetch_word AsanUbsan.M.loaded_segments (0x7c688 : word) = Some W_7c638.
Proof. vm_refl. Qed.
Lemma D_7c638 : decode_any W_7c638 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c63c : bv 32 := 0x14058c63.
Lemma F_7c63c : fetch_word AsanUbsan.M.loaded_segments (0x7c68c : word) = Some W_7c63c.
Proof. vm_refl. Qed.
Lemma D_7c63c : decode_any W_7c63c = Some (Branch BC_EQ 11 0 344, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c640 : bv 32 := 0x00058493.
Lemma F_7c640 : fetch_word AsanUbsan.M.loaded_segments (0x7c690 : word) = Some W_7c640.
Proof. vm_refl. Qed.
Lemma D_7c640 : decode_any W_7c640 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c644 : bv 32 := 0x00050413.
Lemma F_7c644 : fetch_word AsanUbsan.M.loaded_segments (0x7c694 : word) = Some W_7c644.
Proof. vm_refl. Qed.
Lemma D_7c644 : decode_any W_7c644 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c648 : bv 32 := 0x000c1517.
Lemma F_7c648 : fetch_word AsanUbsan.M.loaded_segments (0x7c698 : word) = Some W_7c648.
Proof. vm_refl. Qed.
Lemma D_7c648 : decode_any W_7c648 = Some (Auipc 10 193, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c64c : bv 32 := 0x23053a83.
Lemma F_7c64c : fetch_word AsanUbsan.M.loaded_segments (0x7c69c : word) = Some W_7c64c.
Proof. vm_refl. Qed.
Lemma D_7c64c : decode_any W_7c64c = Some (Load SZ8 true 21 10 560, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c650 : bv 32 := 0x000ab583.
Lemma F_7c650 : fetch_word AsanUbsan.M.loaded_segments (0x7c6a0 : word) = Some W_7c650.
Proof. vm_refl. Qed.
Lemma D_7c650 : decode_any W_7c650 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c654 : bv 32 := 0xfff58513.
Lemma F_7c654 : fetch_word AsanUbsan.M.loaded_segments (0x7c6a4 : word) = Some W_7c654.
Proof. vm_refl. Qed.
Lemma D_7c654 : decode_any W_7c654 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c658 : bv 32 := 0x00a5b633.
Lemma F_7c658 : fetch_word AsanUbsan.M.loaded_segments (0x7c6a8 : word) = Some W_7c658.
Proof. vm_refl. Qed.
Lemma D_7c658 : decode_any W_7c658 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c65c : bv 32 := 0xfff60613.
Lemma F_7c65c : fetch_word AsanUbsan.M.loaded_segments (0x7c6ac : word) = Some W_7c65c.
Proof. vm_refl. Qed.
Lemma D_7c65c : decode_any W_7c65c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c660 : bv 32 := 0x00a67633.
Lemma F_7c660 : fetch_word AsanUbsan.M.loaded_segments (0x7c6b0 : word) = Some W_7c660.
Proof. vm_refl. Qed.
Lemma D_7c660 : decode_any W_7c660 = Some (Op ALU_AND 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c664 : bv 32 := 0x04867263.
Lemma F_7c664 : fetch_word AsanUbsan.M.loaded_segments (0x7c6b4 : word) = Some W_7c664.
Proof. vm_refl. Qed.
Lemma D_7c664 : decode_any W_7c664 = Some (Branch BC_GEU 12 8 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c668 : bv 32 := 0x000c1697.
Lemma F_7c668 : fetch_word AsanUbsan.M.loaded_segments (0x7c6b8 : word) = Some W_7c668.
Proof. vm_refl. Qed.
Lemma D_7c668 : decode_any W_7c668 = Some (Auipc 13 193, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c66c : bv 32 := 0x2186b683.
Lemma F_7c66c : fetch_word AsanUbsan.M.loaded_segments (0x7c6bc : word) = Some W_7c66c.
Proof. vm_refl. Qed.
Lemma D_7c66c : decode_any W_7c66c = Some (Load SZ8 true 13 13 536, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c670 : bv 32 := 0x000c1717.
Lemma F_7c670 : fetch_word AsanUbsan.M.loaded_segments (0x7c6c0 : word) = Some W_7c670.
Proof. vm_refl. Qed.
Lemma D_7c670 : decode_any W_7c670 = Some (Auipc 14 193, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c674 : bv 32 := 0x21873703.
Lemma F_7c674 : fetch_word AsanUbsan.M.loaded_segments (0x7c6c4 : word) = Some W_7c674.
Proof. vm_refl. Qed.
Lemma D_7c674 : decode_any W_7c674 = Some (Load SZ8 true 14 14 536, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c678 : bv 32 := 0x0006b803.
Lemma F_7c678 : fetch_word AsanUbsan.M.loaded_segments (0x7c6c8 : word) = Some W_7c678.
Proof. vm_refl. Qed.
Lemma D_7c678 : decode_any W_7c678 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c67c : bv 32 := 0x00073683.
Lemma F_7c67c : fetch_word AsanUbsan.M.loaded_segments (0x7c6cc : word) = Some W_7c67c.
Proof. vm_refl. Qed.
Lemma D_7c67c : decode_any W_7c67c = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c680 : bv 32 := 0xfff80793.
Lemma F_7c680 : fetch_word AsanUbsan.M.loaded_segments (0x7c6d0 : word) = Some W_7c680.
Proof. vm_refl. Qed.
Lemma D_7c680 : decode_any W_7c680 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c684 : bv 32 := 0x0087f463.
Lemma F_7c684 : fetch_word AsanUbsan.M.loaded_segments (0x7c6d4 : word) = Some W_7c684.
Proof. vm_refl. Qed.
Lemma D_7c684 : decode_any W_7c684 = Some (Branch BC_GEU 15 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c68c : bv 32 := 0x000c1717.
Lemma F_7c68c : fetch_word AsanUbsan.M.loaded_segments (0x7c6dc : word) = Some W_7c68c.
Proof. vm_refl. Qed.
Lemma D_7c68c : decode_any W_7c68c = Some (Auipc 14 193, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c690 : bv 32 := 0x20473703.
Lemma F_7c690 : fetch_word AsanUbsan.M.loaded_segments (0x7c6e0 : word) = Some W_7c690.
Proof. vm_refl. Qed.
Lemma D_7c690 : decode_any W_7c690 = Some (Load SZ8 true 14 14 516, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c694 : bv 32 := 0x00073283.
Lemma F_7c694 : fetch_word AsanUbsan.M.loaded_segments (0x7c6e4 : word) = Some W_7c694.
Proof. vm_refl. Qed.
Lemma D_7c694 : decode_any W_7c694 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c698 : bv 32 := 0x0032d713.
Lemma F_7c698 : fetch_word AsanUbsan.M.loaded_segments (0x7c6e8 : word) = Some W_7c698.
Proof. vm_refl. Qed.
Lemma D_7c698 : decode_any W_7c698 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c69c : bv 32 := 0x00b708b3.
Lemma F_7c69c : fetch_word AsanUbsan.M.loaded_segments (0x7c6ec : word) = Some W_7c69c.
Proof. vm_refl. Qed.
Lemma D_7c69c : decode_any W_7c69c = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c6a0 : bv 32 := 0x1282e063.
Lemma F_7c6a0 : fetch_word AsanUbsan.M.loaded_segments (0x7c6f0 : word) = Some W_7c6a0.
Proof. vm_refl. Qed.
Lemma D_7c6a0 : decode_any W_7c6a0 = Some (Branch BC_LTU 5 8 288, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c6a4 : bv 32 := 0x1088fe63.
Lemma F_7c6a4 : fetch_word AsanUbsan.M.loaded_segments (0x7c6f4 : word) = Some W_7c6a4.
Proof. vm_refl. Qed.
Lemma D_7c6a4 : decode_any W_7c6a4 = Some (Branch BC_GEU 17 8 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c6a8 : bv 32 := 0x00848933.
Lemma F_7c6a8 : fetch_word AsanUbsan.M.loaded_segments (0x7c6f8 : word) = Some W_7c6a8.
Proof. vm_refl. Qed.
Lemma D_7c6a8 : decode_any W_7c6a8 = Some (Op ALU_ADD 18 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c6ac : bv 32 := 0x05267263.
Lemma F_7c6ac : fetch_word AsanUbsan.M.loaded_segments (0x7c6fc : word) = Some W_7c6ac.
Proof. vm_refl. Qed.
Lemma D_7c6ac : decode_any W_7c6ac = Some (Branch BC_GEU 12 18 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c6b0 : bv 32 := 0x000c1617.
Lemma F_7c6b0 : fetch_word AsanUbsan.M.loaded_segments (0x7c700 : word) = Some W_7c6b0.
Proof. vm_refl. Qed.
Lemma D_7c6b0 : decode_any W_7c6b0 = Some (Auipc 12 193, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c6b4 : bv 32 := 0x1d063603.
Lemma F_7c6b4 : fetch_word AsanUbsan.M.loaded_segments (0x7c704 : word) = Some W_7c6b4.
Proof. vm_refl. Qed.
Lemma D_7c6b4 : decode_any W_7c6b4 = Some (Load SZ8 true 12 12 464, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c6b8 : bv 32 := 0x000c1697.
Lemma F_7c6b8 : fetch_word AsanUbsan.M.loaded_segments (0x7c708 : word) = Some W_7c6b8.
Proof. vm_refl. Qed.
Lemma D_7c6b8 : decode_any W_7c6b8 = Some (Auipc 13 193, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c6bc : bv 32 := 0x1d06b683.
Lemma F_7c6bc : fetch_word AsanUbsan.M.loaded_segments (0x7c70c : word) = Some W_7c6bc.
Proof. vm_refl. Qed.
Lemma D_7c6bc : decode_any W_7c6bc = Some (Load SZ8 true 13 13 464, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c6c0 : bv 32 := 0x00063783.
Lemma F_7c6c0 : fetch_word AsanUbsan.M.loaded_segments (0x7c710 : word) = Some W_7c6c0.
Proof. vm_refl. Qed.
Lemma D_7c6c0 : decode_any W_7c6c0 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c6c4 : bv 32 := 0x0006b603.
Lemma F_7c6c4 : fetch_word AsanUbsan.M.loaded_segments (0x7c714 : word) = Some W_7c6c4.
Proof. vm_refl. Qed.
Lemma D_7c6c4 : decode_any W_7c6c4 = Some (Load SZ8 true 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c6c8 : bv 32 := 0xfff78713.
Lemma F_7c6c8 : fetch_word AsanUbsan.M.loaded_segments (0x7c718 : word) = Some W_7c6c8.
Proof. vm_refl. Qed.
Lemma D_7c6c8 : decode_any W_7c6c8 = Some (OpImm ALU_ADD 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c6cc : bv 32 := 0x01277463.
Lemma F_7c6cc : fetch_word AsanUbsan.M.loaded_segments (0x7c71c : word) = Some W_7c6cc.
Proof. vm_refl. Qed.
Lemma D_7c6cc : decode_any W_7c6cc = Some (Branch BC_GEU 14 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c6d4 : bv 32 := 0x000c1697.
Lemma F_7c6d4 : fetch_word AsanUbsan.M.loaded_segments (0x7c724 : word) = Some W_7c6d4.
Proof. vm_refl. Qed.
Lemma D_7c6d4 : decode_any W_7c6d4 = Some (Auipc 13 193, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c6d8 : bv 32 := 0x1bc6b683.
Lemma F_7c6d8 : fetch_word AsanUbsan.M.loaded_segments (0x7c728 : word) = Some W_7c6d8.
Proof. vm_refl. Qed.
Lemma D_7c6d8 : decode_any W_7c6d8 = Some (Load SZ8 true 13 13 444, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c6dc : bv 32 := 0x0006b883.
Lemma F_7c6dc : fetch_word AsanUbsan.M.loaded_segments (0x7c72c : word) = Some W_7c6dc.
Proof. vm_refl. Qed.
Lemma D_7c6dc : decode_any W_7c6dc = Some (Load SZ8 true 17 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c6e0 : bv 32 := 0x0038d693.
Lemma F_7c6e0 : fetch_word AsanUbsan.M.loaded_segments (0x7c730 : word) = Some W_7c6e0.
Proof. vm_refl. Qed.
Lemma D_7c6e0 : decode_any W_7c6e0 = Some (ShiftImm ALU_SRL 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c6e4 : bv 32 := 0x00b68833.
Lemma F_7c6e4 : fetch_word AsanUbsan.M.loaded_segments (0x7c734 : word) = Some W_7c6e4.
Proof. vm_refl. Qed.
Lemma D_7c6e4 : decode_any W_7c6e4 = Some (Op ALU_ADD 16 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c6e8 : bv 32 := 0x1328e463.
Lemma F_7c6e8 : fetch_word AsanUbsan.M.loaded_segments (0x7c738 : word) = Some W_7c6e8.
Proof. vm_refl. Qed.
Lemma D_7c6e8 : decode_any W_7c6e8 = Some (Branch BC_LTU 17 18 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c6ec : bv 32 := 0x13287263.
Lemma F_7c6ec : fetch_word AsanUbsan.M.loaded_segments (0x7c73c : word) = Some W_7c6ec.
Proof. vm_refl. Qed.
Lemma D_7c6ec : decode_any W_7c6ec = Some (Branch BC_GEU 16 18 292, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c6f0 : bv 32 := 0x23247863.
Lemma F_7c6f0 : fetch_word AsanUbsan.M.loaded_segments (0x7c740 : word) = Some W_7c6f0.
Proof. vm_refl. Qed.
Lemma D_7c6f0 : decode_any W_7c6f0 = Some (Branch BC_GEU 8 18 560, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c6f4 : bv 32 := 0x00740513.
Lemma F_7c6f4 : fetch_word AsanUbsan.M.loaded_segments (0x7c744 : word) = Some W_7c6f4.
Proof. vm_refl. Qed.
Lemma D_7c6f4 : decode_any W_7c6f4 = Some (OpImm ALU_ADD 10 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c6f8 : bv 32 := 0xff857513.
Lemma F_7c6f8 : fetch_word AsanUbsan.M.loaded_segments (0x7c748 : word) = Some W_7c6f8.
Proof. vm_refl. Qed.
Lemma D_7c6f8 : decode_any W_7c6f8 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c6fc : bv 32 := 0xff897a13.
Lemma F_7c6fc : fetch_word AsanUbsan.M.loaded_segments (0x7c74c : word) = Some W_7c6fc.
Proof. vm_refl. Qed.
Lemma D_7c6fc : decode_any W_7c6fc = Some (OpImm ALU_AND 20 18 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c700 : bv 32 := 0xa91ff0ef.
Lemma F_7c700 : fetch_word AsanUbsan.M.loaded_segments (0x7c750 : word) = Some W_7c700.
Proof. vm_refl. Qed.
Lemma D_7c700 : decode_any W_7c700 = Some (Jal 1 2095760, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c704 : bv 32 := 0x00050993.
Lemma F_7c704 : fetch_word AsanUbsan.M.loaded_segments (0x7c754 : word) = Some W_7c704.
Proof. vm_refl. Qed.
Lemma D_7c704 : decode_any W_7c704 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c708 : bv 32 := 0x000a0513.
Lemma F_7c708 : fetch_word AsanUbsan.M.loaded_segments (0x7c758 : word) = Some W_7c708.
Proof. vm_refl. Qed.
Lemma D_7c708 : decode_any W_7c708 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c70c : bv 32 := 0xa85ff0ef.
Lemma F_7c70c : fetch_word AsanUbsan.M.loaded_segments (0x7c75c : word) = Some W_7c70c.
Proof. vm_refl. Qed.
Lemma D_7c70c : decode_any W_7c70c = Some (Jal 1 2095748, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c710 : bv 32 := 0x000ab583.
Lemma F_7c710 : fetch_word AsanUbsan.M.loaded_segments (0x7c760 : word) = Some W_7c710.
Proof. vm_refl. Qed.
Lemma D_7c710 : decode_any W_7c710 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c714 : bv 32 := 0x00345613.
Lemma F_7c714 : fetch_word AsanUbsan.M.loaded_segments (0x7c764 : word) = Some W_7c714.
Proof. vm_refl. Qed.
Lemma D_7c714 : decode_any W_7c714 = Some (ShiftImm ALU_SRL 12 8 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c718 : bv 32 := 0x00c58633.
Lemma F_7c718 : fetch_word AsanUbsan.M.loaded_segments (0x7c768 : word) = Some W_7c718.
Proof. vm_refl. Qed.
Lemma D_7c718 : decode_any W_7c718 = Some (Op ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c71c : bv 32 := 0x00060603.
Lemma F_7c71c : fetch_word AsanUbsan.M.loaded_segments (0x7c76c : word) = Some W_7c71c.
Proof. vm_refl. Qed.
Lemma D_7c71c : decode_any W_7c71c = Some (Load SZ1 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c720 : bv 32 := 0x00060663.
Lemma F_7c720 : fetch_word AsanUbsan.M.loaded_segments (0x7c770 : word) = Some W_7c720.
Proof. vm_refl. Qed.
Lemma D_7c720 : decode_any W_7c720 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c724 : bv 32 := 0x00747693.
Lemma F_7c724 : fetch_word AsanUbsan.M.loaded_segments (0x7c774 : word) = Some W_7c724.
Proof. vm_refl. Qed.
Lemma D_7c724 : decode_any W_7c724 = Some (OpImm ALU_AND 13 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c728 : bv 32 := 0x02c6d063.
Lemma F_7c728 : fetch_word AsanUbsan.M.loaded_segments (0x7c778 : word) = Some W_7c728.
Proof. vm_refl. Qed.
Lemma D_7c728 : decode_any W_7c728 = Some (Branch BC_GE 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c72c : bv 32 := 0xfff90913.
Lemma F_7c72c : fetch_word AsanUbsan.M.loaded_segments (0x7c77c : word) = Some W_7c72c.
Proof. vm_refl. Qed.
Lemma D_7c72c : decode_any W_7c72c = Some (OpImm ALU_ADD 18 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c730 : bv 32 := 0x00395613.
Lemma F_7c730 : fetch_word AsanUbsan.M.loaded_segments (0x7c780 : word) = Some W_7c730.
Proof. vm_refl. Qed.
Lemma D_7c730 : decode_any W_7c730 = Some (ShiftImm ALU_SRL 12 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c734 : bv 32 := 0x00c585b3.
Lemma F_7c734 : fetch_word AsanUbsan.M.loaded_segments (0x7c784 : word) = Some W_7c734.
Proof. vm_refl. Qed.
Lemma D_7c734 : decode_any W_7c734 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c738 : bv 32 := 0x00058583.
Lemma F_7c738 : fetch_word AsanUbsan.M.loaded_segments (0x7c788 : word) = Some W_7c738.
Proof. vm_refl. Qed.
Lemma D_7c738 : decode_any W_7c738 = Some (Load SZ1 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c73c : bv 32 := 0x04058263.
Lemma F_7c73c : fetch_word AsanUbsan.M.loaded_segments (0x7c78c : word) = Some W_7c73c.
Proof. vm_refl. Qed.
Lemma D_7c73c : decode_any W_7c73c = Some (Branch BC_EQ 11 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c740 : bv 32 := 0x00797613.
Lemma F_7c740 : fetch_word AsanUbsan.M.loaded_segments (0x7c790 : word) = Some W_7c740.
Proof. vm_refl. Qed.
Lemma D_7c740 : decode_any W_7c740 = Some (OpImm ALU_AND 12 18 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c744 : bv 32 := 0x02b64e63.
Lemma F_7c744 : fetch_word AsanUbsan.M.loaded_segments (0x7c794 : word) = Some W_7c744.
Proof. vm_refl. Qed.
Lemma D_7c744 : decode_any W_7c744 = Some (Branch BC_LT 12 11 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c780 : bv 32 := 0x00a9fa63.
Lemma F_7c780 : fetch_word AsanUbsan.M.loaded_segments (0x7c7d0 : word) = Some W_7c780.
Proof. vm_refl. Qed.
Lemma D_7c780 : decode_any W_7c780 = Some (Branch BC_GEU 19 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c784 : bv 32 := 0x413505b3.
Lemma F_7c784 : fetch_word AsanUbsan.M.loaded_segments (0x7c7d4 : word) = Some W_7c784.
Proof. vm_refl. Qed.
Lemma D_7c784 : decode_any W_7c784 = Some (Op ALU_SUB 11 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c788 : bv 32 := 0x00098513.
Lemma F_7c788 : fetch_word AsanUbsan.M.loaded_segments (0x7c7d8 : word) = Some W_7c788.
Proof. vm_refl. Qed.
Lemma D_7c788 : decode_any W_7c788 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c78c : bv 32 := 0x37c100ef.
Lemma F_7c78c : fetch_word AsanUbsan.M.loaded_segments (0x7c7dc : word) = Some W_7c78c.
Proof. vm_refl. Qed.
Lemma D_7c78c : decode_any W_7c78c = Some (Jal 1 66428, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c790 : bv 32 := 0xfa050ce3.
Lemma F_7c790 : fetch_word AsanUbsan.M.loaded_segments (0x7c7e0 : word) = Some W_7c790.
Proof. vm_refl. Qed.
Lemma D_7c790 : decode_any W_7c790 = Some (Branch BC_EQ 10 0 8120, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c794 : bv 32 := 0x00000413.
Lemma F_7c794 : fetch_word AsanUbsan.M.loaded_segments (0x7c7e4 : word) = Some W_7c794.
Proof. vm_refl. Qed.
Lemma D_7c794 : decode_any W_7c794 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c798 : bv 32 := 0x00040513.
Lemma F_7c798 : fetch_word AsanUbsan.M.loaded_segments (0x7c7e8 : word) = Some W_7c798.
Proof. vm_refl. Qed.
Lemma D_7c798 : decode_any W_7c798 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c79c : bv 32 := 0x03813083.
Lemma F_7c79c : fetch_word AsanUbsan.M.loaded_segments (0x7c7ec : word) = Some W_7c79c.
Proof. vm_refl. Qed.
Lemma D_7c79c : decode_any W_7c79c = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c7a0 : bv 32 := 0x03013403.
Lemma F_7c7a0 : fetch_word AsanUbsan.M.loaded_segments (0x7c7f0 : word) = Some W_7c7a0.
Proof. vm_refl. Qed.
Lemma D_7c7a0 : decode_any W_7c7a0 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c7a4 : bv 32 := 0x02813483.
Lemma F_7c7a4 : fetch_word AsanUbsan.M.loaded_segments (0x7c7f4 : word) = Some W_7c7a4.
Proof. vm_refl. Qed.
Lemma D_7c7a4 : decode_any W_7c7a4 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c7a8 : bv 32 := 0x02013903.
Lemma F_7c7a8 : fetch_word AsanUbsan.M.loaded_segments (0x7c7f8 : word) = Some W_7c7a8.
Proof. vm_refl. Qed.
Lemma D_7c7a8 : decode_any W_7c7a8 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c7ac : bv 32 := 0x01813983.
Lemma F_7c7ac : fetch_word AsanUbsan.M.loaded_segments (0x7c7fc : word) = Some W_7c7ac.
Proof. vm_refl. Qed.
Lemma D_7c7ac : decode_any W_7c7ac = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c7b0 : bv 32 := 0x01013a03.
Lemma F_7c7b0 : fetch_word AsanUbsan.M.loaded_segments (0x7c800 : word) = Some W_7c7b0.
Proof. vm_refl. Qed.
Lemma D_7c7b0 : decode_any W_7c7b0 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c7b4 : bv 32 := 0x00813a83.
Lemma F_7c7b4 : fetch_word AsanUbsan.M.loaded_segments (0x7c804 : word) = Some W_7c7b4.
Proof. vm_refl. Qed.
Lemma D_7c7b4 : decode_any W_7c7b4 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c7b8 : bv 32 := 0x04010113.
Lemma F_7c7b8 : fetch_word AsanUbsan.M.loaded_segments (0x7c808 : word) = Some W_7c7b8.
Proof. vm_refl. Qed.
Lemma D_7c7b8 : decode_any W_7c7b8 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c7bc : bv 32 := 0x00008067.
Lemma F_7c7bc : fetch_word AsanUbsan.M.loaded_segments (0x7c80c : word) = Some W_7c7bc.
Proof. vm_refl. Qed.
Lemma D_7c7bc : decode_any W_7c7bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
