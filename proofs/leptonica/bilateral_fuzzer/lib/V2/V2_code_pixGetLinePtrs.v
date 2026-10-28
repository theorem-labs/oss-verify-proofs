(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_1abe0 : bv 32 := 0xfe010113.
Lemma F_1abe0 : fetch_word Ubsan.M.loaded_segments (0x1abe0 : word) = Some W_1abe0.
Proof. vm_refl. Qed.
Lemma D_1abe0 : decode_any W_1abe0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_1abe4 : bv 32 := 0x00113c23.
Lemma F_1abe4 : fetch_word Ubsan.M.loaded_segments (0x1abe4 : word) = Some W_1abe4.
Proof. vm_refl. Qed.
Lemma D_1abe4 : decode_any W_1abe4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1abe8 : bv 32 := 0x00813823.
Lemma F_1abe8 : fetch_word Ubsan.M.loaded_segments (0x1abe8 : word) = Some W_1abe8.
Proof. vm_refl. Qed.
Lemma D_1abe8 : decode_any W_1abe8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1abec : bv 32 := 0x00913423.
Lemma F_1abec : fetch_word Ubsan.M.loaded_segments (0x1abec : word) = Some W_1abec.
Proof. vm_refl. Qed.
Lemma D_1abec : decode_any W_1abec = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1abf0 : bv 32 := 0x00050413.
Lemma F_1abf0 : fetch_word Ubsan.M.loaded_segments (0x1abf0 : word) = Some W_1abf0.
Proof. vm_refl. Qed.
Lemma D_1abf0 : decode_any W_1abf0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1abf4 : bv 32 := 0x0035f513.
Lemma F_1abf4 : fetch_word Ubsan.M.loaded_segments (0x1abf4 : word) = Some W_1abf4.
Proof. vm_refl. Qed.
Lemma D_1abf4 : decode_any W_1abf4 = Some (OpImm ALU_AND 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1abf8 : bv 32 := 0x00058663.
Lemma F_1abf8 : fetch_word Ubsan.M.loaded_segments (0x1abf8 : word) = Some W_1abf8.
Proof. vm_refl. Qed.
Lemma D_1abf8 : decode_any W_1abf8 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1abfc : bv 32 := 0x12051063.
Lemma F_1abfc : fetch_word Ubsan.M.loaded_segments (0x1abfc : word) = Some W_1abfc.
Proof. vm_refl. Qed.
Lemma D_1abfc : decode_any W_1abfc = Some (Branch BC_NE 10 0 288, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac00 : bv 32 := 0x0005a023.
Lemma F_1ac00 : fetch_word Ubsan.M.loaded_segments (0x1ac00 : word) = Some W_1ac00.
Proof. vm_refl. Qed.
Lemma D_1ac00 : decode_any W_1ac00 = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac04 : bv 32 := 0x0a040263.
Lemma F_1ac04 : fetch_word Ubsan.M.loaded_segments (0x1ac04 : word) = Some W_1ac04.
Proof. vm_refl. Qed.
Lemma D_1ac04 : decode_any W_1ac04 = Some (Branch BC_EQ 8 0 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac08 : bv 32 := 0x00747613.
Lemma F_1ac08 : fetch_word Ubsan.M.loaded_segments (0x1ac08 : word) = Some W_1ac08.
Proof. vm_refl. Qed.
Lemma D_1ac08 : decode_any W_1ac08 = Some (OpImm ALU_AND 12 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac0c : bv 32 := 0x10061863.
Lemma F_1ac0c : fetch_word Ubsan.M.loaded_segments (0x1ac0c : word) = Some W_1ac0c.
Proof. vm_refl. Qed.
Lemma D_1ac0c : decode_any W_1ac0c = Some (Branch BC_NE 12 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac10 : bv 32 := 0x00442483.
Lemma F_1ac10 : fetch_word Ubsan.M.loaded_segments (0x1ac10 : word) = Some W_1ac10.
Proof. vm_refl. Qed.
Lemma D_1ac10 : decode_any W_1ac10 = Some (Load SZ4 true 9 8 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac14 : bv 32 := 0x00058663.
Lemma F_1ac14 : fetch_word Ubsan.M.loaded_segments (0x1ac14 : word) = Some W_1ac14.
Proof. vm_refl. Qed.
Lemma D_1ac14 : decode_any W_1ac14 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac18 : bv 32 := 0x10051263.
Lemma F_1ac18 : fetch_word Ubsan.M.loaded_segments (0x1ac18 : word) = Some W_1ac18.
Proof. vm_refl. Qed.
Lemma D_1ac18 : decode_any W_1ac18 = Some (Branch BC_NE 10 0 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac1c : bv 32 := 0x0095a023.
Lemma F_1ac1c : fetch_word Ubsan.M.loaded_segments (0x1ac1c : word) = Some W_1ac1c.
Proof. vm_refl. Qed.
Lemma D_1ac1c : decode_any W_1ac1c = Some (Store SZ4 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac20 : bv 32 := 0x00800593.
Lemma F_1ac20 : fetch_word Ubsan.M.loaded_segments (0x1ac20 : word) = Some W_1ac20.
Proof. vm_refl. Qed.
Lemma D_1ac20 : decode_any W_1ac20 = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac24 : bv 32 := 0x00048513.
Lemma F_1ac24 : fetch_word Ubsan.M.loaded_segments (0x1ac24 : word) = Some W_1ac24.
Proof. vm_refl. Qed.
Lemma D_1ac24 : decode_any W_1ac24 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac28 : bv 32 := 0x4d0210ef.
Lemma F_1ac28 : fetch_word Ubsan.M.loaded_segments (0x1ac28 : word) = Some W_1ac28.
Proof. vm_refl. Qed.
Lemma D_1ac28 : decode_any W_1ac28 = Some (Jal 1 136400, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac2c : bv 32 := 0x08050e63.
Lemma F_1ac2c : fetch_word Ubsan.M.loaded_segments (0x1ac2c : word) = Some W_1ac2c.
Proof. vm_refl. Qed.
Lemma D_1ac2c : decode_any W_1ac2c = Some (Branch BC_EQ 10 0 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac30 : bv 32 := 0x0c905c63.
Lemma F_1ac30 : fetch_word Ubsan.M.loaded_segments (0x1ac30 : word) = Some W_1ac30.
Proof. vm_refl. Qed.
Lemma D_1ac30 : decode_any W_1ac30 = Some (Branch BC_GE 0 9 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac34 : bv 32 := 0x00000593.
Lemma F_1ac34 : fetch_word Ubsan.M.loaded_segments (0x1ac34 : word) = Some W_1ac34.
Proof. vm_refl. Qed.
Lemma D_1ac34 : decode_any W_1ac34 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac38 : bv 32 := 0x00000613.
Lemma F_1ac38 : fetch_word Ubsan.M.loaded_segments (0x1ac38 : word) = Some W_1ac38.
Proof. vm_refl. Qed.
Lemma D_1ac38 : decode_any W_1ac38 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac3c : bv 32 := 0x01042683.
Lemma F_1ac3c : fetch_word Ubsan.M.loaded_segments (0x1ac3c : word) = Some W_1ac3c.
Proof. vm_refl. Qed.
Lemma D_1ac3c : decode_any W_1ac3c = Some (Load SZ4 true 13 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac40 : bv 32 := 0x03843703.
Lemma F_1ac40 : fetch_word Ubsan.M.loaded_segments (0x1ac40 : word) = Some W_1ac40.
Proof. vm_refl. Qed.
Lemma D_1ac40 : decode_any W_1ac40 = Some (Load SZ8 true 14 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac44 : bv 32 := 0xfff54793.
Lemma F_1ac44 : fetch_word Ubsan.M.loaded_segments (0x1ac44 : word) = Some W_1ac44.
Proof. vm_refl. Qed.
Lemma D_1ac44 : decode_any W_1ac44 = Some (OpImm ALU_XOR 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac48 : bv 32 := 0x00757813.
Lemma F_1ac48 : fetch_word Ubsan.M.loaded_segments (0x1ac48 : word) = Some W_1ac48.
Proof. vm_refl. Qed.
Lemma D_1ac48 : decode_any W_1ac48 = Some (OpImm ALU_AND 16 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac4c : bv 32 := 0x00349493.
Lemma F_1ac4c : fetch_word Ubsan.M.loaded_segments (0x1ac4c : word) = Some W_1ac4c.
Proof. vm_refl. Qed.
Lemma D_1ac4c : decode_any W_1ac4c = Some (ShiftImm ALU_SLL 9 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac50 : bv 32 := 0x00e038b3.
Lemma F_1ac50 : fetch_word Ubsan.M.loaded_segments (0x1ac50 : word) = Some W_1ac50.
Proof. vm_refl. Qed.
Lemma D_1ac50 : decode_any W_1ac50 = Some (Op ALU_SLTU 17 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac54 : bv 32 := 0x02d60333.
Lemma F_1ac54 : fetch_word Ubsan.M.loaded_segments (0x1ac54 : word) = Some W_1ac54.
Proof. vm_refl. Qed.
Lemma D_1ac54 : decode_any W_1ac54 = Some (Mul M_MUL 6 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac58 : bv 32 := 0x02d602bb.
Lemma F_1ac58 : fetch_word Ubsan.M.loaded_segments (0x1ac58 : word) = Some W_1ac58.
Proof. vm_refl. Qed.
Lemma D_1ac58 : decode_any W_1ac58 = Some (Mul32 M_MUL 5 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac5c : bv 32 := 0x0c629063.
Lemma F_1ac5c : fetch_word Ubsan.M.loaded_segments (0x1ac5c : word) = Some W_1ac5c.
Proof. vm_refl. Qed.
Lemma D_1ac5c : decode_any W_1ac5c = Some (Branch BC_NE 5 6 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac60 : bv 32 := 0x0003031b.
Lemma F_1ac60 : fetch_word Ubsan.M.loaded_segments (0x1ac60 : word) = Some W_1ac60.
Proof. vm_refl. Qed.
Lemma D_1ac60 : decode_any W_1ac60 = Some (OpImm32 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac64 : bv 32 := 0x00231293.
Lemma F_1ac64 : fetch_word Ubsan.M.loaded_segments (0x1ac64 : word) = Some W_1ac64.
Proof. vm_refl. Qed.
Lemma D_1ac64 : decode_any W_1ac64 = Some (ShiftImm ALU_SLL 5 6 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac68 : bv 32 := 0x005702b3.
Lemma F_1ac68 : fetch_word Ubsan.M.loaded_segments (0x1ac68 : word) = Some W_1ac68.
Proof. vm_refl. Qed.
Lemma D_1ac68 : decode_any W_1ac68 = Some (Op ALU_ADD 5 14 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac6c : bv 32 := 0x0012b393.
Lemma F_1ac6c : fetch_word Ubsan.M.loaded_segments (0x1ac6c : word) = Some W_1ac6c.
Proof. vm_refl. Qed.
Lemma D_1ac6c : decode_any W_1ac6c = Some (OpImm ALU_SLTU 7 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac70 : bv 32 := 0x0a788663.
Lemma F_1ac70 : fetch_word Ubsan.M.loaded_segments (0x1ac70 : word) = Some W_1ac70.
Proof. vm_refl. Qed.
Lemma D_1ac70 : decode_any W_1ac70 = Some (Branch BC_EQ 17 7 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac74 : bv 32 := 0x00e2b3b3.
Lemma F_1ac74 : fetch_word Ubsan.M.loaded_segments (0x1ac74 : word) = Some W_1ac74.
Proof. vm_refl. Qed.
Lemma D_1ac74 : decode_any W_1ac74 = Some (Op ALU_SLTU 7 5 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac78 : bv 32 := 0x00032313.
Lemma F_1ac78 : fetch_word Ubsan.M.loaded_segments (0x1ac78 : word) = Some W_1ac78.
Proof. vm_refl. Qed.
Lemma D_1ac78 : decode_any W_1ac78 = Some (OpImm ALU_SLT 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac7c : bv 32 := 0x0063c333.
Lemma F_1ac7c : fetch_word Ubsan.M.loaded_segments (0x1ac7c : word) = Some W_1ac7c.
Proof. vm_refl. Qed.
Lemma D_1ac7c : decode_any W_1ac7c = Some (Op ALU_XOR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac80 : bv 32 := 0x00134313.
Lemma F_1ac80 : fetch_word Ubsan.M.loaded_segments (0x1ac80 : word) = Some W_1ac80.
Proof. vm_refl. Qed.
Lemma D_1ac80 : decode_any W_1ac80 = Some (OpImm ALU_XOR 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac84 : bv 32 := 0x08030c63.
Lemma F_1ac84 : fetch_word Ubsan.M.loaded_segments (0x1ac84 : word) = Some W_1ac84.
Proof. vm_refl. Qed.
Lemma D_1ac84 : decode_any W_1ac84 = Some (Branch BC_EQ 6 0 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac88 : bv 32 := 0x08b7ea63.
Lemma F_1ac88 : fetch_word Ubsan.M.loaded_segments (0x1ac88 : word) = Some W_1ac88.
Proof. vm_refl. Qed.
Lemma D_1ac88 : decode_any W_1ac88 = Some (Branch BC_LTU 15 11 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac8c : bv 32 := 0x08081863.
Lemma F_1ac8c : fetch_word Ubsan.M.loaded_segments (0x1ac8c : word) = Some W_1ac8c.
Proof. vm_refl. Qed.
Lemma D_1ac8c : decode_any W_1ac8c = Some (Branch BC_NE 16 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac90 : bv 32 := 0x00b50333.
Lemma F_1ac90 : fetch_word Ubsan.M.loaded_segments (0x1ac90 : word) = Some W_1ac90.
Proof. vm_refl. Qed.
Lemma D_1ac90 : decode_any W_1ac90 = Some (Op ALU_ADD 6 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac94 : bv 32 := 0x00858593.
Lemma F_1ac94 : fetch_word Ubsan.M.loaded_segments (0x1ac94 : word) = Some W_1ac94.
Proof. vm_refl. Qed.
Lemma D_1ac94 : decode_any W_1ac94 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac98 : bv 32 := 0x00533023.
Lemma F_1ac98 : fetch_word Ubsan.M.loaded_segments (0x1ac98 : word) = Some W_1ac98.
Proof. vm_refl. Qed.
Lemma D_1ac98 : decode_any W_1ac98 = Some (Store SZ8 6 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ac9c : bv 32 := 0x0016061b.
Lemma F_1ac9c : fetch_word Ubsan.M.loaded_segments (0x1ac9c : word) = Some W_1ac9c.
Proof. vm_refl. Qed.
Lemma D_1ac9c : decode_any W_1ac9c = Some (OpImm32 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1aca0 : bv 32 := 0xfab49ae3.
Lemma F_1aca0 : fetch_word Ubsan.M.loaded_segments (0x1aca0 : word) = Some W_1aca0.
Proof. vm_refl. Qed.
Lemma D_1aca0 : decode_any W_1aca0 = Some (Branch BC_NE 9 11 8116, 4%Z).
Proof. vm_refl. Qed.

Definition W_1aca4 : bv 32 := 0x0640006f.
Lemma F_1aca4 : fetch_word Ubsan.M.loaded_segments (0x1aca4 : word) = Some W_1aca4.
Proof. vm_refl. Qed.
Lemma D_1aca4 : decode_any W_1aca4 = Some (Jal 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_1aca8 : bv 32 := 0x0002a517.
Lemma F_1aca8 : fetch_word Ubsan.M.loaded_segments (0x1aca8 : word) = Some W_1aca8.
Proof. vm_refl. Qed.
Lemma D_1aca8 : decode_any W_1aca8 = Some (Auipc 10 42, 4%Z).
Proof. vm_refl. Qed.

Definition W_1acac : bv 32 := 0x1f053503.
Lemma F_1acac : fetch_word Ubsan.M.loaded_segments (0x1acac : word) = Some W_1acac.
Proof. vm_refl. Qed.
Lemma D_1acac : decode_any W_1acac = Some (Load SZ8 true 10 10 496, 4%Z).
Proof. vm_refl. Qed.

Definition W_1acb0 : bv 32 := 0x00052503.
Lemma F_1acb0 : fetch_word Ubsan.M.loaded_segments (0x1acb0 : word) = Some W_1acb0.
Proof. vm_refl. Qed.
Lemma D_1acb0 : decode_any W_1acb0 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1acb4 : bv 32 := 0x00600593.
Lemma F_1acb4 : fetch_word Ubsan.M.loaded_segments (0x1acb4 : word) = Some W_1acb4.
Proof. vm_refl. Qed.
Lemma D_1acb4 : decode_any W_1acb4 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_1acb8 : bv 32 := 0x04b55663.
Lemma F_1acb8 : fetch_word Ubsan.M.loaded_segments (0x1acb8 : word) = Some W_1acb8.
Proof. vm_refl. Qed.
Lemma D_1acb8 : decode_any W_1acb8 = Some (Branch BC_GE 10 11 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_1acbc : bv 32 := 0xffff5517.
Lemma F_1acbc : fetch_word Ubsan.M.loaded_segments (0x1acbc : word) = Some W_1acbc.
Proof. vm_refl. Qed.
Lemma D_1acbc : decode_any W_1acbc = Some (Auipc 10 1048565, 4%Z).
Proof. vm_refl. Qed.

Definition W_1acc0 : bv 32 := 0x7a950513.
Lemma F_1acc0 : fetch_word Ubsan.M.loaded_segments (0x1acc0 : word) = Some W_1acc0.
Proof. vm_refl. Qed.
Lemma D_1acc0 : decode_any W_1acc0 = Some (OpImm ALU_ADD 10 10 1961, 4%Z).
Proof. vm_refl. Qed.

Definition W_1acc4 : bv 32 := 0x0200006f.
Lemma F_1acc4 : fetch_word Ubsan.M.loaded_segments (0x1acc4 : word) = Some W_1acc4.
Proof. vm_refl. Qed.
Lemma D_1acc4 : decode_any W_1acc4 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1acc8 : bv 32 := 0x0002a517.
Lemma F_1acc8 : fetch_word Ubsan.M.loaded_segments (0x1acc8 : word) = Some W_1acc8.
Proof. vm_refl. Qed.
Lemma D_1acc8 : decode_any W_1acc8 = Some (Auipc 10 42, 4%Z).
Proof. vm_refl. Qed.

Definition W_1accc : bv 32 := 0x1d053503.
Lemma F_1accc : fetch_word Ubsan.M.loaded_segments (0x1accc : word) = Some W_1accc.
Proof. vm_refl. Qed.
Lemma D_1accc : decode_any W_1accc = Some (Load SZ8 true 10 10 464, 4%Z).
Proof. vm_refl. Qed.

Definition W_1acd0 : bv 32 := 0x00052503.
Lemma F_1acd0 : fetch_word Ubsan.M.loaded_segments (0x1acd0 : word) = Some W_1acd0.
Proof. vm_refl. Qed.
Lemma D_1acd0 : decode_any W_1acd0 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1acd4 : bv 32 := 0x00600593.
Lemma F_1acd4 : fetch_word Ubsan.M.loaded_segments (0x1acd4 : word) = Some W_1acd4.
Proof. vm_refl. Qed.
Lemma D_1acd4 : decode_any W_1acd4 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_1acd8 : bv 32 := 0x02b55663.
Lemma F_1acd8 : fetch_word Ubsan.M.loaded_segments (0x1acd8 : word) = Some W_1acd8.
Proof. vm_refl. Qed.
Lemma D_1acd8 : decode_any W_1acd8 = Some (Branch BC_GE 10 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_1acdc : bv 32 := 0xffff6517.
Lemma F_1acdc : fetch_word Ubsan.M.loaded_segments (0x1acdc : word) = Some W_1acdc.
Proof. vm_refl. Qed.
Lemma D_1acdc : decode_any W_1acdc = Some (Auipc 10 1048566, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ace0 : bv 32 := 0x6fc50513.
Lemma F_1ace0 : fetch_word Ubsan.M.loaded_segments (0x1ace0 : word) = Some W_1ace0.
Proof. vm_refl. Qed.
Lemma D_1ace0 : decode_any W_1ace0 = Some (OpImm ALU_ADD 10 10 1788, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ace4 : bv 32 := 0xffff7597.
Lemma F_1ace4 : fetch_word Ubsan.M.loaded_segments (0x1ace4 : word) = Some W_1ace4.
Proof. vm_refl. Qed.
Lemma D_1ace4 : decode_any W_1ace4 = Some (Auipc 11 1048567, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ace8 : bv 32 := 0xe2a58593.
Lemma F_1ace8 : fetch_word Ubsan.M.loaded_segments (0x1ace8 : word) = Some W_1ace8.
Proof. vm_refl. Qed.
Lemma D_1ace8 : decode_any W_1ace8 = Some (OpImm ALU_ADD 11 11 3626, 4%Z).
Proof. vm_refl. Qed.

Definition W_1acec : bv 32 := 0x00000613.
Lemma F_1acec : fetch_word Ubsan.M.loaded_segments (0x1acec : word) = Some W_1acec.
Proof. vm_refl. Qed.
Lemma D_1acec : decode_any W_1acec = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1acf0 : bv 32 := 0x01813083.
Lemma F_1acf0 : fetch_word Ubsan.M.loaded_segments (0x1acf0 : word) = Some W_1acf0.
Proof. vm_refl. Qed.
Lemma D_1acf0 : decode_any W_1acf0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1acf4 : bv 32 := 0x01013403.
Lemma F_1acf4 : fetch_word Ubsan.M.loaded_segments (0x1acf4 : word) = Some W_1acf4.
Proof. vm_refl. Qed.
Lemma D_1acf4 : decode_any W_1acf4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1acf8 : bv 32 := 0x00813483.
Lemma F_1acf8 : fetch_word Ubsan.M.loaded_segments (0x1acf8 : word) = Some W_1acf8.
Proof. vm_refl. Qed.
Lemma D_1acf8 : decode_any W_1acf8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1acfc : bv 32 := 0x02010113.
Lemma F_1acfc : fetch_word Ubsan.M.loaded_segments (0x1acfc : word) = Some W_1acfc.
Proof. vm_refl. Qed.
Lemma D_1acfc : decode_any W_1acfc = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ad00 : bv 32 := 0x9c4fd06f.
Lemma F_1ad00 : fetch_word Ubsan.M.loaded_segments (0x1ad00 : word) = Some W_1ad00.
Proof. vm_refl. Qed.
Lemma D_1ad00 : decode_any W_1ad00 = Some (Jal 0 2085316, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ad04 : bv 32 := 0x00000513.
Lemma F_1ad04 : fetch_word Ubsan.M.loaded_segments (0x1ad04 : word) = Some W_1ad04.
Proof. vm_refl. Qed.
Lemma D_1ad04 : decode_any W_1ad04 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ad08 : bv 32 := 0x01813083.
Lemma F_1ad08 : fetch_word Ubsan.M.loaded_segments (0x1ad08 : word) = Some W_1ad08.
Proof. vm_refl. Qed.
Lemma D_1ad08 : decode_any W_1ad08 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ad0c : bv 32 := 0x01013403.
Lemma F_1ad0c : fetch_word Ubsan.M.loaded_segments (0x1ad0c : word) = Some W_1ad0c.
Proof. vm_refl. Qed.
Lemma D_1ad0c : decode_any W_1ad0c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ad10 : bv 32 := 0x00813483.
Lemma F_1ad10 : fetch_word Ubsan.M.loaded_segments (0x1ad10 : word) = Some W_1ad10.
Proof. vm_refl. Qed.
Lemma D_1ad10 : decode_any W_1ad10 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ad14 : bv 32 := 0x02010113.
Lemma F_1ad14 : fetch_word Ubsan.M.loaded_segments (0x1ad14 : word) = Some W_1ad14.
Proof. vm_refl. Qed.
Lemma D_1ad14 : decode_any W_1ad14 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ad18 : bv 32 := 0x00008067.
Lemma F_1ad18 : fetch_word Ubsan.M.loaded_segments (0x1ad18 : word) = Some W_1ad18.
Proof. vm_refl. Qed.
Lemma D_1ad18 : decode_any W_1ad18 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ad1c : bv 32 := 0xc0001073.
Lemma F_1ad1c : fetch_word Ubsan.M.loaded_segments (0x1ad1c : word) = Some W_1ad1c.
Proof. vm_refl. Qed.
Lemma D_1ad1c : decode_any W_1ad1c = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.
