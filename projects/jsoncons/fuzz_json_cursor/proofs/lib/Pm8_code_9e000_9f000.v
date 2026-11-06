(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_9eb58 : bv 32 := 0xfc010113.
Lemma F_9eb58 : fetch_word Asan.M.loaded_segments (0x9eba8 : word) = Some W_9eb58.
Proof. vm_refl. Qed.
Lemma D_9eb58 : decode_any W_9eb58 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_9eb5c : bv 32 := 0x02113c23.
Lemma F_9eb5c : fetch_word Asan.M.loaded_segments (0x9ebac : word) = Some W_9eb5c.
Proof. vm_refl. Qed.
Lemma D_9eb5c : decode_any W_9eb5c = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_9eb60 : bv 32 := 0x02813823.
Lemma F_9eb60 : fetch_word Asan.M.loaded_segments (0x9ebb0 : word) = Some W_9eb60.
Proof. vm_refl. Qed.
Lemma D_9eb60 : decode_any W_9eb60 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9eb64 : bv 32 := 0x02913423.
Lemma F_9eb64 : fetch_word Asan.M.loaded_segments (0x9ebb4 : word) = Some W_9eb64.
Proof. vm_refl. Qed.
Lemma D_9eb64 : decode_any W_9eb64 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9eb68 : bv 32 := 0x03213023.
Lemma F_9eb68 : fetch_word Asan.M.loaded_segments (0x9ebb8 : word) = Some W_9eb68.
Proof. vm_refl. Qed.
Lemma D_9eb68 : decode_any W_9eb68 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9eb6c : bv 32 := 0x01313c23.
Lemma F_9eb6c : fetch_word Asan.M.loaded_segments (0x9ebbc : word) = Some W_9eb6c.
Proof. vm_refl. Qed.
Lemma D_9eb6c : decode_any W_9eb6c = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9eb70 : bv 32 := 0x01413823.
Lemma F_9eb70 : fetch_word Asan.M.loaded_segments (0x9ebc0 : word) = Some W_9eb70.
Proof. vm_refl. Qed.
Lemma D_9eb70 : decode_any W_9eb70 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9eb74 : bv 32 := 0x01513423.
Lemma F_9eb74 : fetch_word Asan.M.loaded_segments (0x9ebc4 : word) = Some W_9eb74.
Proof. vm_refl. Qed.
Lemma D_9eb74 : decode_any W_9eb74 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9eb78 : bv 32 := 0x00058993.
Lemma F_9eb78 : fetch_word Asan.M.loaded_segments (0x9ebc8 : word) = Some W_9eb78.
Proof. vm_refl. Qed.
Lemma D_9eb78 : decode_any W_9eb78 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9eb7c : bv 32 := 0x0085aa03.
Lemma F_9eb7c : fetch_word Asan.M.loaded_segments (0x9ebcc : word) = Some W_9eb7c.
Proof. vm_refl. Qed.
Lemma D_9eb7c : decode_any W_9eb7c = Some (Load SZ4 true 20 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9eb80 : bv 32 := 0x00c5aa83.
Lemma F_9eb80 : fetch_word Asan.M.loaded_segments (0x9ebd0 : word) = Some W_9eb80.
Proof. vm_refl. Qed.
Lemma D_9eb80 : decode_any W_9eb80 = Some (Load SZ4 true 21 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9eb84 : bv 32 := 0x015a65b3.
Lemma F_9eb84 : fetch_word Asan.M.loaded_segments (0x9ebd4 : word) = Some W_9eb84.
Proof. vm_refl. Qed.
Lemma D_9eb84 : decode_any W_9eb84 = Some (Op ALU_OR 11 20 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_9eb88 : bv 32 := 0x00059663.
Lemma F_9eb88 : fetch_word Asan.M.loaded_segments (0x9ebd8 : word) = Some W_9eb88.
Proof. vm_refl. Qed.
Lemma D_9eb88 : decode_any W_9eb88 = Some (Branch BC_NE 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9eb94 : bv 32 := 0x00050493.
Lemma F_9eb94 : fetch_word Asan.M.loaded_segments (0x9ebe4 : word) = Some W_9eb94.
Proof. vm_refl. Qed.
Lemma D_9eb94 : decode_any W_9eb94 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9eb98 : bv 32 := 0x10000513.
Lemma F_9eb98 : fetch_word Asan.M.loaded_segments (0x9ebe8 : word) = Some W_9eb98.
Proof. vm_refl. Qed.
Lemma D_9eb98 : decode_any W_9eb98 = Some (OpImm ALU_ADD 10 0 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_9eb9c : bv 32 := 0x0aaafe63.
Lemma F_9eb9c : fetch_word Asan.M.loaded_segments (0x9ebec : word) = Some W_9eb9c.
Proof. vm_refl. Qed.
Lemma D_9eb9c : decode_any W_9eb9c = Some (Branch BC_GEU 21 10 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_9eba0 : bv 32 := 0x00060413.
Lemma F_9eba0 : fetch_word Asan.M.loaded_segments (0x9ebf0 : word) = Some W_9eba0.
Proof. vm_refl. Qed.
Lemma D_9eba0 : decode_any W_9eba0 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9eba4 : bv 32 := 0x0ff00513.
Lemma F_9eba4 : fetch_word Asan.M.loaded_segments (0x9ebf4 : word) = Some W_9eba4.
Proof. vm_refl. Qed.
Lemma D_9eba4 : decode_any W_9eba4 = Some (OpImm ALU_ADD 10 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_9eba8 : bv 32 := 0x00aa6463.
Lemma F_9eba8 : fetch_word Asan.M.loaded_segments (0x9ebf8 : word) = Some W_9eba8.
Proof. vm_refl. Qed.
Lemma D_9eba8 : decode_any W_9eba8 = Some (Branch BC_LTU 20 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ebb0 : bv 32 := 0x00013023.
Lemma F_9ebb0 : fetch_word Asan.M.loaded_segments (0x9ec00 : word) = Some W_9ebb0.
Proof. vm_refl. Qed.
Lemma D_9ebb0 : decode_any W_9ebb0 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ebb4 : bv 32 := 0x00043023.
Lemma F_9ebb4 : fetch_word Asan.M.loaded_segments (0x9ec04 : word) = Some W_9ebb4.
Proof. vm_refl. Qed.
Lemma D_9ebb4 : decode_any W_9ebb4 = Some (Store SZ8 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ebb8 : bv 32 := 0x001a0913.
Lemma F_9ebb8 : fetch_word Asan.M.loaded_segments (0x9ec08 : word) = Some W_9ebb8.
Proof. vm_refl. Qed.
Lemma D_9ebb8 : decode_any W_9ebb8 = Some (OpImm ALU_ADD 18 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ebbc : bv 32 := 0x00010613.
Lemma F_9ebbc : fetch_word Asan.M.loaded_segments (0x9ec0c : word) = Some W_9ebbc.
Proof. vm_refl. Qed.
Lemma D_9ebbc : decode_any W_9ebbc = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ebc0 : bv 32 := 0x00048513.
Lemma F_9ebc0 : fetch_word Asan.M.loaded_segments (0x9ec10 : word) = Some W_9ebc0.
Proof. vm_refl. Qed.
Lemma D_9ebc0 : decode_any W_9ebc0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ebc4 : bv 32 := 0x00090593.
Lemma F_9ebc4 : fetch_word Asan.M.loaded_segments (0x9ec14 : word) = Some W_9ebc4.
Proof. vm_refl. Qed.
Lemma D_9ebc4 : decode_any W_9ebc4 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ebc8 : bv 32 := 0x00040693.
Lemma F_9ebc8 : fetch_word Asan.M.loaded_segments (0x9ec18 : word) = Some W_9ebc8.
Proof. vm_refl. Qed.
Lemma D_9ebc8 : decode_any W_9ebc8 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ebcc : bv 32 := 0x0b0000ef.
Lemma F_9ebcc : fetch_word Asan.M.loaded_segments (0x9ec1c : word) = Some W_9ebcc.
Proof. vm_refl. Qed.
Lemma D_9ebcc : decode_any W_9ebcc = Some (Jal 1 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ebd0 : bv 32 := 0x06050263.
Lemma F_9ebd0 : fetch_word Asan.M.loaded_segments (0x9ec20 : word) = Some W_9ebd0.
Proof. vm_refl. Qed.
Lemma D_9ebd0 : decode_any W_9ebd0 = Some (Branch BC_EQ 10 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ebd4 : bv 32 := 0x008a961b.
Lemma F_9ebd4 : fetch_word Asan.M.loaded_segments (0x9ec24 : word) = Some W_9ebd4.
Proof. vm_refl. Qed.
Lemma D_9ebd4 : decode_any W_9ebd4 = Some (ShiftImm32 ALU_SLL 12 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ebd8 : bv 32 := 0x0009b583.
Lemma F_9ebd8 : fetch_word Asan.M.loaded_segments (0x9ec28 : word) = Some W_9ebd8.
Proof. vm_refl. Qed.
Lemma D_9ebd8 : decode_any W_9ebd8 = Some (Load SZ8 true 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ebdc : bv 32 := 0x01466633.
Lemma F_9ebdc : fetch_word Asan.M.loaded_segments (0x9ec2c : word) = Some W_9ebdc.
Proof. vm_refl. Qed.
Lemma D_9ebdc : decode_any W_9ebdc = Some (Op ALU_OR 12 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ebe0 : bv 32 := 0x00c53023.
Lemma F_9ebe0 : fetch_word Asan.M.loaded_segments (0x9ec30 : word) = Some W_9ebe0.
Proof. vm_refl. Qed.
Lemma D_9ebe0 : decode_any W_9ebe0 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ebe4 : bv 32 := 0x00850513.
Lemma F_9ebe4 : fetch_word Asan.M.loaded_segments (0x9ec34 : word) = Some W_9ebe4.
Proof. vm_refl. Qed.
Lemma D_9ebe4 : decode_any W_9ebe4 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ebe8 : bv 32 := 0x003a1613.
Lemma F_9ebe8 : fetch_word Asan.M.loaded_segments (0x9ec38 : word) = Some W_9ebe8.
Proof. vm_refl. Qed.
Lemma D_9ebe8 : decode_any W_9ebe8 = Some (ShiftImm ALU_SLL 12 20 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ebec : bv 32 := 0x989f30ef.
Lemma F_9ebec : fetch_word Asan.M.loaded_segments (0x9ec3c : word) = Some W_9ebec.
Proof. vm_refl. Qed.
Lemma D_9ebec : decode_any W_9ebec = Some (Jal 1 2046344, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ebf0 : bv 32 := 0x00013503.
Lemma F_9ebf0 : fetch_word Asan.M.loaded_segments (0x9ec40 : word) = Some W_9ebf0.
Proof. vm_refl. Qed.
Lemma D_9ebf0 : decode_any W_9ebf0 = Some (Load SZ8 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ebf4 : bv 32 := 0x01055513.
Lemma F_9ebf4 : fetch_word Asan.M.loaded_segments (0x9ec44 : word) = Some W_9ebf4.
Proof. vm_refl. Qed.
Lemma D_9ebf4 : decode_any W_9ebf4 = Some (ShiftImm ALU_SRL 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ebf8 : bv 32 := 0xff057513.
Lemma F_9ebf8 : fetch_word Asan.M.loaded_segments (0x9ec48 : word) = Some W_9ebf8.
Proof. vm_refl. Qed.
Lemma D_9ebf8 : decode_any W_9ebf8 = Some (OpImm ALU_AND 10 10 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ebfc : bv 32 := 0x00a48533.
Lemma F_9ebfc : fetch_word Asan.M.loaded_segments (0x9ec4c : word) = Some W_9ebfc.
Proof. vm_refl. Qed.
Lemma D_9ebfc : decode_any W_9ebfc = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec00 : bv 32 := 0x01850513.
Lemma F_9ec00 : fetch_word Asan.M.loaded_segments (0x9ec50 : word) = Some W_9ec00.
Proof. vm_refl. Qed.
Lemma D_9ec00 : decode_any W_9ec00 = Some (OpImm ALU_ADD 10 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec04 : bv 32 := 0x0325252f.
Lemma F_9ec04 : fetch_word Asan.M.loaded_segments (0x9ec54 : word) = Some W_9ec04.
Proof. vm_refl. Qed.
Lemma D_9ec04 : decode_any W_9ec04 = Some (Amo AMO_ADD AW false true 10 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec08 : bv 32 := 0x001005b7.
Lemma F_9ec08 : fetch_word Asan.M.loaded_segments (0x9ec58 : word) = Some W_9ec08.
Proof. vm_refl. Qed.
Lemma D_9ec08 : decode_any W_9ec08 = Some (Lui 11 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec0c : bv 32 := 0x02051513.
Lemma F_9ec0c : fetch_word Asan.M.loaded_segments (0x9ec5c : word) = Some W_9ec0c.
Proof. vm_refl. Qed.
Lemma D_9ec0c : decode_any W_9ec0c = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec10 : bv 32 := 0x02055513.
Lemma F_9ec10 : fetch_word Asan.M.loaded_segments (0x9ec60 : word) = Some W_9ec10.
Proof. vm_refl. Qed.
Lemma D_9ec10 : decode_any W_9ec10 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec14 : bv 32 := 0x00a90533.
Lemma F_9ec14 : fetch_word Asan.M.loaded_segments (0x9ec64 : word) = Some W_9ec14.
Proof. vm_refl. Qed.
Lemma D_9ec14 : decode_any W_9ec14 = Some (Op ALU_ADD 10 18 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec18 : bv 32 := 0x00043603.
Lemma F_9ec18 : fetch_word Asan.M.loaded_segments (0x9ec68 : word) = Some W_9ec18.
Proof. vm_refl. Qed.
Lemma D_9ec18 : decode_any W_9ec18 = Some (Load SZ8 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec1c : bv 32 := 0x00b54533.
Lemma F_9ec1c : fetch_word Asan.M.loaded_segments (0x9ec6c : word) = Some W_9ec1c.
Proof. vm_refl. Qed.
Lemma D_9ec1c : decode_any W_9ec1c = Some (Op ALU_XOR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec20 : bv 32 := 0x00012583.
Lemma F_9ec20 : fetch_word Asan.M.loaded_segments (0x9ec70 : word) = Some W_9ec20.
Proof. vm_refl. Qed.
Lemma D_9ec20 : decode_any W_9ec20 = Some (Load SZ4 true 11 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec24 : bv 32 := 0x00153513.
Lemma F_9ec24 : fetch_word Asan.M.loaded_segments (0x9ec74 : word) = Some W_9ec24.
Proof. vm_refl. Qed.
Lemma D_9ec24 : decode_any W_9ec24 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec28 : bv 32 := 0x00a60533.
Lemma F_9ec28 : fetch_word Asan.M.loaded_segments (0x9ec78 : word) = Some W_9ec28.
Proof. vm_refl. Qed.
Lemma D_9ec28 : decode_any W_9ec28 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec2c : bv 32 := 0x00a43023.
Lemma F_9ec2c : fetch_word Asan.M.loaded_segments (0x9ec7c : word) = Some W_9ec2c.
Proof. vm_refl. Qed.
Lemma D_9ec2c : decode_any W_9ec2c = Some (Store SZ8 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec30 : bv 32 := 0x0015851b.
Lemma F_9ec30 : fetch_word Asan.M.loaded_segments (0x9ec80 : word) = Some W_9ec30.
Proof. vm_refl. Qed.
Lemma D_9ec30 : decode_any W_9ec30 = Some (OpImm32 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec34 : bv 32 := 0x03813083.
Lemma F_9ec34 : fetch_word Asan.M.loaded_segments (0x9ec84 : word) = Some W_9ec34.
Proof. vm_refl. Qed.
Lemma D_9ec34 : decode_any W_9ec34 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec38 : bv 32 := 0x03013403.
Lemma F_9ec38 : fetch_word Asan.M.loaded_segments (0x9ec88 : word) = Some W_9ec38.
Proof. vm_refl. Qed.
Lemma D_9ec38 : decode_any W_9ec38 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec3c : bv 32 := 0x02813483.
Lemma F_9ec3c : fetch_word Asan.M.loaded_segments (0x9ec8c : word) = Some W_9ec3c.
Proof. vm_refl. Qed.
Lemma D_9ec3c : decode_any W_9ec3c = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec40 : bv 32 := 0x02013903.
Lemma F_9ec40 : fetch_word Asan.M.loaded_segments (0x9ec90 : word) = Some W_9ec40.
Proof. vm_refl. Qed.
Lemma D_9ec40 : decode_any W_9ec40 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec44 : bv 32 := 0x01813983.
Lemma F_9ec44 : fetch_word Asan.M.loaded_segments (0x9ec94 : word) = Some W_9ec44.
Proof. vm_refl. Qed.
Lemma D_9ec44 : decode_any W_9ec44 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec48 : bv 32 := 0x01013a03.
Lemma F_9ec48 : fetch_word Asan.M.loaded_segments (0x9ec98 : word) = Some W_9ec48.
Proof. vm_refl. Qed.
Lemma D_9ec48 : decode_any W_9ec48 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec4c : bv 32 := 0x00813a83.
Lemma F_9ec4c : fetch_word Asan.M.loaded_segments (0x9ec9c : word) = Some W_9ec4c.
Proof. vm_refl. Qed.
Lemma D_9ec4c : decode_any W_9ec4c = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec50 : bv 32 := 0x04010113.
Lemma F_9ec50 : fetch_word Asan.M.loaded_segments (0x9eca0 : word) = Some W_9ec50.
Proof. vm_refl. Qed.
Lemma D_9ec50 : decode_any W_9ec50 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec54 : bv 32 := 0x00008067.
Lemma F_9ec54 : fetch_word Asan.M.loaded_segments (0x9eca4 : word) = Some W_9ec54.
Proof. vm_refl. Qed.
Lemma D_9ec54 : decode_any W_9ec54 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec7c : bv 32 := 0xff010113.
Lemma F_9ec7c : fetch_word Asan.M.loaded_segments (0x9eccc : word) = Some W_9ec7c.
Proof. vm_refl. Qed.
Lemma D_9ec7c : decode_any W_9ec7c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec80 : bv 32 := 0x00113423.
Lemma F_9ec80 : fetch_word Asan.M.loaded_segments (0x9ecd0 : word) = Some W_9ec80.
Proof. vm_refl. Qed.
Lemma D_9ec80 : decode_any W_9ec80 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec84 : bv 32 := 0x00813023.
Lemma F_9ec84 : fetch_word Asan.M.loaded_segments (0x9ecd4 : word) = Some W_9ec84.
Proof. vm_refl. Qed.
Lemma D_9ec84 : decode_any W_9ec84 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec88 : bv 32 := 0x00058793.
Lemma F_9ec88 : fetch_word Asan.M.loaded_segments (0x9ecd8 : word) = Some W_9ec88.
Proof. vm_refl. Qed.
Lemma D_9ec88 : decode_any W_9ec88 = Some (OpImm ALU_ADD 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec8c : bv 32 := 0x00050593.
Lemma F_9ec8c : fetch_word Asan.M.loaded_segments (0x9ecdc : word) = Some W_9ec8c.
Proof. vm_refl. Qed.
Lemma D_9ec8c : decode_any W_9ec8c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec90 : bv 32 := 0x00f5342f.
Lemma F_9ec90 : fetch_word Asan.M.loaded_segments (0x9ece0 : word) = Some W_9ec90.
Proof. vm_refl. Qed.
Lemma D_9ec90 : decode_any W_9ec90 = Some (Amo AMO_ADD AD false false 8 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec94 : bv 32 := 0xfff78513.
Lemma F_9ec94 : fetch_word Asan.M.loaded_segments (0x9ece4 : word) = Some W_9ec94.
Proof. vm_refl. Qed.
Lemma D_9ec94 : decode_any W_9ec94 = Some (OpImm ALU_ADD 10 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec98 : bv 32 := 0x01445293.
Lemma F_9ec98 : fetch_word Asan.M.loaded_segments (0x9ece8 : word) = Some W_9ec98.
Proof. vm_refl. Qed.
Lemma D_9ec98 : decode_any W_9ec98 = Some (ShiftImm ALU_SRL 5 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ec9c : bv 32 := 0x00850733.
Lemma F_9ec9c : fetch_word Asan.M.loaded_segments (0x9ecec : word) = Some W_9ec9c.
Proof. vm_refl. Qed.
Lemma D_9ec9c : decode_any W_9ec9c = Some (Op ALU_ADD 14 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9eca0 : bv 32 := 0x01475313.
Lemma F_9eca0 : fetch_word Asan.M.loaded_segments (0x9ecf0 : word) = Some W_9eca0.
Proof. vm_refl. Qed.
Lemma D_9eca0 : decode_any W_9eca0 = Some (ShiftImm ALU_SRL 6 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_9eca4 : bv 32 := 0x04629863.
Lemma F_9eca4 : fetch_word Asan.M.loaded_segments (0x9ecf4 : word) = Some W_9eca4.
Proof. vm_refl. Qed.
Lemma D_9eca4 : decode_any W_9eca4 = Some (Branch BC_NE 5 6 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_9eca8 : bv 32 := 0x02045513.
Lemma F_9eca8 : fetch_word Asan.M.loaded_segments (0x9ecf8 : word) = Some W_9eca8.
Proof. vm_refl. Qed.
Lemma D_9eca8 : decode_any W_9eca8 = Some (ShiftImm ALU_SRL 10 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ecac : bv 32 := 0x00050c63.
Lemma F_9ecac : fetch_word Asan.M.loaded_segments (0x9ecfc : word) = Some W_9ecac.
Proof. vm_refl. Qed.
Lemma D_9ecac : decode_any W_9ecac = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ecc4 : bv 32 := 0x00863023.
Lemma F_9ecc4 : fetch_word Asan.M.loaded_segments (0x9ed14 : word) = Some W_9ecc4.
Proof. vm_refl. Qed.
Lemma D_9ecc4 : decode_any W_9ecc4 = Some (Store SZ8 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ecc8 : bv 32 := 0x00429613.
Lemma F_9ecc8 : fetch_word Asan.M.loaded_segments (0x9ed18 : word) = Some W_9ecc8.
Proof. vm_refl. Qed.
Lemma D_9ecc8 : decode_any W_9ecc8 = Some (ShiftImm ALU_SLL 12 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_9eccc : bv 32 := 0x00c58633.
Lemma F_9eccc : fetch_word Asan.M.loaded_segments (0x9ed1c : word) = Some W_9eccc.
Proof. vm_refl. Qed.
Lemma D_9eccc : decode_any W_9eccc = Some (Op ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ecd0 : bv 32 := 0x01063503.
Lemma F_9ecd0 : fetch_word Asan.M.loaded_segments (0x9ed20 : word) = Some W_9ecd0.
Proof. vm_refl. Qed.
Lemma D_9ecd0 : decode_any W_9ecd0 = Some (Load SZ8 true 10 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ecd4 : bv 32 := 0x0a050a63.
Lemma F_9ecd4 : fetch_word Asan.M.loaded_segments (0x9ed24 : word) = Some W_9ecd4.
Proof. vm_refl. Qed.
Lemma D_9ecd4 : decode_any W_9ecd4 = Some (Branch BC_EQ 10 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ecd8 : bv 32 := 0x02c41413.
Lemma F_9ecd8 : fetch_word Asan.M.loaded_segments (0x9ed28 : word) = Some W_9ecd8.
Proof. vm_refl. Qed.
Lemma D_9ecd8 : decode_any W_9ecd8 = Some (ShiftImm ALU_SLL 8 8 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ecdc : bv 32 := 0x02945413.
Lemma F_9ecdc : fetch_word Asan.M.loaded_segments (0x9ed2c : word) = Some W_9ecdc.
Proof. vm_refl. Qed.
Lemma D_9ecdc : decode_any W_9ecdc = Some (ShiftImm ALU_SRL 8 8 41, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ece0 : bv 32 := 0x00850533.
Lemma F_9ece0 : fetch_word Asan.M.loaded_segments (0x9ed30 : word) = Some W_9ece0.
Proof. vm_refl. Qed.
Lemma D_9ece0 : decode_any W_9ece0 = Some (Op ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ece4 : bv 32 := 0x00813083.
Lemma F_9ece4 : fetch_word Asan.M.loaded_segments (0x9ed34 : word) = Some W_9ece4.
Proof. vm_refl. Qed.
Lemma D_9ece4 : decode_any W_9ece4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ece8 : bv 32 := 0x00013403.
Lemma F_9ece8 : fetch_word Asan.M.loaded_segments (0x9ed38 : word) = Some W_9ece8.
Proof. vm_refl. Qed.
Lemma D_9ece8 : decode_any W_9ece8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ecec : bv 32 := 0x01010113.
Lemma F_9ecec : fetch_word Asan.M.loaded_segments (0x9ed3c : word) = Some W_9ecec.
Proof. vm_refl. Qed.
Lemma D_9ecec : decode_any W_9ecec = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ecf0 : bv 32 := 0x00008067.
Lemma F_9ecf0 : fetch_word Asan.M.loaded_segments (0x9ed40 : word) = Some W_9ecf0.
Proof. vm_refl. Qed.
Lemma D_9ecf0 : decode_any W_9ecf0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

