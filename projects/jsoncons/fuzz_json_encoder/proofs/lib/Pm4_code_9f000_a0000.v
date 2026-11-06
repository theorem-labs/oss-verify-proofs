(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_9ff24 : bv 32 := 0xfc010113.
Lemma F_9ff24 : fetch_word Asan.M.loaded_segments (0x9ff74 : word) = Some W_9ff24.
Proof. vm_refl. Qed.
Lemma D_9ff24 : decode_any W_9ff24 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff28 : bv 32 := 0x02113c23.
Lemma F_9ff28 : fetch_word Asan.M.loaded_segments (0x9ff78 : word) = Some W_9ff28.
Proof. vm_refl. Qed.
Lemma D_9ff28 : decode_any W_9ff28 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff2c : bv 32 := 0x02813823.
Lemma F_9ff2c : fetch_word Asan.M.loaded_segments (0x9ff7c : word) = Some W_9ff2c.
Proof. vm_refl. Qed.
Lemma D_9ff2c : decode_any W_9ff2c = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff30 : bv 32 := 0x02913423.
Lemma F_9ff30 : fetch_word Asan.M.loaded_segments (0x9ff80 : word) = Some W_9ff30.
Proof. vm_refl. Qed.
Lemma D_9ff30 : decode_any W_9ff30 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff34 : bv 32 := 0x03213023.
Lemma F_9ff34 : fetch_word Asan.M.loaded_segments (0x9ff84 : word) = Some W_9ff34.
Proof. vm_refl. Qed.
Lemma D_9ff34 : decode_any W_9ff34 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff38 : bv 32 := 0x01313c23.
Lemma F_9ff38 : fetch_word Asan.M.loaded_segments (0x9ff88 : word) = Some W_9ff38.
Proof. vm_refl. Qed.
Lemma D_9ff38 : decode_any W_9ff38 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff3c : bv 32 := 0x01413823.
Lemma F_9ff3c : fetch_word Asan.M.loaded_segments (0x9ff8c : word) = Some W_9ff3c.
Proof. vm_refl. Qed.
Lemma D_9ff3c : decode_any W_9ff3c = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff40 : bv 32 := 0x01513423.
Lemma F_9ff40 : fetch_word Asan.M.loaded_segments (0x9ff90 : word) = Some W_9ff40.
Proof. vm_refl. Qed.
Lemma D_9ff40 : decode_any W_9ff40 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff44 : bv 32 := 0x00058993.
Lemma F_9ff44 : fetch_word Asan.M.loaded_segments (0x9ff94 : word) = Some W_9ff44.
Proof. vm_refl. Qed.
Lemma D_9ff44 : decode_any W_9ff44 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff48 : bv 32 := 0x0085aa03.
Lemma F_9ff48 : fetch_word Asan.M.loaded_segments (0x9ff98 : word) = Some W_9ff48.
Proof. vm_refl. Qed.
Lemma D_9ff48 : decode_any W_9ff48 = Some (Load SZ4 true 20 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff4c : bv 32 := 0x00c5aa83.
Lemma F_9ff4c : fetch_word Asan.M.loaded_segments (0x9ff9c : word) = Some W_9ff4c.
Proof. vm_refl. Qed.
Lemma D_9ff4c : decode_any W_9ff4c = Some (Load SZ4 true 21 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff50 : bv 32 := 0x015a65b3.
Lemma F_9ff50 : fetch_word Asan.M.loaded_segments (0x9ffa0 : word) = Some W_9ff50.
Proof. vm_refl. Qed.
Lemma D_9ff50 : decode_any W_9ff50 = Some (Op ALU_OR 11 20 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff54 : bv 32 := 0x00059663.
Lemma F_9ff54 : fetch_word Asan.M.loaded_segments (0x9ffa4 : word) = Some W_9ff54.
Proof. vm_refl. Qed.
Lemma D_9ff54 : decode_any W_9ff54 = Some (Branch BC_NE 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff60 : bv 32 := 0x00050493.
Lemma F_9ff60 : fetch_word Asan.M.loaded_segments (0x9ffb0 : word) = Some W_9ff60.
Proof. vm_refl. Qed.
Lemma D_9ff60 : decode_any W_9ff60 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff64 : bv 32 := 0x10000513.
Lemma F_9ff64 : fetch_word Asan.M.loaded_segments (0x9ffb4 : word) = Some W_9ff64.
Proof. vm_refl. Qed.
Lemma D_9ff64 : decode_any W_9ff64 = Some (OpImm ALU_ADD 10 0 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff68 : bv 32 := 0x0aaafe63.
Lemma F_9ff68 : fetch_word Asan.M.loaded_segments (0x9ffb8 : word) = Some W_9ff68.
Proof. vm_refl. Qed.
Lemma D_9ff68 : decode_any W_9ff68 = Some (Branch BC_GEU 21 10 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff6c : bv 32 := 0x00060413.
Lemma F_9ff6c : fetch_word Asan.M.loaded_segments (0x9ffbc : word) = Some W_9ff6c.
Proof. vm_refl. Qed.
Lemma D_9ff6c : decode_any W_9ff6c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff70 : bv 32 := 0x0ff00513.
Lemma F_9ff70 : fetch_word Asan.M.loaded_segments (0x9ffc0 : word) = Some W_9ff70.
Proof. vm_refl. Qed.
Lemma D_9ff70 : decode_any W_9ff70 = Some (OpImm ALU_ADD 10 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff74 : bv 32 := 0x00aa6463.
Lemma F_9ff74 : fetch_word Asan.M.loaded_segments (0x9ffc4 : word) = Some W_9ff74.
Proof. vm_refl. Qed.
Lemma D_9ff74 : decode_any W_9ff74 = Some (Branch BC_LTU 20 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff7c : bv 32 := 0x00013023.
Lemma F_9ff7c : fetch_word Asan.M.loaded_segments (0x9ffcc : word) = Some W_9ff7c.
Proof. vm_refl. Qed.
Lemma D_9ff7c : decode_any W_9ff7c = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff80 : bv 32 := 0x00043023.
Lemma F_9ff80 : fetch_word Asan.M.loaded_segments (0x9ffd0 : word) = Some W_9ff80.
Proof. vm_refl. Qed.
Lemma D_9ff80 : decode_any W_9ff80 = Some (Store SZ8 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff84 : bv 32 := 0x001a0913.
Lemma F_9ff84 : fetch_word Asan.M.loaded_segments (0x9ffd4 : word) = Some W_9ff84.
Proof. vm_refl. Qed.
Lemma D_9ff84 : decode_any W_9ff84 = Some (OpImm ALU_ADD 18 20 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff88 : bv 32 := 0x00010613.
Lemma F_9ff88 : fetch_word Asan.M.loaded_segments (0x9ffd8 : word) = Some W_9ff88.
Proof. vm_refl. Qed.
Lemma D_9ff88 : decode_any W_9ff88 = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff8c : bv 32 := 0x00048513.
Lemma F_9ff8c : fetch_word Asan.M.loaded_segments (0x9ffdc : word) = Some W_9ff8c.
Proof. vm_refl. Qed.
Lemma D_9ff8c : decode_any W_9ff8c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff90 : bv 32 := 0x00090593.
Lemma F_9ff90 : fetch_word Asan.M.loaded_segments (0x9ffe0 : word) = Some W_9ff90.
Proof. vm_refl. Qed.
Lemma D_9ff90 : decode_any W_9ff90 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff94 : bv 32 := 0x00040693.
Lemma F_9ff94 : fetch_word Asan.M.loaded_segments (0x9ffe4 : word) = Some W_9ff94.
Proof. vm_refl. Qed.
Lemma D_9ff94 : decode_any W_9ff94 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff98 : bv 32 := 0x0b0000ef.
Lemma F_9ff98 : fetch_word Asan.M.loaded_segments (0x9ffe8 : word) = Some W_9ff98.
Proof. vm_refl. Qed.
Lemma D_9ff98 : decode_any W_9ff98 = Some (Jal 1 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff9c : bv 32 := 0x06050263.
Lemma F_9ff9c : fetch_word Asan.M.loaded_segments (0x9ffec : word) = Some W_9ff9c.
Proof. vm_refl. Qed.
Lemma D_9ff9c : decode_any W_9ff9c = Some (Branch BC_EQ 10 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffa0 : bv 32 := 0x008a961b.
Lemma F_9ffa0 : fetch_word Asan.M.loaded_segments (0x9fff0 : word) = Some W_9ffa0.
Proof. vm_refl. Qed.
Lemma D_9ffa0 : decode_any W_9ffa0 = Some (ShiftImm32 ALU_SLL 12 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffa4 : bv 32 := 0x0009b583.
Lemma F_9ffa4 : fetch_word Asan.M.loaded_segments (0x9fff4 : word) = Some W_9ffa4.
Proof. vm_refl. Qed.
Lemma D_9ffa4 : decode_any W_9ffa4 = Some (Load SZ8 true 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffa8 : bv 32 := 0x01466633.
Lemma F_9ffa8 : fetch_word Asan.M.loaded_segments (0x9fff8 : word) = Some W_9ffa8.
Proof. vm_refl. Qed.
Lemma D_9ffa8 : decode_any W_9ffa8 = Some (Op ALU_OR 12 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffac : bv 32 := 0x00c53023.
Lemma F_9ffac : fetch_word Asan.M.loaded_segments (0x9fffc : word) = Some W_9ffac.
Proof. vm_refl. Qed.
Lemma D_9ffac : decode_any W_9ffac = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffb0 : bv 32 := 0x00850513.
Lemma F_9ffb0 : fetch_word Asan.M.loaded_segments (0xa0000 : word) = Some W_9ffb0.
Proof. vm_refl. Qed.
Lemma D_9ffb0 : decode_any W_9ffb0 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffb4 : bv 32 := 0x003a1613.
Lemma F_9ffb4 : fetch_word Asan.M.loaded_segments (0xa0004 : word) = Some W_9ffb4.
Proof. vm_refl. Qed.
Lemma D_9ffb4 : decode_any W_9ffb4 = Some (ShiftImm ALU_SLL 12 20 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffb8 : bv 32 := 0x989f30ef.
Lemma F_9ffb8 : fetch_word Asan.M.loaded_segments (0xa0008 : word) = Some W_9ffb8.
Proof. vm_refl. Qed.
Lemma D_9ffb8 : decode_any W_9ffb8 = Some (Jal 1 2046344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffbc : bv 32 := 0x00013503.
Lemma F_9ffbc : fetch_word Asan.M.loaded_segments (0xa000c : word) = Some W_9ffbc.
Proof. vm_refl. Qed.
Lemma D_9ffbc : decode_any W_9ffbc = Some (Load SZ8 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffc0 : bv 32 := 0x01055513.
Lemma F_9ffc0 : fetch_word Asan.M.loaded_segments (0xa0010 : word) = Some W_9ffc0.
Proof. vm_refl. Qed.
Lemma D_9ffc0 : decode_any W_9ffc0 = Some (ShiftImm ALU_SRL 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffc4 : bv 32 := 0xff057513.
Lemma F_9ffc4 : fetch_word Asan.M.loaded_segments (0xa0014 : word) = Some W_9ffc4.
Proof. vm_refl. Qed.
Lemma D_9ffc4 : decode_any W_9ffc4 = Some (OpImm ALU_AND 10 10 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffc8 : bv 32 := 0x00a48533.
Lemma F_9ffc8 : fetch_word Asan.M.loaded_segments (0xa0018 : word) = Some W_9ffc8.
Proof. vm_refl. Qed.
Lemma D_9ffc8 : decode_any W_9ffc8 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffcc : bv 32 := 0x01850513.
Lemma F_9ffcc : fetch_word Asan.M.loaded_segments (0xa001c : word) = Some W_9ffcc.
Proof. vm_refl. Qed.
Lemma D_9ffcc : decode_any W_9ffcc = Some (OpImm ALU_ADD 10 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffd0 : bv 32 := 0x0325252f.
Lemma F_9ffd0 : fetch_word Asan.M.loaded_segments (0xa0020 : word) = Some W_9ffd0.
Proof. vm_refl. Qed.
Lemma D_9ffd0 : decode_any W_9ffd0 = Some (Amo AMO_ADD AW false true 10 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffd4 : bv 32 := 0x001005b7.
Lemma F_9ffd4 : fetch_word Asan.M.loaded_segments (0xa0024 : word) = Some W_9ffd4.
Proof. vm_refl. Qed.
Lemma D_9ffd4 : decode_any W_9ffd4 = Some (Lui 11 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffd8 : bv 32 := 0x02051513.
Lemma F_9ffd8 : fetch_word Asan.M.loaded_segments (0xa0028 : word) = Some W_9ffd8.
Proof. vm_refl. Qed.
Lemma D_9ffd8 : decode_any W_9ffd8 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffdc : bv 32 := 0x02055513.
Lemma F_9ffdc : fetch_word Asan.M.loaded_segments (0xa002c : word) = Some W_9ffdc.
Proof. vm_refl. Qed.
Lemma D_9ffdc : decode_any W_9ffdc = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffe0 : bv 32 := 0x00a90533.
Lemma F_9ffe0 : fetch_word Asan.M.loaded_segments (0xa0030 : word) = Some W_9ffe0.
Proof. vm_refl. Qed.
Lemma D_9ffe0 : decode_any W_9ffe0 = Some (Op ALU_ADD 10 18 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffe4 : bv 32 := 0x00043603.
Lemma F_9ffe4 : fetch_word Asan.M.loaded_segments (0xa0034 : word) = Some W_9ffe4.
Proof. vm_refl. Qed.
Lemma D_9ffe4 : decode_any W_9ffe4 = Some (Load SZ8 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffe8 : bv 32 := 0x00b54533.
Lemma F_9ffe8 : fetch_word Asan.M.loaded_segments (0xa0038 : word) = Some W_9ffe8.
Proof. vm_refl. Qed.
Lemma D_9ffe8 : decode_any W_9ffe8 = Some (Op ALU_XOR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffec : bv 32 := 0x00012583.
Lemma F_9ffec : fetch_word Asan.M.loaded_segments (0xa003c : word) = Some W_9ffec.
Proof. vm_refl. Qed.
Lemma D_9ffec : decode_any W_9ffec = Some (Load SZ4 true 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9fff0 : bv 32 := 0x00153513.
Lemma F_9fff0 : fetch_word Asan.M.loaded_segments (0xa0040 : word) = Some W_9fff0.
Proof. vm_refl. Qed.
Lemma D_9fff0 : decode_any W_9fff0 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9fff4 : bv 32 := 0x00a60533.
Lemma F_9fff4 : fetch_word Asan.M.loaded_segments (0xa0044 : word) = Some W_9fff4.
Proof. vm_refl. Qed.
Lemma D_9fff4 : decode_any W_9fff4 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9fff8 : bv 32 := 0x00a43023.
Lemma F_9fff8 : fetch_word Asan.M.loaded_segments (0xa0048 : word) = Some W_9fff8.
Proof. vm_refl. Qed.
Lemma D_9fff8 : decode_any W_9fff8 = Some (Store SZ8 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9fffc : bv 32 := 0x0015851b.
Lemma F_9fffc : fetch_word Asan.M.loaded_segments (0xa004c : word) = Some W_9fffc.
Proof. vm_refl. Qed.
Lemma D_9fffc : decode_any W_9fffc = Some (OpImm32 10 11 1, 4%Z).
Proof. vm_refl. Qed.

