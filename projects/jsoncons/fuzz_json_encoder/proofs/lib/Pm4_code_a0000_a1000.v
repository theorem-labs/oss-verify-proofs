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
Definition W_a0000 : bv 32 := 0x03813083.
Lemma F_a0000 : fetch_word Asan.M.loaded_segments (0xa0050 : word) = Some W_a0000.
Proof. vm_refl. Qed.
Lemma D_a0000 : decode_any W_a0000 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0004 : bv 32 := 0x03013403.
Lemma F_a0004 : fetch_word Asan.M.loaded_segments (0xa0054 : word) = Some W_a0004.
Proof. vm_refl. Qed.
Lemma D_a0004 : decode_any W_a0004 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0008 : bv 32 := 0x02813483.
Lemma F_a0008 : fetch_word Asan.M.loaded_segments (0xa0058 : word) = Some W_a0008.
Proof. vm_refl. Qed.
Lemma D_a0008 : decode_any W_a0008 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a000c : bv 32 := 0x02013903.
Lemma F_a000c : fetch_word Asan.M.loaded_segments (0xa005c : word) = Some W_a000c.
Proof. vm_refl. Qed.
Lemma D_a000c : decode_any W_a000c = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0010 : bv 32 := 0x01813983.
Lemma F_a0010 : fetch_word Asan.M.loaded_segments (0xa0060 : word) = Some W_a0010.
Proof. vm_refl. Qed.
Lemma D_a0010 : decode_any W_a0010 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0014 : bv 32 := 0x01013a03.
Lemma F_a0014 : fetch_word Asan.M.loaded_segments (0xa0064 : word) = Some W_a0014.
Proof. vm_refl. Qed.
Lemma D_a0014 : decode_any W_a0014 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0018 : bv 32 := 0x00813a83.
Lemma F_a0018 : fetch_word Asan.M.loaded_segments (0xa0068 : word) = Some W_a0018.
Proof. vm_refl. Qed.
Lemma D_a0018 : decode_any W_a0018 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a001c : bv 32 := 0x04010113.
Lemma F_a001c : fetch_word Asan.M.loaded_segments (0xa006c : word) = Some W_a001c.
Proof. vm_refl. Qed.
Lemma D_a001c : decode_any W_a001c = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0020 : bv 32 := 0x00008067.
Lemma F_a0020 : fetch_word Asan.M.loaded_segments (0xa0070 : word) = Some W_a0020.
Proof. vm_refl. Qed.
Lemma D_a0020 : decode_any W_a0020 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0048 : bv 32 := 0xff010113.
Lemma F_a0048 : fetch_word Asan.M.loaded_segments (0xa0098 : word) = Some W_a0048.
Proof. vm_refl. Qed.
Lemma D_a0048 : decode_any W_a0048 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a004c : bv 32 := 0x00113423.
Lemma F_a004c : fetch_word Asan.M.loaded_segments (0xa009c : word) = Some W_a004c.
Proof. vm_refl. Qed.
Lemma D_a004c : decode_any W_a004c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0050 : bv 32 := 0x00813023.
Lemma F_a0050 : fetch_word Asan.M.loaded_segments (0xa00a0 : word) = Some W_a0050.
Proof. vm_refl. Qed.
Lemma D_a0050 : decode_any W_a0050 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0054 : bv 32 := 0x00058793.
Lemma F_a0054 : fetch_word Asan.M.loaded_segments (0xa00a4 : word) = Some W_a0054.
Proof. vm_refl. Qed.
Lemma D_a0054 : decode_any W_a0054 = Some (OpImm ALU_ADD 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0058 : bv 32 := 0x00050593.
Lemma F_a0058 : fetch_word Asan.M.loaded_segments (0xa00a8 : word) = Some W_a0058.
Proof. vm_refl. Qed.
Lemma D_a0058 : decode_any W_a0058 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a005c : bv 32 := 0x00f5342f.
Lemma F_a005c : fetch_word Asan.M.loaded_segments (0xa00ac : word) = Some W_a005c.
Proof. vm_refl. Qed.
Lemma D_a005c : decode_any W_a005c = Some (Amo AMO_ADD AD false false 8 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0060 : bv 32 := 0xfff78513.
Lemma F_a0060 : fetch_word Asan.M.loaded_segments (0xa00b0 : word) = Some W_a0060.
Proof. vm_refl. Qed.
Lemma D_a0060 : decode_any W_a0060 = Some (OpImm ALU_ADD 10 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0064 : bv 32 := 0x01445293.
Lemma F_a0064 : fetch_word Asan.M.loaded_segments (0xa00b4 : word) = Some W_a0064.
Proof. vm_refl. Qed.
Lemma D_a0064 : decode_any W_a0064 = Some (ShiftImm ALU_SRL 5 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0068 : bv 32 := 0x00850733.
Lemma F_a0068 : fetch_word Asan.M.loaded_segments (0xa00b8 : word) = Some W_a0068.
Proof. vm_refl. Qed.
Lemma D_a0068 : decode_any W_a0068 = Some (Op ALU_ADD 14 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a006c : bv 32 := 0x01475313.
Lemma F_a006c : fetch_word Asan.M.loaded_segments (0xa00bc : word) = Some W_a006c.
Proof. vm_refl. Qed.
Lemma D_a006c : decode_any W_a006c = Some (ShiftImm ALU_SRL 6 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0070 : bv 32 := 0x04629863.
Lemma F_a0070 : fetch_word Asan.M.loaded_segments (0xa00c0 : word) = Some W_a0070.
Proof. vm_refl. Qed.
Lemma D_a0070 : decode_any W_a0070 = Some (Branch BC_NE 5 6 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0074 : bv 32 := 0x02045513.
Lemma F_a0074 : fetch_word Asan.M.loaded_segments (0xa00c4 : word) = Some W_a0074.
Proof. vm_refl. Qed.
Lemma D_a0074 : decode_any W_a0074 = Some (ShiftImm ALU_SRL 10 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0078 : bv 32 := 0x00050c63.
Lemma F_a0078 : fetch_word Asan.M.loaded_segments (0xa00c8 : word) = Some W_a0078.
Proof. vm_refl. Qed.
Lemma D_a0078 : decode_any W_a0078 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0090 : bv 32 := 0x00863023.
Lemma F_a0090 : fetch_word Asan.M.loaded_segments (0xa00e0 : word) = Some W_a0090.
Proof. vm_refl. Qed.
Lemma D_a0090 : decode_any W_a0090 = Some (Store SZ8 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0094 : bv 32 := 0x00429613.
Lemma F_a0094 : fetch_word Asan.M.loaded_segments (0xa00e4 : word) = Some W_a0094.
Proof. vm_refl. Qed.
Lemma D_a0094 : decode_any W_a0094 = Some (ShiftImm ALU_SLL 12 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0098 : bv 32 := 0x00c58633.
Lemma F_a0098 : fetch_word Asan.M.loaded_segments (0xa00e8 : word) = Some W_a0098.
Proof. vm_refl. Qed.
Lemma D_a0098 : decode_any W_a0098 = Some (Op ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a009c : bv 32 := 0x01063503.
Lemma F_a009c : fetch_word Asan.M.loaded_segments (0xa00ec : word) = Some W_a009c.
Proof. vm_refl. Qed.
Lemma D_a009c : decode_any W_a009c = Some (Load SZ8 true 10 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a00a0 : bv 32 := 0x0a050a63.
Lemma F_a00a0 : fetch_word Asan.M.loaded_segments (0xa00f0 : word) = Some W_a00a0.
Proof. vm_refl. Qed.
Lemma D_a00a0 : decode_any W_a00a0 = Some (Branch BC_EQ 10 0 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a00a4 : bv 32 := 0x02c41413.
Lemma F_a00a4 : fetch_word Asan.M.loaded_segments (0xa00f4 : word) = Some W_a00a4.
Proof. vm_refl. Qed.
Lemma D_a00a4 : decode_any W_a00a4 = Some (ShiftImm ALU_SLL 8 8 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a00a8 : bv 32 := 0x02945413.
Lemma F_a00a8 : fetch_word Asan.M.loaded_segments (0xa00f8 : word) = Some W_a00a8.
Proof. vm_refl. Qed.
Lemma D_a00a8 : decode_any W_a00a8 = Some (ShiftImm ALU_SRL 8 8 41, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a00ac : bv 32 := 0x00850533.
Lemma F_a00ac : fetch_word Asan.M.loaded_segments (0xa00fc : word) = Some W_a00ac.
Proof. vm_refl. Qed.
Lemma D_a00ac : decode_any W_a00ac = Some (Op ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a00b0 : bv 32 := 0x00813083.
Lemma F_a00b0 : fetch_word Asan.M.loaded_segments (0xa0100 : word) = Some W_a00b0.
Proof. vm_refl. Qed.
Lemma D_a00b0 : decode_any W_a00b0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a00b4 : bv 32 := 0x00013403.
Lemma F_a00b4 : fetch_word Asan.M.loaded_segments (0xa0104 : word) = Some W_a00b4.
Proof. vm_refl. Qed.
Lemma D_a00b4 : decode_any W_a00b4 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a00b8 : bv 32 := 0x01010113.
Lemma F_a00b8 : fetch_word Asan.M.loaded_segments (0xa0108 : word) = Some W_a00b8.
Proof. vm_refl. Qed.
Lemma D_a00b8 : decode_any W_a00b8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a00bc : bv 32 := 0x00008067.
Lemma F_a00bc : fetch_word Asan.M.loaded_segments (0xa010c : word) = Some W_a00bc.
Proof. vm_refl. Qed.
Lemma D_a00bc : decode_any W_a00bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

