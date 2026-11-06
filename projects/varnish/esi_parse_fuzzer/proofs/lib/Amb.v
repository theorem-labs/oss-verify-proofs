(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.

Module DU_cink.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_25e88 : bv 32 := 0xff010113.
Lemma F_25e88 : fetch_word Ubsan.M.loaded_segments (0x25e88 : word) = Some W_25e88.
Proof. vm_refl. Qed.
Lemma D_25e88 : decode_any W_25e88 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e8c : bv 32 := 0x00113423.
Lemma F_25e8c : fetch_word Ubsan.M.loaded_segments (0x25e8c : word) = Some W_25e8c.
Proof. vm_refl. Qed.
Lemma D_25e8c : decode_any W_25e8c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e90 : bv 32 := 0x00813023.
Lemma F_25e90 : fetch_word Ubsan.M.loaded_segments (0x25e90 : word) = Some W_25e90.
Proof. vm_refl. Qed.
Lemma D_25e90 : decode_any W_25e90 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e94 : bv 32 := 0x198000ef.
Lemma F_25e94 : fetch_word Ubsan.M.loaded_segments (0x25e94 : word) = Some W_25e94.
Proof. vm_refl. Qed.
Lemma D_25e94 : decode_any W_25e94 = Some (Jal 1 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e98 : bv 32 := 0x00053403.
Lemma F_25e98 : fetch_word Ubsan.M.loaded_segments (0x25e98 : word) = Some W_25e98.
Proof. vm_refl. Qed.
Lemma D_25e98 : decode_any W_25e98 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e9c : bv 32 := 0x12041663.
Lemma F_25e9c : fetch_word Ubsan.M.loaded_segments (0x25e9c : word) = Some W_25e9c.
Proof. vm_refl. Qed.
Lemma D_25e9c : decode_any W_25e9c = Some (Branch BC_NE 8 0 300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25ea0 : bv 32 := 0x0003d517.
Lemma F_25ea0 : fetch_word Ubsan.M.loaded_segments (0x25ea0 : word) = Some W_25ea0.
Proof. vm_refl. Qed.
Lemma D_25ea0 : decode_any W_25ea0 = Some (Auipc 10 61, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25ea4 : bv 32 := 0xd3053403.
Lemma F_25ea4 : fetch_word Ubsan.M.loaded_segments (0x25ea4 : word) = Some W_25ea4.
Proof. vm_refl. Qed.
Lemma D_25ea4 : decode_any W_25ea4 = Some (Load SZ8 true 8 10 3376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25ea8 : bv 32 := 0x04040a63.
Lemma F_25ea8 : fetch_word Ubsan.M.loaded_segments (0x25ea8 : word) = Some W_25ea8.
Proof. vm_refl. Qed.
Lemma D_25ea8 : decode_any W_25ea8 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25efc : bv 32 := 0x0000c517.
Lemma F_25efc : fetch_word Ubsan.M.loaded_segments (0x25efc : word) = Some W_25efc.
Proof. vm_refl. Qed.
Lemma D_25efc : decode_any W_25efc = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25f00 : bv 32 := 0xc2453403.
Lemma F_25f00 : fetch_word Ubsan.M.loaded_segments (0x25f00 : word) = Some W_25f00.
Proof. vm_refl. Qed.
Lemma D_25f00 : decode_any W_25f00 = Some (Load SZ8 true 8 10 3108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25f04 : bv 32 := 0x04040a63.
Lemma F_25f04 : fetch_word Ubsan.M.loaded_segments (0x25f04 : word) = Some W_25f04.
Proof. vm_refl. Qed.
Lemma D_25f04 : decode_any W_25f04 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25f08 : bv 32 := 0x08c42503.
Lemma F_25f08 : fetch_word Ubsan.M.loaded_segments (0x25f08 : word) = Some W_25f08.
Proof. vm_refl. Qed.
Lemma D_25f08 : decode_any W_25f08 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25f0c : bv 32 := 0x00054663.
Lemma F_25f0c : fetch_word Ubsan.M.loaded_segments (0x25f0c : word) = Some W_25f0c.
Proof. vm_refl. Qed.
Lemma D_25f0c : decode_any W_25f0c = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25f18 : bv 32 := 0x02843503.
Lemma F_25f18 : fetch_word Ubsan.M.loaded_segments (0x25f18 : word) = Some W_25f18.
Proof. vm_refl. Qed.
Lemma D_25f18 : decode_any W_25f18 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25f1c : bv 32 := 0x03843583.
Lemma F_25f1c : fetch_word Ubsan.M.loaded_segments (0x25f1c : word) = Some W_25f1c.
Proof. vm_refl. Qed.
Lemma D_25f1c : decode_any W_25f1c = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25f20 : bv 32 := 0x00b50c63.
Lemma F_25f20 : fetch_word Ubsan.M.loaded_segments (0x25f20 : word) = Some W_25f20.
Proof. vm_refl. Qed.
Lemma D_25f20 : decode_any W_25f20 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25f24 : bv 32 := 0x04843683.
Lemma F_25f24 : fetch_word Ubsan.M.loaded_segments (0x25f24 : word) = Some W_25f24.
Proof. vm_refl. Qed.
Lemma D_25f24 : decode_any W_25f24 = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25f28 : bv 32 := 0x00040513.
Lemma F_25f28 : fetch_word Ubsan.M.loaded_segments (0x25f28 : word) = Some W_25f28.
Proof. vm_refl. Qed.
Lemma D_25f28 : decode_any W_25f28 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25f2c : bv 32 := 0x00000593.
Lemma F_25f2c : fetch_word Ubsan.M.loaded_segments (0x25f2c : word) = Some W_25f2c.
Proof. vm_refl. Qed.
Lemma D_25f2c : decode_any W_25f2c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25f30 : bv 32 := 0x00000613.
Lemma F_25f30 : fetch_word Ubsan.M.loaded_segments (0x25f30 : word) = Some W_25f30.
Proof. vm_refl. Qed.
Lemma D_25f30 : decode_any W_25f30 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25f34 : bv 32 := 0x000680e7.
Lemma F_25f34 : fetch_word Ubsan.M.loaded_segments (0x25f34 : word) = Some W_25f34.
Proof. vm_refl. Qed.
Lemma D_25f34 : decode_any W_25f34 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25f38 : bv 32 := 0x00843503.
Lemma F_25f38 : fetch_word Ubsan.M.loaded_segments (0x25f38 : word) = Some W_25f38.
Proof. vm_refl. Qed.
Lemma D_25f38 : decode_any W_25f38 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25f3c : bv 32 := 0x01043583.
Lemma F_25f3c : fetch_word Ubsan.M.loaded_segments (0x25f3c : word) = Some W_25f3c.
Proof. vm_refl. Qed.
Lemma D_25f3c : decode_any W_25f3c = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25f40 : bv 32 := 0x00b50c63.
Lemma F_25f40 : fetch_word Ubsan.M.loaded_segments (0x25f40 : word) = Some W_25f40.
Proof. vm_refl. Qed.
Lemma D_25f40 : decode_any W_25f40 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25f58 : bv 32 := 0x0000c517.
Lemma F_25f58 : fetch_word Ubsan.M.loaded_segments (0x25f58 : word) = Some W_25f58.
Proof. vm_refl. Qed.
Lemma D_25f58 : decode_any W_25f58 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25f5c : bv 32 := 0xad853403.
Lemma F_25f5c : fetch_word Ubsan.M.loaded_segments (0x25f5c : word) = Some W_25f5c.
Proof. vm_refl. Qed.
Lemma D_25f5c : decode_any W_25f5c = Some (Load SZ8 true 8 10 2776, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25f60 : bv 32 := 0x0a040e63.
Lemma F_25f60 : fetch_word Ubsan.M.loaded_segments (0x25f60 : word) = Some W_25f60.
Proof. vm_refl. Qed.
Lemma D_25f60 : decode_any W_25f60 = Some (Branch BC_EQ 8 0 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25f64 : bv 32 := 0x08c42503.
Lemma F_25f64 : fetch_word Ubsan.M.loaded_segments (0x25f64 : word) = Some W_25f64.
Proof. vm_refl. Qed.
Lemma D_25f64 : decode_any W_25f64 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25f68 : bv 32 := 0x00054663.
Lemma F_25f68 : fetch_word Ubsan.M.loaded_segments (0x25f68 : word) = Some W_25f68.
Proof. vm_refl. Qed.
Lemma D_25f68 : decode_any W_25f68 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25f74 : bv 32 := 0x02843503.
Lemma F_25f74 : fetch_word Ubsan.M.loaded_segments (0x25f74 : word) = Some W_25f74.
Proof. vm_refl. Qed.
Lemma D_25f74 : decode_any W_25f74 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25f78 : bv 32 := 0x03843583.
Lemma F_25f78 : fetch_word Ubsan.M.loaded_segments (0x25f78 : word) = Some W_25f78.
Proof. vm_refl. Qed.
Lemma D_25f78 : decode_any W_25f78 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25f7c : bv 32 := 0x00b50c63.
Lemma F_25f7c : fetch_word Ubsan.M.loaded_segments (0x25f7c : word) = Some W_25f7c.
Proof. vm_refl. Qed.
Lemma D_25f7c : decode_any W_25f7c = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25f94 : bv 32 := 0x00843503.
Lemma F_25f94 : fetch_word Ubsan.M.loaded_segments (0x25f94 : word) = Some W_25f94.
Proof. vm_refl. Qed.
Lemma D_25f94 : decode_any W_25f94 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25f98 : bv 32 := 0x01043583.
Lemma F_25f98 : fetch_word Ubsan.M.loaded_segments (0x25f98 : word) = Some W_25f98.
Proof. vm_refl. Qed.
Lemma D_25f98 : decode_any W_25f98 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25f9c : bv 32 := 0x08b50063.
Lemma F_25f9c : fetch_word Ubsan.M.loaded_segments (0x25f9c : word) = Some W_25f9c.
Proof. vm_refl. Qed.
Lemma D_25f9c : decode_any W_25f9c = Some (Branch BC_EQ 10 11 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2601c : bv 32 := 0x00813083.
Lemma F_2601c : fetch_word Ubsan.M.loaded_segments (0x2601c : word) = Some W_2601c.
Proof. vm_refl. Qed.
Lemma D_2601c : decode_any W_2601c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26020 : bv 32 := 0x00013403.
Lemma F_26020 : fetch_word Ubsan.M.loaded_segments (0x26020 : word) = Some W_26020.
Proof. vm_refl. Qed.
Lemma D_26020 : decode_any W_26020 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26024 : bv 32 := 0x01010113.
Lemma F_26024 : fetch_word Ubsan.M.loaded_segments (0x26024 : word) = Some W_26024.
Proof. vm_refl. Qed.
Lemma D_26024 : decode_any W_26024 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26028 : bv 32 := 0x00008067.
Lemma F_26028 : fetch_word Ubsan.M.loaded_segments (0x26028 : word) = Some W_26028.
Proof. vm_refl. Qed.
Lemma D_26028 : decode_any W_26028 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2602c : bv 32 := 0xff010113.
Lemma F_2602c : fetch_word Ubsan.M.loaded_segments (0x2602c : word) = Some W_2602c.
Proof. vm_refl. Qed.
Lemma D_2602c : decode_any W_2602c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26030 : bv 32 := 0x00113423.
Lemma F_26030 : fetch_word Ubsan.M.loaded_segments (0x26030 : word) = Some W_26030.
Proof. vm_refl. Qed.
Lemma D_26030 : decode_any W_26030 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26034 : bv 32 := 0x00813023.
Lemma F_26034 : fetch_word Ubsan.M.loaded_segments (0x26034 : word) = Some W_26034.
Proof. vm_refl. Qed.
Lemma D_26034 : decode_any W_26034 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26038 : bv 32 := 0x0003d517.
Lemma F_26038 : fetch_word Ubsan.M.loaded_segments (0x26038 : word) = Some W_26038.
Proof. vm_refl. Qed.
Lemma D_26038 : decode_any W_26038 = Some (Auipc 10 61, 4%Z).
Proof. vm_refl. Qed.
End DU_cink.

Module DU_cmu8.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_2603c : bv 32 := 0xba050413.
Lemma F_2603c : fetch_word Ubsan.M.loaded_segments (0x2603c : word) = Some W_2603c.
Proof. vm_refl. Qed.
Lemma D_2603c : decode_any W_2603c = Some (OpImm ALU_ADD 8 10 2976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26040 : bv 32 := 0x00040513.
Lemma F_26040 : fetch_word Ubsan.M.loaded_segments (0x26040 : word) = Some W_26040.
Proof. vm_refl. Qed.
Lemma D_26040 : decode_any W_26040 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26044 : bv 32 := 0x7bc050ef.
Lemma F_26044 : fetch_word Ubsan.M.loaded_segments (0x26044 : word) = Some W_26044.
Proof. vm_refl. Qed.
Lemma D_26044 : decode_any W_26044 = Some (Jal 1 22460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26048 : bv 32 := 0x00840513.
Lemma F_26048 : fetch_word Ubsan.M.loaded_segments (0x26048 : word) = Some W_26048.
Proof. vm_refl. Qed.
Lemma D_26048 : decode_any W_26048 = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2604c : bv 32 := 0x00813083.
Lemma F_2604c : fetch_word Ubsan.M.loaded_segments (0x2604c : word) = Some W_2604c.
Proof. vm_refl. Qed.
Lemma D_2604c : decode_any W_2604c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26050 : bv 32 := 0x00013403.
Lemma F_26050 : fetch_word Ubsan.M.loaded_segments (0x26050 : word) = Some W_26050.
Proof. vm_refl. Qed.
Lemma D_26050 : decode_any W_26050 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26054 : bv 32 := 0x01010113.
Lemma F_26054 : fetch_word Ubsan.M.loaded_segments (0x26054 : word) = Some W_26054.
Proof. vm_refl. Qed.
Lemma D_26054 : decode_any W_26054 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26058 : bv 32 := 0x00008067.
Lemma F_26058 : fetch_word Ubsan.M.loaded_segments (0x26058 : word) = Some W_26058.
Proof. vm_refl. Qed.
Lemma D_26058 : decode_any W_26058 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_260f8 : bv 32 := 0xf9010113.
Lemma F_260f8 : fetch_word Ubsan.M.loaded_segments (0x260f8 : word) = Some W_260f8.
Proof. vm_refl. Qed.
Lemma D_260f8 : decode_any W_260f8 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_260fc : bv 32 := 0x06113423.
Lemma F_260fc : fetch_word Ubsan.M.loaded_segments (0x260fc : word) = Some W_260fc.
Proof. vm_refl. Qed.
Lemma D_260fc : decode_any W_260fc = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26100 : bv 32 := 0x06813023.
Lemma F_26100 : fetch_word Ubsan.M.loaded_segments (0x26100 : word) = Some W_26100.
Proof. vm_refl. Qed.
Lemma D_26100 : decode_any W_26100 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26104 : bv 32 := 0x04913c23.
Lemma F_26104 : fetch_word Ubsan.M.loaded_segments (0x26104 : word) = Some W_26104.
Proof. vm_refl. Qed.
Lemma D_26104 : decode_any W_26104 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26108 : bv 32 := 0x05213823.
Lemma F_26108 : fetch_word Ubsan.M.loaded_segments (0x26108 : word) = Some W_26108.
Proof. vm_refl. Qed.
Lemma D_26108 : decode_any W_26108 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2610c : bv 32 := 0x05313423.
Lemma F_2610c : fetch_word Ubsan.M.loaded_segments (0x2610c : word) = Some W_2610c.
Proof. vm_refl. Qed.
Lemma D_2610c : decode_any W_2610c = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26110 : bv 32 := 0x05413023.
Lemma F_26110 : fetch_word Ubsan.M.loaded_segments (0x26110 : word) = Some W_26110.
Proof. vm_refl. Qed.
Lemma D_26110 : decode_any W_26110 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26114 : bv 32 := 0x03513c23.
Lemma F_26114 : fetch_word Ubsan.M.loaded_segments (0x26114 : word) = Some W_26114.
Proof. vm_refl. Qed.
Lemma D_26114 : decode_any W_26114 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26118 : bv 32 := 0x03613823.
Lemma F_26118 : fetch_word Ubsan.M.loaded_segments (0x26118 : word) = Some W_26118.
Proof. vm_refl. Qed.
Lemma D_26118 : decode_any W_26118 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2611c : bv 32 := 0x00060413.
Lemma F_2611c : fetch_word Ubsan.M.loaded_segments (0x2611c : word) = Some W_2611c.
Proof. vm_refl. Qed.
Lemma D_2611c : decode_any W_2611c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26120 : bv 32 := 0x00050493.
Lemma F_26120 : fetch_word Ubsan.M.loaded_segments (0x26120 : word) = Some W_26120.
Proof. vm_refl. Qed.
Lemma D_26120 : decode_any W_26120 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26124 : bv 32 := 0x0000a517.
Lemma F_26124 : fetch_word Ubsan.M.loaded_segments (0x26124 : word) = Some W_26124.
Proof. vm_refl. Qed.
Lemma D_26124 : decode_any W_26124 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26128 : bv 32 := 0x6a453a83.
Lemma F_26128 : fetch_word Ubsan.M.loaded_segments (0x26128 : word) = Some W_26128.
Proof. vm_refl. Qed.
Lemma D_26128 : decode_any W_26128 = Some (Load SZ8 true 21 10 1700, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2612c : bv 32 := 0x000ab503.
Lemma F_2612c : fetch_word Ubsan.M.loaded_segments (0x2612c : word) = Some W_2612c.
Proof. vm_refl. Qed.
Lemma D_2612c : decode_any W_2612c = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26130 : bv 32 := 0x02a13423.
Lemma F_26130 : fetch_word Ubsan.M.loaded_segments (0x26130 : word) = Some W_26130.
Proof. vm_refl. Qed.
Lemma D_26130 : decode_any W_26130 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26134 : bv 32 := 0x0284b503.
Lemma F_26134 : fetch_word Ubsan.M.loaded_segments (0x26134 : word) = Some W_26134.
Proof. vm_refl. Qed.
Lemma D_26134 : decode_any W_26134 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26138 : bv 32 := 0x0384b603.
Lemma F_26138 : fetch_word Ubsan.M.loaded_segments (0x26138 : word) = Some W_26138.
Proof. vm_refl. Qed.
Lemma D_26138 : decode_any W_26138 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2613c : bv 32 := 0x40c50b33.
Lemma F_2613c : fetch_word Ubsan.M.loaded_segments (0x2613c : word) = Some W_2613c.
Proof. vm_refl. Qed.
Lemma D_2613c : decode_any W_2613c = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26140 : bv 32 := 0x00c546b3.
Lemma F_26140 : fetch_word Ubsan.M.loaded_segments (0x26140 : word) = Some W_26140.
Proof. vm_refl. Qed.
Lemma D_26140 : decode_any W_26140 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26144 : bv 32 := 0x00c13423.
Lemma F_26144 : fetch_word Ubsan.M.loaded_segments (0x26144 : word) = Some W_26144.
Proof. vm_refl. Qed.
Lemma D_26144 : decode_any W_26144 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26148 : bv 32 := 0x01613823.
Lemma F_26148 : fetch_word Ubsan.M.loaded_segments (0x26148 : word) = Some W_26148.
Proof. vm_refl. Qed.
Lemma D_26148 : decode_any W_26148 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2614c : bv 32 := 0x00b13c23.
Lemma F_2614c : fetch_word Ubsan.M.loaded_segments (0x2614c : word) = Some W_2614c.
Proof. vm_refl. Qed.
Lemma D_2614c : decode_any W_2614c = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26150 : bv 32 := 0x02813023.
Lemma F_26150 : fetch_word Ubsan.M.loaded_segments (0x26150 : word) = Some W_26150.
Proof. vm_refl. Qed.
Lemma D_26150 : decode_any W_26150 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26154 : bv 32 := 0x008b0b33.
Lemma F_26154 : fetch_word Ubsan.M.loaded_segments (0x26154 : word) = Some W_26154.
Proof. vm_refl. Qed.
Lemma D_26154 : decode_any W_26154 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26158 : bv 32 := 0x00d03933.
Lemma F_26158 : fetch_word Ubsan.M.loaded_segments (0x26158 : word) = Some W_26158.
Proof. vm_refl. Qed.
Lemma D_26158 : decode_any W_26158 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2615c : bv 32 := 0x00c50663.
Lemma F_2615c : fetch_word Ubsan.M.loaded_segments (0x2615c : word) = Some W_2615c.
Proof. vm_refl. Qed.
Lemma D_2615c : decode_any W_2615c = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26160 : bv 32 := 0x00810993.
Lemma F_26160 : fetch_word Ubsan.M.loaded_segments (0x26160 : word) = Some W_26160.
Proof. vm_refl. Qed.
Lemma D_26160 : decode_any W_26160 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26164 : bv 32 := 0x0080006f.
Lemma F_26164 : fetch_word Ubsan.M.loaded_segments (0x26164 : word) = Some W_26164.
Proof. vm_refl. Qed.
Lemma D_26164 : decode_any W_26164 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26168 : bv 32 := 0x01810993.
Lemma F_26168 : fetch_word Ubsan.M.loaded_segments (0x26168 : word) = Some W_26168.
Proof. vm_refl. Qed.
Lemma D_26168 : decode_any W_26168 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2616c : bv 32 := 0x0784a503.
Lemma F_2616c : fetch_word Ubsan.M.loaded_segments (0x2616c : word) = Some W_2616c.
Proof. vm_refl. Qed.
Lemma D_2616c : decode_any W_2616c = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26170 : bv 32 := 0x00190913.
Lemma F_26170 : fetch_word Ubsan.M.loaded_segments (0x26170 : word) = Some W_26170.
Proof. vm_refl. Qed.
Lemma D_26170 : decode_any W_26170 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26174 : bv 32 := 0x04200893.
Lemma F_26174 : fetch_word Ubsan.M.loaded_segments (0x26174 : word) = Some W_26174.
Proof. vm_refl. Qed.
Lemma D_26174 : decode_any W_26174 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26178 : bv 32 := 0x00098593.
Lemma F_26178 : fetch_word Ubsan.M.loaded_segments (0x26178 : word) = Some W_26178.
Proof. vm_refl. Qed.
Lemma D_26178 : decode_any W_26178 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2617c : bv 32 := 0x00090613.
Lemma F_2617c : fetch_word Ubsan.M.loaded_segments (0x2617c : word) = Some W_2617c.
Proof. vm_refl. Qed.
Lemma D_2617c : decode_any W_2617c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26180 : bv 32 := 0x00000073.
Lemma F_26180 : fetch_word Ubsan.M.loaded_segments (0x26180 : word) = Some W_26180.
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma E_26180 : is_ecall W_26180 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26184 : bv 32 := 0xd79fc0ef.
Lemma F_26184 : fetch_word Ubsan.M.loaded_segments (0x26184 : word) = Some W_26184.
Proof. vm_refl. Qed.
Lemma D_26184 : decode_any W_26184 = Some (Jal 1 2084216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26188 : bv 32 := 0x09651863.
Lemma F_26188 : fetch_word Ubsan.M.loaded_segments (0x26188 : word) = Some W_26188.
Proof. vm_refl. Qed.
Lemma D_26188 : decode_any W_26188 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2618c : bv 32 := 0x0584b503.
Lemma F_2618c : fetch_word Ubsan.M.loaded_segments (0x2618c : word) = Some W_2618c.
Proof. vm_refl. Qed.
Lemma D_2618c : decode_any W_2618c = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26190 : bv 32 := 0x0604b583.
Lemma F_26190 : fetch_word Ubsan.M.loaded_segments (0x26190 : word) = Some W_26190.
Proof. vm_refl. Qed.
Lemma D_26190 : decode_any W_26190 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26194 : bv 32 := 0x00b505b3.
Lemma F_26194 : fetch_word Ubsan.M.loaded_segments (0x26194 : word) = Some W_26194.
Proof. vm_refl. Qed.
Lemma D_26194 : decode_any W_26194 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26198 : bv 32 := 0x02b4b023.
Lemma F_26198 : fetch_word Ubsan.M.loaded_segments (0x26198 : word) = Some W_26198.
Proof. vm_refl. Qed.
Lemma D_26198 : decode_any W_26198 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2619c : bv 32 := 0x02a4b423.
Lemma F_2619c : fetch_word Ubsan.M.loaded_segments (0x2619c : word) = Some W_2619c.
Proof. vm_refl. Qed.
Lemma D_2619c : decode_any W_2619c = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_261a0 : bv 32 := 0x02a4bc23.
Lemma F_261a0 : fetch_word Ubsan.M.loaded_segments (0x261a0 : word) = Some W_261a0.
Proof. vm_refl. Qed.
Lemma D_261a0 : decode_any W_261a0 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_261a4 : bv 32 := 0x00040513.
Lemma F_261a4 : fetch_word Ubsan.M.loaded_segments (0x261a4 : word) = Some W_261a4.
Proof. vm_refl. Qed.
Lemma D_261a4 : decode_any W_261a4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_261a8 : bv 32 := 0x000ab583.
Lemma F_261a8 : fetch_word Ubsan.M.loaded_segments (0x261a8 : word) = Some W_261a8.
Proof. vm_refl. Qed.
Lemma D_261a8 : decode_any W_261a8 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_261ac : bv 32 := 0x02813603.
Lemma F_261ac : fetch_word Ubsan.M.loaded_segments (0x261ac : word) = Some W_261ac.
Proof. vm_refl. Qed.
Lemma D_261ac : decode_any W_261ac = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_261b0 : bv 32 := 0x0cc59a63.
Lemma F_261b0 : fetch_word Ubsan.M.loaded_segments (0x261b0 : word) = Some W_261b0.
Proof. vm_refl. Qed.
Lemma D_261b0 : decode_any W_261b0 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_261b4 : bv 32 := 0x06813083.
Lemma F_261b4 : fetch_word Ubsan.M.loaded_segments (0x261b4 : word) = Some W_261b4.
Proof. vm_refl. Qed.
Lemma D_261b4 : decode_any W_261b4 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_261b8 : bv 32 := 0x06013403.
Lemma F_261b8 : fetch_word Ubsan.M.loaded_segments (0x261b8 : word) = Some W_261b8.
Proof. vm_refl. Qed.
Lemma D_261b8 : decode_any W_261b8 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_261bc : bv 32 := 0x05813483.
Lemma F_261bc : fetch_word Ubsan.M.loaded_segments (0x261bc : word) = Some W_261bc.
Proof. vm_refl. Qed.
Lemma D_261bc : decode_any W_261bc = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_261c0 : bv 32 := 0x05013903.
Lemma F_261c0 : fetch_word Ubsan.M.loaded_segments (0x261c0 : word) = Some W_261c0.
Proof. vm_refl. Qed.
Lemma D_261c0 : decode_any W_261c0 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_261c4 : bv 32 := 0x04813983.
Lemma F_261c4 : fetch_word Ubsan.M.loaded_segments (0x261c4 : word) = Some W_261c4.
Proof. vm_refl. Qed.
Lemma D_261c4 : decode_any W_261c4 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_261c8 : bv 32 := 0x04013a03.
Lemma F_261c8 : fetch_word Ubsan.M.loaded_segments (0x261c8 : word) = Some W_261c8.
Proof. vm_refl. Qed.
Lemma D_261c8 : decode_any W_261c8 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_261cc : bv 32 := 0x03813a83.
Lemma F_261cc : fetch_word Ubsan.M.loaded_segments (0x261cc : word) = Some W_261cc.
Proof. vm_refl. Qed.
Lemma D_261cc : decode_any W_261cc = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_261d0 : bv 32 := 0x03013b03.
Lemma F_261d0 : fetch_word Ubsan.M.loaded_segments (0x261d0 : word) = Some W_261d0.
Proof. vm_refl. Qed.
Lemma D_261d0 : decode_any W_261d0 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_261d4 : bv 32 := 0x07010113.
Lemma F_261d4 : fetch_word Ubsan.M.loaded_segments (0x261d4 : word) = Some W_261d4.
Proof. vm_refl. Qed.
Lemma D_261d4 : decode_any W_261d4 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_261d8 : bv 32 := 0x00008067.
Lemma F_261d8 : fetch_word Ubsan.M.loaded_segments (0x261d8 : word) = Some W_261d8.
Proof. vm_refl. Qed.
Lemma D_261d8 : decode_any W_261d8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_261dc : bv 32 := 0x00800713.
Lemma F_261dc : fetch_word Ubsan.M.loaded_segments (0x261dc : word) = Some W_261dc.
Proof. vm_refl. Qed.
Lemma D_261dc : decode_any W_261dc = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_261e0 : bv 32 := 0x000a0593.
Lemma F_261e0 : fetch_word Ubsan.M.loaded_segments (0x261e0 : word) = Some W_261e0.
Proof. vm_refl. Qed.
Lemma D_261e0 : decode_any W_261e0 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_261e4 : bv 32 := 0x00e98733.
Lemma F_261e4 : fetch_word Ubsan.M.loaded_segments (0x261e4 : word) = Some W_261e4.
Proof. vm_refl. Qed.
Lemma D_261e4 : decode_any W_261e4 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_261e8 : bv 32 := 0x00073783.
Lemma F_261e8 : fetch_word Ubsan.M.loaded_segments (0x261e8 : word) = Some W_261e8.
Proof. vm_refl. Qed.
Lemma D_261e8 : decode_any W_261e8 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_261ec : bv 32 := 0x40ab0b33.
Lemma F_261ec : fetch_word Ubsan.M.loaded_segments (0x261ec : word) = Some W_261ec.
Proof. vm_refl. Qed.
Lemma D_261ec : decode_any W_261ec = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_261f0 : bv 32 := 0x0784a503.
Lemma F_261f0 : fetch_word Ubsan.M.loaded_segments (0x261f0 : word) = Some W_261f0.
Proof. vm_refl. Qed.
Lemma D_261f0 : decode_any W_261f0 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_261f4 : bv 32 := 0x40c9093b.
Lemma F_261f4 : fetch_word Ubsan.M.loaded_segments (0x261f4 : word) = Some W_261f4.
Proof. vm_refl. Qed.
Lemma D_261f4 : decode_any W_261f4 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_261f8 : bv 32 := 0x40d787b3.
Lemma F_261f8 : fetch_word Ubsan.M.loaded_segments (0x261f8 : word) = Some W_261f8.
Proof. vm_refl. Qed.
Lemma D_261f8 : decode_any W_261f8 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_261fc : bv 32 := 0x00f73023.
Lemma F_261fc : fetch_word Ubsan.M.loaded_segments (0x261fc : word) = Some W_261fc.
Proof. vm_refl. Qed.
Lemma D_261fc : decode_any W_261fc = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26200 : bv 32 := 0x04200893.
Lemma F_26200 : fetch_word Ubsan.M.loaded_segments (0x26200 : word) = Some W_26200.
Proof. vm_refl. Qed.
Lemma D_26200 : decode_any W_26200 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26204 : bv 32 := 0x00090613.
Lemma F_26204 : fetch_word Ubsan.M.loaded_segments (0x26204 : word) = Some W_26204.
Proof. vm_refl. Qed.
Lemma D_26204 : decode_any W_26204 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26208 : bv 32 := 0x00000073.
Lemma F_26208 : fetch_word Ubsan.M.loaded_segments (0x26208 : word) = Some W_26208.
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma E_26208 : is_ecall W_26208 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_2620c : bv 32 := 0xcf1fc0ef.
Lemma F_2620c : fetch_word Ubsan.M.loaded_segments (0x2620c : word) = Some W_2620c.
Proof. vm_refl. Qed.
Lemma D_2620c : decode_any W_2620c = Some (Jal 1 2084080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26210 : bv 32 := 0x000a0993.
Lemma F_26210 : fetch_word Ubsan.M.loaded_segments (0x26210 : word) = Some W_26210.
Proof. vm_refl. Qed.
Lemma D_26210 : decode_any W_26210 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26214 : bv 32 := 0xf7650ce3.
Lemma F_26214 : fetch_word Ubsan.M.loaded_segments (0x26214 : word) = Some W_26214.
Proof. vm_refl. Qed.
Lemma D_26214 : decode_any W_26214 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26218 : bv 32 := 0x02054c63.
Lemma F_26218 : fetch_word Ubsan.M.loaded_segments (0x26218 : word) = Some W_26218.
Proof. vm_refl. Qed.
Lemma D_26218 : decode_any W_26218 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2621c : bv 32 := 0x0089b583.
Lemma F_2621c : fetch_word Ubsan.M.loaded_segments (0x2621c : word) = Some W_2621c.
Proof. vm_refl. Qed.
Lemma D_2621c : decode_any W_2621c = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26220 : bv 32 := 0x00a5b633.
Lemma F_26220 : fetch_word Ubsan.M.loaded_segments (0x26220 : word) = Some W_26220.
Proof. vm_refl. Qed.
Lemma D_26220 : decode_any W_26220 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26224 : bv 32 := 0x00461a13.
Lemma F_26224 : fetch_word Ubsan.M.loaded_segments (0x26224 : word) = Some W_26224.
Proof. vm_refl. Qed.
Lemma D_26224 : decode_any W_26224 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26228 : bv 32 := 0x01498a33.
Lemma F_26228 : fetch_word Ubsan.M.loaded_segments (0x26228 : word) = Some W_26228.
Proof. vm_refl. Qed.
Lemma D_26228 : decode_any W_26228 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2622c : bv 32 := 0x000a3703.
Lemma F_2622c : fetch_word Ubsan.M.loaded_segments (0x2622c : word) = Some W_2622c.
Proof. vm_refl. Qed.
Lemma D_2622c : decode_any W_2622c = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26230 : bv 32 := 0x40c006b3.
Lemma F_26230 : fetch_word Ubsan.M.loaded_segments (0x26230 : word) = Some W_26230.
Proof. vm_refl. Qed.
Lemma D_26230 : decode_any W_26230 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26234 : bv 32 := 0x00b6f6b3.
Lemma F_26234 : fetch_word Ubsan.M.loaded_segments (0x26234 : word) = Some W_26234.
Proof. vm_refl. Qed.
Lemma D_26234 : decode_any W_26234 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26238 : bv 32 := 0x40d506b3.
Lemma F_26238 : fetch_word Ubsan.M.loaded_segments (0x26238 : word) = Some W_26238.
Proof. vm_refl. Qed.
Lemma D_26238 : decode_any W_26238 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2623c : bv 32 := 0x00d70733.
Lemma F_2623c : fetch_word Ubsan.M.loaded_segments (0x2623c : word) = Some W_2623c.
Proof. vm_refl. Qed.
Lemma D_2623c : decode_any W_2623c = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26240 : bv 32 := 0x00ea3023.
Lemma F_26240 : fetch_word Ubsan.M.loaded_segments (0x26240 : word) = Some W_26240.
Proof. vm_refl. Qed.
Lemma D_26240 : decode_any W_26240 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26244 : bv 32 := 0xf8a5fce3.
Lemma F_26244 : fetch_word Ubsan.M.loaded_segments (0x26244 : word) = Some W_26244.
Proof. vm_refl. Qed.
Lemma D_26244 : decode_any W_26244 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26248 : bv 32 := 0x01800713.
Lemma F_26248 : fetch_word Ubsan.M.loaded_segments (0x26248 : word) = Some W_26248.
Proof. vm_refl. Qed.
Lemma D_26248 : decode_any W_26248 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2624c : bv 32 := 0xf95ff06f.
Lemma F_2624c : fetch_word Ubsan.M.loaded_segments (0x2624c : word) = Some W_2624c.
Proof. vm_refl. Qed.
Lemma D_2624c : decode_any W_2624c = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.
End DU_cmu8.

Module D_co2af.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_25ae8 : bv 32 := 0xff010113.
Lemma F_25ae8 : fetch_word Plain.M.loaded_segments (0x25ae8 : word) = Some W_25ae8.
Proof. vm_refl. Qed.
Lemma D_25ae8 : decode_any W_25ae8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25aec : bv 32 := 0x00113423.
Lemma F_25aec : fetch_word Plain.M.loaded_segments (0x25aec : word) = Some W_25aec.
Proof. vm_refl. Qed.
Lemma D_25aec : decode_any W_25aec = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25af0 : bv 32 := 0x00813023.
Lemma F_25af0 : fetch_word Plain.M.loaded_segments (0x25af0 : word) = Some W_25af0.
Proof. vm_refl. Qed.
Lemma D_25af0 : decode_any W_25af0 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25af4 : bv 32 := 0x198000ef.
Lemma F_25af4 : fetch_word Plain.M.loaded_segments (0x25af4 : word) = Some W_25af4.
Proof. vm_refl. Qed.
Lemma D_25af4 : decode_any W_25af4 = Some (Jal 1 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25af8 : bv 32 := 0x00053403.
Lemma F_25af8 : fetch_word Plain.M.loaded_segments (0x25af8 : word) = Some W_25af8.
Proof. vm_refl. Qed.
Lemma D_25af8 : decode_any W_25af8 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25afc : bv 32 := 0x12041663.
Lemma F_25afc : fetch_word Plain.M.loaded_segments (0x25afc : word) = Some W_25afc.
Proof. vm_refl. Qed.
Lemma D_25afc : decode_any W_25afc = Some (Branch BC_NE 8 0 300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25b00 : bv 32 := 0x0003d517.
Lemma F_25b00 : fetch_word Plain.M.loaded_segments (0x25b00 : word) = Some W_25b00.
Proof. vm_refl. Qed.
Lemma D_25b00 : decode_any W_25b00 = Some (Auipc 10 61, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25b04 : bv 32 := 0xd3053403.
Lemma F_25b04 : fetch_word Plain.M.loaded_segments (0x25b04 : word) = Some W_25b04.
Proof. vm_refl. Qed.
Lemma D_25b04 : decode_any W_25b04 = Some (Load SZ8 true 8 10 3376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25b08 : bv 32 := 0x04040a63.
Lemma F_25b08 : fetch_word Plain.M.loaded_segments (0x25b08 : word) = Some W_25b08.
Proof. vm_refl. Qed.
Lemma D_25b08 : decode_any W_25b08 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25b5c : bv 32 := 0x0000c517.
Lemma F_25b5c : fetch_word Plain.M.loaded_segments (0x25b5c : word) = Some W_25b5c.
Proof. vm_refl. Qed.
Lemma D_25b5c : decode_any W_25b5c = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25b60 : bv 32 := 0xc2453403.
Lemma F_25b60 : fetch_word Plain.M.loaded_segments (0x25b60 : word) = Some W_25b60.
Proof. vm_refl. Qed.
Lemma D_25b60 : decode_any W_25b60 = Some (Load SZ8 true 8 10 3108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25b64 : bv 32 := 0x04040a63.
Lemma F_25b64 : fetch_word Plain.M.loaded_segments (0x25b64 : word) = Some W_25b64.
Proof. vm_refl. Qed.
Lemma D_25b64 : decode_any W_25b64 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25b68 : bv 32 := 0x08c42503.
Lemma F_25b68 : fetch_word Plain.M.loaded_segments (0x25b68 : word) = Some W_25b68.
Proof. vm_refl. Qed.
Lemma D_25b68 : decode_any W_25b68 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25b6c : bv 32 := 0x00054663.
Lemma F_25b6c : fetch_word Plain.M.loaded_segments (0x25b6c : word) = Some W_25b6c.
Proof. vm_refl. Qed.
Lemma D_25b6c : decode_any W_25b6c = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25b78 : bv 32 := 0x02843503.
Lemma F_25b78 : fetch_word Plain.M.loaded_segments (0x25b78 : word) = Some W_25b78.
Proof. vm_refl. Qed.
Lemma D_25b78 : decode_any W_25b78 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25b7c : bv 32 := 0x03843583.
Lemma F_25b7c : fetch_word Plain.M.loaded_segments (0x25b7c : word) = Some W_25b7c.
Proof. vm_refl. Qed.
Lemma D_25b7c : decode_any W_25b7c = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25b80 : bv 32 := 0x00b50c63.
Lemma F_25b80 : fetch_word Plain.M.loaded_segments (0x25b80 : word) = Some W_25b80.
Proof. vm_refl. Qed.
Lemma D_25b80 : decode_any W_25b80 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25b84 : bv 32 := 0x04843683.
Lemma F_25b84 : fetch_word Plain.M.loaded_segments (0x25b84 : word) = Some W_25b84.
Proof. vm_refl. Qed.
Lemma D_25b84 : decode_any W_25b84 = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25b88 : bv 32 := 0x00040513.
Lemma F_25b88 : fetch_word Plain.M.loaded_segments (0x25b88 : word) = Some W_25b88.
Proof. vm_refl. Qed.
Lemma D_25b88 : decode_any W_25b88 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25b8c : bv 32 := 0x00000593.
Lemma F_25b8c : fetch_word Plain.M.loaded_segments (0x25b8c : word) = Some W_25b8c.
Proof. vm_refl. Qed.
Lemma D_25b8c : decode_any W_25b8c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25b90 : bv 32 := 0x00000613.
Lemma F_25b90 : fetch_word Plain.M.loaded_segments (0x25b90 : word) = Some W_25b90.
Proof. vm_refl. Qed.
Lemma D_25b90 : decode_any W_25b90 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25b94 : bv 32 := 0x000680e7.
Lemma F_25b94 : fetch_word Plain.M.loaded_segments (0x25b94 : word) = Some W_25b94.
Proof. vm_refl. Qed.
Lemma D_25b94 : decode_any W_25b94 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25b98 : bv 32 := 0x00843503.
Lemma F_25b98 : fetch_word Plain.M.loaded_segments (0x25b98 : word) = Some W_25b98.
Proof. vm_refl. Qed.
Lemma D_25b98 : decode_any W_25b98 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25b9c : bv 32 := 0x01043583.
Lemma F_25b9c : fetch_word Plain.M.loaded_segments (0x25b9c : word) = Some W_25b9c.
Proof. vm_refl. Qed.
Lemma D_25b9c : decode_any W_25b9c = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25ba0 : bv 32 := 0x00b50c63.
Lemma F_25ba0 : fetch_word Plain.M.loaded_segments (0x25ba0 : word) = Some W_25ba0.
Proof. vm_refl. Qed.
Lemma D_25ba0 : decode_any W_25ba0 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25bb8 : bv 32 := 0x0000c517.
Lemma F_25bb8 : fetch_word Plain.M.loaded_segments (0x25bb8 : word) = Some W_25bb8.
Proof. vm_refl. Qed.
Lemma D_25bb8 : decode_any W_25bb8 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25bbc : bv 32 := 0xad853403.
Lemma F_25bbc : fetch_word Plain.M.loaded_segments (0x25bbc : word) = Some W_25bbc.
Proof. vm_refl. Qed.
Lemma D_25bbc : decode_any W_25bbc = Some (Load SZ8 true 8 10 2776, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25bc0 : bv 32 := 0x0a040e63.
Lemma F_25bc0 : fetch_word Plain.M.loaded_segments (0x25bc0 : word) = Some W_25bc0.
Proof. vm_refl. Qed.
Lemma D_25bc0 : decode_any W_25bc0 = Some (Branch BC_EQ 8 0 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25bc4 : bv 32 := 0x08c42503.
Lemma F_25bc4 : fetch_word Plain.M.loaded_segments (0x25bc4 : word) = Some W_25bc4.
Proof. vm_refl. Qed.
Lemma D_25bc4 : decode_any W_25bc4 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25bc8 : bv 32 := 0x00054663.
Lemma F_25bc8 : fetch_word Plain.M.loaded_segments (0x25bc8 : word) = Some W_25bc8.
Proof. vm_refl. Qed.
Lemma D_25bc8 : decode_any W_25bc8 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25bd4 : bv 32 := 0x02843503.
Lemma F_25bd4 : fetch_word Plain.M.loaded_segments (0x25bd4 : word) = Some W_25bd4.
Proof. vm_refl. Qed.
Lemma D_25bd4 : decode_any W_25bd4 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25bd8 : bv 32 := 0x03843583.
Lemma F_25bd8 : fetch_word Plain.M.loaded_segments (0x25bd8 : word) = Some W_25bd8.
Proof. vm_refl. Qed.
Lemma D_25bd8 : decode_any W_25bd8 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25bdc : bv 32 := 0x00b50c63.
Lemma F_25bdc : fetch_word Plain.M.loaded_segments (0x25bdc : word) = Some W_25bdc.
Proof. vm_refl. Qed.
Lemma D_25bdc : decode_any W_25bdc = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25bf4 : bv 32 := 0x00843503.
Lemma F_25bf4 : fetch_word Plain.M.loaded_segments (0x25bf4 : word) = Some W_25bf4.
Proof. vm_refl. Qed.
Lemma D_25bf4 : decode_any W_25bf4 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25bf8 : bv 32 := 0x01043583.
Lemma F_25bf8 : fetch_word Plain.M.loaded_segments (0x25bf8 : word) = Some W_25bf8.
Proof. vm_refl. Qed.
Lemma D_25bf8 : decode_any W_25bf8 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25bfc : bv 32 := 0x08b50063.
Lemma F_25bfc : fetch_word Plain.M.loaded_segments (0x25bfc : word) = Some W_25bfc.
Proof. vm_refl. Qed.
Lemma D_25bfc : decode_any W_25bfc = Some (Branch BC_EQ 10 11 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25c7c : bv 32 := 0x00813083.
Lemma F_25c7c : fetch_word Plain.M.loaded_segments (0x25c7c : word) = Some W_25c7c.
Proof. vm_refl. Qed.
Lemma D_25c7c : decode_any W_25c7c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25c80 : bv 32 := 0x00013403.
Lemma F_25c80 : fetch_word Plain.M.loaded_segments (0x25c80 : word) = Some W_25c80.
Proof. vm_refl. Qed.
Lemma D_25c80 : decode_any W_25c80 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25c84 : bv 32 := 0x01010113.
Lemma F_25c84 : fetch_word Plain.M.loaded_segments (0x25c84 : word) = Some W_25c84.
Proof. vm_refl. Qed.
Lemma D_25c84 : decode_any W_25c84 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25c88 : bv 32 := 0x00008067.
Lemma F_25c88 : fetch_word Plain.M.loaded_segments (0x25c88 : word) = Some W_25c88.
Proof. vm_refl. Qed.
Lemma D_25c88 : decode_any W_25c88 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25c8c : bv 32 := 0xff010113.
Lemma F_25c8c : fetch_word Plain.M.loaded_segments (0x25c8c : word) = Some W_25c8c.
Proof. vm_refl. Qed.
Lemma D_25c8c : decode_any W_25c8c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25c90 : bv 32 := 0x00113423.
Lemma F_25c90 : fetch_word Plain.M.loaded_segments (0x25c90 : word) = Some W_25c90.
Proof. vm_refl. Qed.
Lemma D_25c90 : decode_any W_25c90 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25c94 : bv 32 := 0x00813023.
Lemma F_25c94 : fetch_word Plain.M.loaded_segments (0x25c94 : word) = Some W_25c94.
Proof. vm_refl. Qed.
Lemma D_25c94 : decode_any W_25c94 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25c98 : bv 32 := 0x0003d517.
Lemma F_25c98 : fetch_word Plain.M.loaded_segments (0x25c98 : word) = Some W_25c98.
Proof. vm_refl. Qed.
Lemma D_25c98 : decode_any W_25c98 = Some (Auipc 10 61, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25c9c : bv 32 := 0xba050413.
Lemma F_25c9c : fetch_word Plain.M.loaded_segments (0x25c9c : word) = Some W_25c9c.
Proof. vm_refl. Qed.
Lemma D_25c9c : decode_any W_25c9c = Some (OpImm ALU_ADD 8 10 2976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25ca0 : bv 32 := 0x00040513.
Lemma F_25ca0 : fetch_word Plain.M.loaded_segments (0x25ca0 : word) = Some W_25ca0.
Proof. vm_refl. Qed.
Lemma D_25ca0 : decode_any W_25ca0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25ca4 : bv 32 := 0x7bc050ef.
Lemma F_25ca4 : fetch_word Plain.M.loaded_segments (0x25ca4 : word) = Some W_25ca4.
Proof. vm_refl. Qed.
Lemma D_25ca4 : decode_any W_25ca4 = Some (Jal 1 22460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25ca8 : bv 32 := 0x00840513.
Lemma F_25ca8 : fetch_word Plain.M.loaded_segments (0x25ca8 : word) = Some W_25ca8.
Proof. vm_refl. Qed.
Lemma D_25ca8 : decode_any W_25ca8 = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25cac : bv 32 := 0x00813083.
Lemma F_25cac : fetch_word Plain.M.loaded_segments (0x25cac : word) = Some W_25cac.
Proof. vm_refl. Qed.
Lemma D_25cac : decode_any W_25cac = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25cb0 : bv 32 := 0x00013403.
Lemma F_25cb0 : fetch_word Plain.M.loaded_segments (0x25cb0 : word) = Some W_25cb0.
Proof. vm_refl. Qed.
Lemma D_25cb0 : decode_any W_25cb0 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25cb4 : bv 32 := 0x01010113.
Lemma F_25cb4 : fetch_word Plain.M.loaded_segments (0x25cb4 : word) = Some W_25cb4.
Proof. vm_refl. Qed.
Lemma D_25cb4 : decode_any W_25cb4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25cb8 : bv 32 := 0x00008067.
Lemma F_25cb8 : fetch_word Plain.M.loaded_segments (0x25cb8 : word) = Some W_25cb8.
Proof. vm_refl. Qed.
Lemma D_25cb8 : decode_any W_25cb8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25d58 : bv 32 := 0xf9010113.
Lemma F_25d58 : fetch_word Plain.M.loaded_segments (0x25d58 : word) = Some W_25d58.
Proof. vm_refl. Qed.
Lemma D_25d58 : decode_any W_25d58 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25d5c : bv 32 := 0x06113423.
Lemma F_25d5c : fetch_word Plain.M.loaded_segments (0x25d5c : word) = Some W_25d5c.
Proof. vm_refl. Qed.
Lemma D_25d5c : decode_any W_25d5c = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25d60 : bv 32 := 0x06813023.
Lemma F_25d60 : fetch_word Plain.M.loaded_segments (0x25d60 : word) = Some W_25d60.
Proof. vm_refl. Qed.
Lemma D_25d60 : decode_any W_25d60 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25d64 : bv 32 := 0x04913c23.
Lemma F_25d64 : fetch_word Plain.M.loaded_segments (0x25d64 : word) = Some W_25d64.
Proof. vm_refl. Qed.
Lemma D_25d64 : decode_any W_25d64 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25d68 : bv 32 := 0x05213823.
Lemma F_25d68 : fetch_word Plain.M.loaded_segments (0x25d68 : word) = Some W_25d68.
Proof. vm_refl. Qed.
Lemma D_25d68 : decode_any W_25d68 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25d6c : bv 32 := 0x05313423.
Lemma F_25d6c : fetch_word Plain.M.loaded_segments (0x25d6c : word) = Some W_25d6c.
Proof. vm_refl. Qed.
Lemma D_25d6c : decode_any W_25d6c = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25d70 : bv 32 := 0x05413023.
Lemma F_25d70 : fetch_word Plain.M.loaded_segments (0x25d70 : word) = Some W_25d70.
Proof. vm_refl. Qed.
Lemma D_25d70 : decode_any W_25d70 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25d74 : bv 32 := 0x03513c23.
Lemma F_25d74 : fetch_word Plain.M.loaded_segments (0x25d74 : word) = Some W_25d74.
Proof. vm_refl. Qed.
Lemma D_25d74 : decode_any W_25d74 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25d78 : bv 32 := 0x03613823.
Lemma F_25d78 : fetch_word Plain.M.loaded_segments (0x25d78 : word) = Some W_25d78.
Proof. vm_refl. Qed.
Lemma D_25d78 : decode_any W_25d78 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25d7c : bv 32 := 0x00060413.
Lemma F_25d7c : fetch_word Plain.M.loaded_segments (0x25d7c : word) = Some W_25d7c.
Proof. vm_refl. Qed.
Lemma D_25d7c : decode_any W_25d7c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25d80 : bv 32 := 0x00050493.
Lemma F_25d80 : fetch_word Plain.M.loaded_segments (0x25d80 : word) = Some W_25d80.
Proof. vm_refl. Qed.
Lemma D_25d80 : decode_any W_25d80 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25d84 : bv 32 := 0x0000a517.
Lemma F_25d84 : fetch_word Plain.M.loaded_segments (0x25d84 : word) = Some W_25d84.
Proof. vm_refl. Qed.
Lemma D_25d84 : decode_any W_25d84 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25d88 : bv 32 := 0x6a453a83.
Lemma F_25d88 : fetch_word Plain.M.loaded_segments (0x25d88 : word) = Some W_25d88.
Proof. vm_refl. Qed.
Lemma D_25d88 : decode_any W_25d88 = Some (Load SZ8 true 21 10 1700, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25d8c : bv 32 := 0x000ab503.
Lemma F_25d8c : fetch_word Plain.M.loaded_segments (0x25d8c : word) = Some W_25d8c.
Proof. vm_refl. Qed.
Lemma D_25d8c : decode_any W_25d8c = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25d90 : bv 32 := 0x02a13423.
Lemma F_25d90 : fetch_word Plain.M.loaded_segments (0x25d90 : word) = Some W_25d90.
Proof. vm_refl. Qed.
Lemma D_25d90 : decode_any W_25d90 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25d94 : bv 32 := 0x0284b503.
Lemma F_25d94 : fetch_word Plain.M.loaded_segments (0x25d94 : word) = Some W_25d94.
Proof. vm_refl. Qed.
Lemma D_25d94 : decode_any W_25d94 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25d98 : bv 32 := 0x0384b603.
Lemma F_25d98 : fetch_word Plain.M.loaded_segments (0x25d98 : word) = Some W_25d98.
Proof. vm_refl. Qed.
Lemma D_25d98 : decode_any W_25d98 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25d9c : bv 32 := 0x40c50b33.
Lemma F_25d9c : fetch_word Plain.M.loaded_segments (0x25d9c : word) = Some W_25d9c.
Proof. vm_refl. Qed.
Lemma D_25d9c : decode_any W_25d9c = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25da0 : bv 32 := 0x00c546b3.
Lemma F_25da0 : fetch_word Plain.M.loaded_segments (0x25da0 : word) = Some W_25da0.
Proof. vm_refl. Qed.
Lemma D_25da0 : decode_any W_25da0 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25da4 : bv 32 := 0x00c13423.
Lemma F_25da4 : fetch_word Plain.M.loaded_segments (0x25da4 : word) = Some W_25da4.
Proof. vm_refl. Qed.
Lemma D_25da4 : decode_any W_25da4 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25da8 : bv 32 := 0x01613823.
Lemma F_25da8 : fetch_word Plain.M.loaded_segments (0x25da8 : word) = Some W_25da8.
Proof. vm_refl. Qed.
Lemma D_25da8 : decode_any W_25da8 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25dac : bv 32 := 0x00b13c23.
Lemma F_25dac : fetch_word Plain.M.loaded_segments (0x25dac : word) = Some W_25dac.
Proof. vm_refl. Qed.
Lemma D_25dac : decode_any W_25dac = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25db0 : bv 32 := 0x02813023.
Lemma F_25db0 : fetch_word Plain.M.loaded_segments (0x25db0 : word) = Some W_25db0.
Proof. vm_refl. Qed.
Lemma D_25db0 : decode_any W_25db0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25db4 : bv 32 := 0x008b0b33.
Lemma F_25db4 : fetch_word Plain.M.loaded_segments (0x25db4 : word) = Some W_25db4.
Proof. vm_refl. Qed.
Lemma D_25db4 : decode_any W_25db4 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25db8 : bv 32 := 0x00d03933.
Lemma F_25db8 : fetch_word Plain.M.loaded_segments (0x25db8 : word) = Some W_25db8.
Proof. vm_refl. Qed.
Lemma D_25db8 : decode_any W_25db8 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25dbc : bv 32 := 0x00c50663.
Lemma F_25dbc : fetch_word Plain.M.loaded_segments (0x25dbc : word) = Some W_25dbc.
Proof. vm_refl. Qed.
Lemma D_25dbc : decode_any W_25dbc = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25dc0 : bv 32 := 0x00810993.
Lemma F_25dc0 : fetch_word Plain.M.loaded_segments (0x25dc0 : word) = Some W_25dc0.
Proof. vm_refl. Qed.
Lemma D_25dc0 : decode_any W_25dc0 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25dc4 : bv 32 := 0x0080006f.
Lemma F_25dc4 : fetch_word Plain.M.loaded_segments (0x25dc4 : word) = Some W_25dc4.
Proof. vm_refl. Qed.
Lemma D_25dc4 : decode_any W_25dc4 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25dc8 : bv 32 := 0x01810993.
Lemma F_25dc8 : fetch_word Plain.M.loaded_segments (0x25dc8 : word) = Some W_25dc8.
Proof. vm_refl. Qed.
Lemma D_25dc8 : decode_any W_25dc8 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25dcc : bv 32 := 0x0784a503.
Lemma F_25dcc : fetch_word Plain.M.loaded_segments (0x25dcc : word) = Some W_25dcc.
Proof. vm_refl. Qed.
Lemma D_25dcc : decode_any W_25dcc = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25dd0 : bv 32 := 0x00190913.
Lemma F_25dd0 : fetch_word Plain.M.loaded_segments (0x25dd0 : word) = Some W_25dd0.
Proof. vm_refl. Qed.
Lemma D_25dd0 : decode_any W_25dd0 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25dd4 : bv 32 := 0x04200893.
Lemma F_25dd4 : fetch_word Plain.M.loaded_segments (0x25dd4 : word) = Some W_25dd4.
Proof. vm_refl. Qed.
Lemma D_25dd4 : decode_any W_25dd4 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25dd8 : bv 32 := 0x00098593.
Lemma F_25dd8 : fetch_word Plain.M.loaded_segments (0x25dd8 : word) = Some W_25dd8.
Proof. vm_refl. Qed.
Lemma D_25dd8 : decode_any W_25dd8 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25ddc : bv 32 := 0x00090613.
Lemma F_25ddc : fetch_word Plain.M.loaded_segments (0x25ddc : word) = Some W_25ddc.
Proof. vm_refl. Qed.
Lemma D_25ddc : decode_any W_25ddc = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25de0 : bv 32 := 0x00000073.
Lemma F_25de0 : fetch_word Plain.M.loaded_segments (0x25de0 : word) = Some W_25de0.
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma E_25de0 : is_ecall W_25de0 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_25de4 : bv 32 := 0xd79fc0ef.
Lemma F_25de4 : fetch_word Plain.M.loaded_segments (0x25de4 : word) = Some W_25de4.
Proof. vm_refl. Qed.
Lemma D_25de4 : decode_any W_25de4 = Some (Jal 1 2084216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25de8 : bv 32 := 0x09651863.
Lemma F_25de8 : fetch_word Plain.M.loaded_segments (0x25de8 : word) = Some W_25de8.
Proof. vm_refl. Qed.
Lemma D_25de8 : decode_any W_25de8 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25dec : bv 32 := 0x0584b503.
Lemma F_25dec : fetch_word Plain.M.loaded_segments (0x25dec : word) = Some W_25dec.
Proof. vm_refl. Qed.
Lemma D_25dec : decode_any W_25dec = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25df0 : bv 32 := 0x0604b583.
Lemma F_25df0 : fetch_word Plain.M.loaded_segments (0x25df0 : word) = Some W_25df0.
Proof. vm_refl. Qed.
Lemma D_25df0 : decode_any W_25df0 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25df4 : bv 32 := 0x00b505b3.
Lemma F_25df4 : fetch_word Plain.M.loaded_segments (0x25df4 : word) = Some W_25df4.
Proof. vm_refl. Qed.
Lemma D_25df4 : decode_any W_25df4 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25df8 : bv 32 := 0x02b4b023.
Lemma F_25df8 : fetch_word Plain.M.loaded_segments (0x25df8 : word) = Some W_25df8.
Proof. vm_refl. Qed.
Lemma D_25df8 : decode_any W_25df8 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25dfc : bv 32 := 0x02a4b423.
Lemma F_25dfc : fetch_word Plain.M.loaded_segments (0x25dfc : word) = Some W_25dfc.
Proof. vm_refl. Qed.
Lemma D_25dfc : decode_any W_25dfc = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e00 : bv 32 := 0x02a4bc23.
Lemma F_25e00 : fetch_word Plain.M.loaded_segments (0x25e00 : word) = Some W_25e00.
Proof. vm_refl. Qed.
Lemma D_25e00 : decode_any W_25e00 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e04 : bv 32 := 0x00040513.
Lemma F_25e04 : fetch_word Plain.M.loaded_segments (0x25e04 : word) = Some W_25e04.
Proof. vm_refl. Qed.
Lemma D_25e04 : decode_any W_25e04 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e08 : bv 32 := 0x000ab583.
Lemma F_25e08 : fetch_word Plain.M.loaded_segments (0x25e08 : word) = Some W_25e08.
Proof. vm_refl. Qed.
Lemma D_25e08 : decode_any W_25e08 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e0c : bv 32 := 0x02813603.
Lemma F_25e0c : fetch_word Plain.M.loaded_segments (0x25e0c : word) = Some W_25e0c.
Proof. vm_refl. Qed.
Lemma D_25e0c : decode_any W_25e0c = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e10 : bv 32 := 0x0cc59a63.
Lemma F_25e10 : fetch_word Plain.M.loaded_segments (0x25e10 : word) = Some W_25e10.
Proof. vm_refl. Qed.
Lemma D_25e10 : decode_any W_25e10 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e14 : bv 32 := 0x06813083.
Lemma F_25e14 : fetch_word Plain.M.loaded_segments (0x25e14 : word) = Some W_25e14.
Proof. vm_refl. Qed.
Lemma D_25e14 : decode_any W_25e14 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e18 : bv 32 := 0x06013403.
Lemma F_25e18 : fetch_word Plain.M.loaded_segments (0x25e18 : word) = Some W_25e18.
Proof. vm_refl. Qed.
Lemma D_25e18 : decode_any W_25e18 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e1c : bv 32 := 0x05813483.
Lemma F_25e1c : fetch_word Plain.M.loaded_segments (0x25e1c : word) = Some W_25e1c.
Proof. vm_refl. Qed.
Lemma D_25e1c : decode_any W_25e1c = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e20 : bv 32 := 0x05013903.
Lemma F_25e20 : fetch_word Plain.M.loaded_segments (0x25e20 : word) = Some W_25e20.
Proof. vm_refl. Qed.
Lemma D_25e20 : decode_any W_25e20 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e24 : bv 32 := 0x04813983.
Lemma F_25e24 : fetch_word Plain.M.loaded_segments (0x25e24 : word) = Some W_25e24.
Proof. vm_refl. Qed.
Lemma D_25e24 : decode_any W_25e24 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e28 : bv 32 := 0x04013a03.
Lemma F_25e28 : fetch_word Plain.M.loaded_segments (0x25e28 : word) = Some W_25e28.
Proof. vm_refl. Qed.
Lemma D_25e28 : decode_any W_25e28 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e2c : bv 32 := 0x03813a83.
Lemma F_25e2c : fetch_word Plain.M.loaded_segments (0x25e2c : word) = Some W_25e2c.
Proof. vm_refl. Qed.
Lemma D_25e2c : decode_any W_25e2c = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e30 : bv 32 := 0x03013b03.
Lemma F_25e30 : fetch_word Plain.M.loaded_segments (0x25e30 : word) = Some W_25e30.
Proof. vm_refl. Qed.
Lemma D_25e30 : decode_any W_25e30 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e34 : bv 32 := 0x07010113.
Lemma F_25e34 : fetch_word Plain.M.loaded_segments (0x25e34 : word) = Some W_25e34.
Proof. vm_refl. Qed.
Lemma D_25e34 : decode_any W_25e34 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e38 : bv 32 := 0x00008067.
Lemma F_25e38 : fetch_word Plain.M.loaded_segments (0x25e38 : word) = Some W_25e38.
Proof. vm_refl. Qed.
Lemma D_25e38 : decode_any W_25e38 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e3c : bv 32 := 0x00800713.
Lemma F_25e3c : fetch_word Plain.M.loaded_segments (0x25e3c : word) = Some W_25e3c.
Proof. vm_refl. Qed.
Lemma D_25e3c : decode_any W_25e3c = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e40 : bv 32 := 0x000a0593.
Lemma F_25e40 : fetch_word Plain.M.loaded_segments (0x25e40 : word) = Some W_25e40.
Proof. vm_refl. Qed.
Lemma D_25e40 : decode_any W_25e40 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e44 : bv 32 := 0x00e98733.
Lemma F_25e44 : fetch_word Plain.M.loaded_segments (0x25e44 : word) = Some W_25e44.
Proof. vm_refl. Qed.
Lemma D_25e44 : decode_any W_25e44 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e48 : bv 32 := 0x00073783.
Lemma F_25e48 : fetch_word Plain.M.loaded_segments (0x25e48 : word) = Some W_25e48.
Proof. vm_refl. Qed.
Lemma D_25e48 : decode_any W_25e48 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e4c : bv 32 := 0x40ab0b33.
Lemma F_25e4c : fetch_word Plain.M.loaded_segments (0x25e4c : word) = Some W_25e4c.
Proof. vm_refl. Qed.
Lemma D_25e4c : decode_any W_25e4c = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e50 : bv 32 := 0x0784a503.
Lemma F_25e50 : fetch_word Plain.M.loaded_segments (0x25e50 : word) = Some W_25e50.
Proof. vm_refl. Qed.
Lemma D_25e50 : decode_any W_25e50 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e54 : bv 32 := 0x40c9093b.
Lemma F_25e54 : fetch_word Plain.M.loaded_segments (0x25e54 : word) = Some W_25e54.
Proof. vm_refl. Qed.
Lemma D_25e54 : decode_any W_25e54 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e58 : bv 32 := 0x40d787b3.
Lemma F_25e58 : fetch_word Plain.M.loaded_segments (0x25e58 : word) = Some W_25e58.
Proof. vm_refl. Qed.
Lemma D_25e58 : decode_any W_25e58 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e5c : bv 32 := 0x00f73023.
Lemma F_25e5c : fetch_word Plain.M.loaded_segments (0x25e5c : word) = Some W_25e5c.
Proof. vm_refl. Qed.
Lemma D_25e5c : decode_any W_25e5c = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e60 : bv 32 := 0x04200893.
Lemma F_25e60 : fetch_word Plain.M.loaded_segments (0x25e60 : word) = Some W_25e60.
Proof. vm_refl. Qed.
Lemma D_25e60 : decode_any W_25e60 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e64 : bv 32 := 0x00090613.
Lemma F_25e64 : fetch_word Plain.M.loaded_segments (0x25e64 : word) = Some W_25e64.
Proof. vm_refl. Qed.
Lemma D_25e64 : decode_any W_25e64 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e68 : bv 32 := 0x00000073.
Lemma F_25e68 : fetch_word Plain.M.loaded_segments (0x25e68 : word) = Some W_25e68.
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma E_25e68 : is_ecall W_25e68 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_25e6c : bv 32 := 0xcf1fc0ef.
Lemma F_25e6c : fetch_word Plain.M.loaded_segments (0x25e6c : word) = Some W_25e6c.
Proof. vm_refl. Qed.
Lemma D_25e6c : decode_any W_25e6c = Some (Jal 1 2084080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e70 : bv 32 := 0x000a0993.
Lemma F_25e70 : fetch_word Plain.M.loaded_segments (0x25e70 : word) = Some W_25e70.
Proof. vm_refl. Qed.
Lemma D_25e70 : decode_any W_25e70 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e74 : bv 32 := 0xf7650ce3.
Lemma F_25e74 : fetch_word Plain.M.loaded_segments (0x25e74 : word) = Some W_25e74.
Proof. vm_refl. Qed.
Lemma D_25e74 : decode_any W_25e74 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e78 : bv 32 := 0x02054c63.
Lemma F_25e78 : fetch_word Plain.M.loaded_segments (0x25e78 : word) = Some W_25e78.
Proof. vm_refl. Qed.
Lemma D_25e78 : decode_any W_25e78 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e7c : bv 32 := 0x0089b583.
Lemma F_25e7c : fetch_word Plain.M.loaded_segments (0x25e7c : word) = Some W_25e7c.
Proof. vm_refl. Qed.
Lemma D_25e7c : decode_any W_25e7c = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e80 : bv 32 := 0x00a5b633.
Lemma F_25e80 : fetch_word Plain.M.loaded_segments (0x25e80 : word) = Some W_25e80.
Proof. vm_refl. Qed.
Lemma D_25e80 : decode_any W_25e80 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e84 : bv 32 := 0x00461a13.
Lemma F_25e84 : fetch_word Plain.M.loaded_segments (0x25e84 : word) = Some W_25e84.
Proof. vm_refl. Qed.
Lemma D_25e84 : decode_any W_25e84 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e88 : bv 32 := 0x01498a33.
Lemma F_25e88 : fetch_word Plain.M.loaded_segments (0x25e88 : word) = Some W_25e88.
Proof. vm_refl. Qed.
Lemma D_25e88 : decode_any W_25e88 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e8c : bv 32 := 0x000a3703.
Lemma F_25e8c : fetch_word Plain.M.loaded_segments (0x25e8c : word) = Some W_25e8c.
Proof. vm_refl. Qed.
Lemma D_25e8c : decode_any W_25e8c = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e90 : bv 32 := 0x40c006b3.
Lemma F_25e90 : fetch_word Plain.M.loaded_segments (0x25e90 : word) = Some W_25e90.
Proof. vm_refl. Qed.
Lemma D_25e90 : decode_any W_25e90 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e94 : bv 32 := 0x00b6f6b3.
Lemma F_25e94 : fetch_word Plain.M.loaded_segments (0x25e94 : word) = Some W_25e94.
Proof. vm_refl. Qed.
Lemma D_25e94 : decode_any W_25e94 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e98 : bv 32 := 0x40d506b3.
Lemma F_25e98 : fetch_word Plain.M.loaded_segments (0x25e98 : word) = Some W_25e98.
Proof. vm_refl. Qed.
Lemma D_25e98 : decode_any W_25e98 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25e9c : bv 32 := 0x00d70733.
Lemma F_25e9c : fetch_word Plain.M.loaded_segments (0x25e9c : word) = Some W_25e9c.
Proof. vm_refl. Qed.
Lemma D_25e9c : decode_any W_25e9c = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25ea0 : bv 32 := 0x00ea3023.
Lemma F_25ea0 : fetch_word Plain.M.loaded_segments (0x25ea0 : word) = Some W_25ea0.
Proof. vm_refl. Qed.
Lemma D_25ea0 : decode_any W_25ea0 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25ea4 : bv 32 := 0xf8a5fce3.
Lemma F_25ea4 : fetch_word Plain.M.loaded_segments (0x25ea4 : word) = Some W_25ea4.
Proof. vm_refl. Qed.
Lemma D_25ea4 : decode_any W_25ea4 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25ea8 : bv 32 := 0x01800713.
Lemma F_25ea8 : fetch_word Plain.M.loaded_segments (0x25ea8 : word) = Some W_25ea8.
Proof. vm_refl. Qed.
Lemma D_25ea8 : decode_any W_25ea8 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25eac : bv 32 := 0xf95ff06f.
Lemma F_25eac : fetch_word Plain.M.loaded_segments (0x25eac : word) = Some W_25eac.
Proof. vm_refl. Qed.
Lemma D_25eac : decode_any W_25eac = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.
End D_co2af.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
Class Amb : Type := mkAmb {
  a_uid : word;
  a_gid : word;
  a_groups : list word;
  a_net : NetQueue;
  a_nofile : word;
  a_sigmask : word;
  a_hwcap : word;
  a_va : VaSize;   (* [comment removed for export] *)
  a_urandom : InputStream   (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition amb_creds {AMB : Amb} : Creds :=
  mkCreds a_uid a_uid a_uid a_gid a_gid a_gid a_groups.

(* [comment removed for export] *)
Definition mkModelC {AMB : Amb} (fds : list (word * FdEntry)) (vm : VmMaps)
    (stdin : InputStream) (fs : Fs.Fs) (halted : option word)
    (tid : option word) (rlim : option (list byte)) : Model :=
  mkModelOf (mkFdState fds []) (mkVmState vm [] [])
            (mkIoState stdin a_urandom a_net (Z_to_bv 64 0)) (mkFsState fs)
            (mkProcState halted tid amb_creds false a_sigmask
                         false None false false false false [])
            (mkLimState rlim a_nofile)
            (mkTimeState (Z_to_bv 64 0)).

(* [comment removed for export] *)
Definition mkProcInputC {AMB : Amb} (argv envp : list (list byte)) (fs : Fs.Fs)
    (stdin : InputStream) : ProcInput :=
  mkProcInput_full argv envp fs stdin a_uid a_gid a_groups a_net a_nofile a_sigmask a_hwcap false a_va
                   a_urandom [].

(* [comment removed for export] *)
Definition amb_of (inp : ProcInput) : Amb :=
  mkAmb (in_uid inp) (in_gid inp) (in_groups inp) (in_net inp)
        (in_nofile inp) (in_sigmask inp) (in_hwcap inp) (in_va_size inp) (in_urandom inp).

(* [comment removed for export] *)
Lemma init_model_C_of : forall reserved brk0 mbase sp lim inp,
  in_abort_terminal inp = false ->
  init_model reserved brk0 mbase sp lim
    (@mkProcInputC (amb_of inp) (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp))
  = init_model reserved brk0 mbase sp lim inp.
Proof. intros r b mb sp lim [av ev fs si u g gs n nf sm hw ab va ur tm] H. cbn in H. subst ab. reflexivity. Qed.

Lemma init_config_C_of : forall segs pc ph sp brk mbase rdraw lim inp,
  in_abort_terminal inp = false ->
  init_config segs pc ph sp brk mbase rdraw lim
    (@mkProcInputC (amb_of inp) (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp))
  = init_config segs pc ph sp brk mbase rdraw lim inp.
Proof. intros segs pc ph sp brk mbase rdraw lim [av ev fs si u g gs n nf sm hw ab va ur tm] H. cbn in H. subst ab. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Section Proj.
  Context {AMB : Amb}.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
End Proj.
