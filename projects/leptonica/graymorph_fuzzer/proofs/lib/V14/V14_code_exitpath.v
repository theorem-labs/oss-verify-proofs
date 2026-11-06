(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.H Require GcFlushU14.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_14dfc : bv 32 := 0xffffe517.
Lemma F_14dfc : fetch_word Ubsan.M.loaded_segments (0x14dfc : word) = Some W_14dfc.
Proof. vm_refl. Qed.
Lemma D_14dfc : decode_any W_14dfc = Some (Auipc 10 1048574, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e00 : bv 32 := 0x9fc50513.
Lemma F_14e00 : fetch_word Ubsan.M.loaded_segments (0x14e00 : word) = Some W_14e00.
Proof. vm_refl. Qed.
Lemma D_14e00 : decode_any W_14e00 = Some (OpImm ALU_ADD 10 10 2556, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e04 : bv 32 := 0x0001f597.
Lemma F_14e04 : fetch_word Ubsan.M.loaded_segments (0x14e04 : word) = Some W_14e04.
Proof. vm_refl. Qed.
Lemma D_14e04 : decode_any W_14e04 = Some (Auipc 11 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e08 : bv 32 := 0x1f458593.
Lemma F_14e08 : fetch_word Ubsan.M.loaded_segments (0x14e08 : word) = Some W_14e08.
Proof. vm_refl. Qed.
Lemma D_14e08 : decode_any W_14e08 = Some (OpImm ALU_ADD 11 11 500, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e0c : bv 32 := 0x000000ef.
Lemma F_14e0c : fetch_word Ubsan.M.loaded_segments (0x14e0c : word) = Some W_14e0c.
Proof. vm_refl. Qed.
Lemma D_14e0c : decode_any W_14e0c = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e10 : bv 32 := 0x0040006f.
Lemma F_14e10 : fetch_word Ubsan.M.loaded_segments (0x14e10 : word) = Some W_14e10.
Proof. vm_refl. Qed.
Lemma D_14e10 : decode_any W_14e10 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e14 : bv 32 := 0x00813083.
Lemma F_14e14 : fetch_word Ubsan.M.loaded_segments (0x14e14 : word) = Some W_14e14.
Proof. vm_refl. Qed.
Lemma D_14e14 : decode_any W_14e14 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e18 : bv 32 := 0x00013403.
Lemma F_14e18 : fetch_word Ubsan.M.loaded_segments (0x14e18 : word) = Some W_14e18.
Proof. vm_refl. Qed.
Lemma D_14e18 : decode_any W_14e18 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e1c : bv 32 := 0x01010113.
Lemma F_14e1c : fetch_word Ubsan.M.loaded_segments (0x14e1c : word) = Some W_14e1c.
Proof. vm_refl. Qed.
Lemma D_14e1c : decode_any W_14e1c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e20 : bv 32 := 0x00008067.
Lemma F_14e20 : fetch_word Ubsan.M.loaded_segments (0x14e20 : word) = Some W_14e20.
Proof. vm_refl. Qed.
Lemma D_14e20 : decode_any W_14e20 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e24 : bv 32 := 0xff010113.
Lemma F_14e24 : fetch_word Ubsan.M.loaded_segments (0x14e24 : word) = Some W_14e24.
Proof. vm_refl. Qed.
Lemma D_14e24 : decode_any W_14e24 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e28 : bv 32 := 0x00113423.
Lemma F_14e28 : fetch_word Ubsan.M.loaded_segments (0x14e28 : word) = Some W_14e28.
Proof. vm_refl. Qed.
Lemma D_14e28 : decode_any W_14e28 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e2c : bv 32 := 0x00813023.
Lemma F_14e2c : fetch_word Ubsan.M.loaded_segments (0x14e2c : word) = Some W_14e2c.
Proof. vm_refl. Qed.
Lemma D_14e2c : decode_any W_14e2c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e30 : bv 32 := 0x01010413.
Lemma F_14e30 : fetch_word Ubsan.M.loaded_segments (0x14e30 : word) = Some W_14e30.
Proof. vm_refl. Qed.
Lemma D_14e30 : decode_any W_14e30 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e34 : bv 32 := 0x0001f517.
Lemma F_14e34 : fetch_word Ubsan.M.loaded_segments (0x14e34 : word) = Some W_14e34.
Proof. vm_refl. Qed.
Lemma D_14e34 : decode_any W_14e34 = Some (Auipc 10 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e38 : bv 32 := 0x20450513.
Lemma F_14e38 : fetch_word Ubsan.M.loaded_segments (0x14e38 : word) = Some W_14e38.
Proof. vm_refl. Qed.
Lemma D_14e38 : decode_any W_14e38 = Some (OpImm ALU_ADD 10 10 516, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e3c : bv 32 := 0x00054503.
Lemma F_14e3c : fetch_word Ubsan.M.loaded_segments (0x14e3c : word) = Some W_14e3c.
Proof. vm_refl. Qed.
Lemma D_14e3c : decode_any W_14e3c = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e40 : bv 32 := 0x00157513.
Lemma F_14e40 : fetch_word Ubsan.M.loaded_segments (0x14e40 : word) = Some W_14e40.
Proof. vm_refl. Qed.
Lemma D_14e40 : decode_any W_14e40 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e44 : bv 32 := 0x00050663.
Lemma F_14e44 : fetch_word Ubsan.M.loaded_segments (0x14e44 : word) = Some W_14e44.
Proof. vm_refl. Qed.
Lemma D_14e44 : decode_any W_14e44 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e48 : bv 32 := 0x0040006f.
Lemma F_14e48 : fetch_word Ubsan.M.loaded_segments (0x14e48 : word) = Some W_14e48.
Proof. vm_refl. Qed.
Lemma D_14e48 : decode_any W_14e48 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e4c : bv 32 := 0x0580006f.
Lemma F_14e4c : fetch_word Ubsan.M.loaded_segments (0x14e4c : word) = Some W_14e4c.
Proof. vm_refl. Qed.
Lemma D_14e4c : decode_any W_14e4c = Some (Jal 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e50 : bv 32 := 0x0001f517.
Lemma F_14e50 : fetch_word Ubsan.M.loaded_segments (0x14e50 : word) = Some W_14e50.
Proof. vm_refl. Qed.
Lemma D_14e50 : decode_any W_14e50 = Some (Auipc 10 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e54 : bv 32 := 0x1e850593.
Lemma F_14e54 : fetch_word Ubsan.M.loaded_segments (0x14e54 : word) = Some W_14e54.
Proof. vm_refl. Qed.
Lemma D_14e54 : decode_any W_14e54 = Some (OpImm ALU_ADD 11 10 488, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e58 : bv 32 := 0x00100513.
Lemma F_14e58 : fetch_word Ubsan.M.loaded_segments (0x14e58 : word) = Some W_14e58.
Proof. vm_refl. Qed.
Lemma D_14e58 : decode_any W_14e58 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e5c : bv 32 := 0x00a58023.
Lemma F_14e5c : fetch_word Ubsan.M.loaded_segments (0x14e5c : word) = Some W_14e5c.
Proof. vm_refl. Qed.
Lemma D_14e5c : decode_any W_14e5c = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e60 : bv 32 := 0x0001e517.
Lemma F_14e60 : fetch_word Ubsan.M.loaded_segments (0x14e60 : word) = Some W_14e60.
Proof. vm_refl. Qed.
Lemma D_14e60 : decode_any W_14e60 = Some (Auipc 10 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e64 : bv 32 := 0xee853503.
Lemma F_14e64 : fetch_word Ubsan.M.loaded_segments (0x14e64 : word) = Some W_14e64.
Proof. vm_refl. Qed.
Lemma D_14e64 : decode_any W_14e64 = Some (Load SZ8 true 10 10 3816, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e68 : bv 32 := 0x00050e63.
Lemma F_14e68 : fetch_word Ubsan.M.loaded_segments (0x14e68 : word) = Some W_14e68.
Proof. vm_refl. Qed.
Lemma D_14e68 : decode_any W_14e68 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e6c : bv 32 := 0x0040006f.
Lemma F_14e6c : fetch_word Ubsan.M.loaded_segments (0x14e6c : word) = Some W_14e6c.
Proof. vm_refl. Qed.
Lemma D_14e6c : decode_any W_14e6c = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e70 : bv 32 := 0x0001f517.
Lemma F_14e70 : fetch_word Ubsan.M.loaded_segments (0x14e70 : word) = Some W_14e70.
Proof. vm_refl. Qed.
Lemma D_14e70 : decode_any W_14e70 = Some (Auipc 10 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e74 : bv 32 := 0xf4850513.
Lemma F_14e74 : fetch_word Ubsan.M.loaded_segments (0x14e74 : word) = Some W_14e74.
Proof. vm_refl. Qed.
Lemma D_14e74 : decode_any W_14e74 = Some (OpImm ALU_ADD 10 10 3912, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e78 : bv 32 := 0x00053503.
Lemma F_14e78 : fetch_word Ubsan.M.loaded_segments (0x14e78 : word) = Some W_14e78.
Proof. vm_refl. Qed.
Lemma D_14e78 : decode_any W_14e78 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e7c : bv 32 := 0x751140ef.
Lemma F_14e7c : fetch_word Ubsan.M.loaded_segments (0x14e7c : word) = Some W_14e7c.
Proof. vm_refl. Qed.
Lemma D_14e7c : decode_any W_14e7c = Some (Jal 1 85840, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e80 : bv 32 := 0x0040006f.
Lemma F_14e80 : fetch_word Ubsan.M.loaded_segments (0x14e80 : word) = Some W_14e80.
Proof. vm_refl. Qed.
Lemma D_14e80 : decode_any W_14e80 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e84 : bv 32 := 0x0001e517.
Lemma F_14e84 : fetch_word Ubsan.M.loaded_segments (0x14e84 : word) = Some W_14e84.
Proof. vm_refl. Qed.
Lemma D_14e84 : decode_any W_14e84 = Some (Auipc 10 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e88 : bv 32 := 0xecc53503.
Lemma F_14e88 : fetch_word Ubsan.M.loaded_segments (0x14e88 : word) = Some W_14e88.
Proof. vm_refl. Qed.
Lemma D_14e88 : decode_any W_14e88 = Some (Load SZ8 true 10 10 3788, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e8c : bv 32 := 0x00050c63.
Lemma F_14e8c : fetch_word Ubsan.M.loaded_segments (0x14e8c : word) = Some W_14e8c.
Proof. vm_refl. Qed.
Lemma D_14e8c : decode_any W_14e8c = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e90 : bv 32 := 0x0040006f.
Lemma F_14e90 : fetch_word Ubsan.M.loaded_segments (0x14e90 : word) = Some W_14e90.
Proof. vm_refl. Qed.
Lemma D_14e90 : decode_any W_14e90 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e94 : bv 32 := 0xffffe517.
Lemma F_14e94 : fetch_word Ubsan.M.loaded_segments (0x14e94 : word) = Some W_14e94.
Proof. vm_refl. Qed.
Lemma D_14e94 : decode_any W_14e94 = Some (Auipc 10 1048574, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e98 : bv 32 := 0x96450513.
Lemma F_14e98 : fetch_word Ubsan.M.loaded_segments (0x14e98 : word) = Some W_14e98.
Proof. vm_refl. Qed.
Lemma D_14e98 : decode_any W_14e98 = Some (OpImm ALU_ADD 10 10 2404, 4%Z).
Proof. vm_refl. Qed.

Definition W_14e9c : bv 32 := 0x000000ef.
Lemma F_14e9c : fetch_word Ubsan.M.loaded_segments (0x14e9c : word) = Some W_14e9c.
Proof. vm_refl. Qed.
Lemma D_14e9c : decode_any W_14e9c = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14ea0 : bv 32 := 0x0040006f.
Lemma F_14ea0 : fetch_word Ubsan.M.loaded_segments (0x14ea0 : word) = Some W_14ea0.
Proof. vm_refl. Qed.
Lemma D_14ea0 : decode_any W_14ea0 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_14ea4 : bv 32 := 0x00813083.
Lemma F_14ea4 : fetch_word Ubsan.M.loaded_segments (0x14ea4 : word) = Some W_14ea4.
Proof. vm_refl. Qed.
Lemma D_14ea4 : decode_any W_14ea4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_14ea8 : bv 32 := 0x00013403.
Lemma F_14ea8 : fetch_word Ubsan.M.loaded_segments (0x14ea8 : word) = Some W_14ea8.
Proof. vm_refl. Qed.
Lemma D_14ea8 : decode_any W_14ea8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14eac : bv 32 := 0x01010113.
Lemma F_14eac : fetch_word Ubsan.M.loaded_segments (0x14eac : word) = Some W_14eac.
Proof. vm_refl. Qed.
Lemma D_14eac : decode_any W_14eac = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_14eb0 : bv 32 := 0x00008067.
Lemma F_14eb0 : fetch_word Ubsan.M.loaded_segments (0x14eb0 : word) = Some W_14eb0.
Proof. vm_refl. Qed.
Lemma D_14eb0 : decode_any W_14eb0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_152dc : bv 32 := 0x0002f517.
Lemma F_152dc : fetch_word Ubsan.M.loaded_segments (0x152dc : word) = Some W_152dc.
Proof. vm_refl. Qed.
Lemma D_152dc : decode_any W_152dc = Some (Auipc 10 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_152e0 : bv 32 := 0xd6854503.
Lemma F_152e0 : fetch_word Ubsan.M.loaded_segments (0x152e0 : word) = Some W_152e0.
Proof. vm_refl. Qed.
Lemma D_152e0 : decode_any W_152e0 = Some (Load SZ1 false 10 10 3432, 4%Z).
Proof. vm_refl. Qed.

Definition W_152e4 : bv 32 := 0x00051463.
Lemma F_152e4 : fetch_word Ubsan.M.loaded_segments (0x152e4 : word) = Some W_152e4.
Proof. vm_refl. Qed.
Lemma D_152e4 : decode_any W_152e4 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_152e8 : bv 32 := 0x00008067.
Lemma F_152e8 : fetch_word Ubsan.M.loaded_segments (0x152e8 : word) = Some W_152e8.
Proof. vm_refl. Qed.
Lemma D_152e8 : decode_any W_152e8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_152ec : bv 32 := 0xff010113.
Lemma F_152ec : fetch_word Ubsan.M.loaded_segments (0x152ec : word) = Some W_152ec.
Proof. vm_refl. Qed.
Lemma D_152ec : decode_any W_152ec = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_152f0 : bv 32 := 0x00113423.
Lemma F_152f0 : fetch_word Ubsan.M.loaded_segments (0x152f0 : word) = Some W_152f0.
Proof. vm_refl. Qed.
Lemma D_152f0 : decode_any W_152f0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_152f4 : bv 32 := 0x0001e517.
Lemma F_152f4 : fetch_word Ubsan.M.loaded_segments (0x152f4 : word) = Some W_152f4.
Proof. vm_refl. Qed.
Lemma D_152f4 : decode_any W_152f4 = Some (Auipc 10 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_152f8 : bv 32 := 0xa7453503.
Lemma F_152f8 : fetch_word Ubsan.M.loaded_segments (0x152f8 : word) = Some W_152f8.
Proof. vm_refl. Qed.
Lemma D_152f8 : decode_any W_152f8 = Some (Load SZ8 true 10 10 2676, 4%Z).
Proof. vm_refl. Qed.

Definition W_152fc : bv 32 := 0x00053503.
Lemma F_152fc : fetch_word Ubsan.M.loaded_segments (0x152fc : word) = Some W_152fc.
Proof. vm_refl. Qed.
Lemma D_152fc : decode_any W_152fc = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15300 : bv 32 := 0x441160ef.
Lemma F_15300 : fetch_word Ubsan.M.loaded_segments (0x15300 : word) = Some W_15300.
Proof. vm_refl. Qed.
Lemma D_15300 : decode_any W_15300 = Some (Jal 1 93248, 4%Z).
Proof. vm_refl. Qed.

Definition W_15304 : bv 32 := 0x04d00513.
Lemma F_15304 : fetch_word Ubsan.M.loaded_segments (0x15304 : word) = Some W_15304.
Proof. vm_refl. Qed.
Lemma D_15304 : decode_any W_15304 = Some (OpImm ALU_ADD 10 0 77, 4%Z).
Proof. vm_refl. Qed.

Definition W_15308 : bv 32 := 0x14d1c0ef.
Lemma F_15308 : fetch_word Ubsan.M.loaded_segments (0x15308 : word) = Some W_15308.
Proof. vm_refl. Qed.
Lemma D_15308 : decode_any W_15308 = Some (Jal 1 117068, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d04 : bv 32 := 0xfd010113.
Lemma F_29d04 : fetch_word Ubsan.M.loaded_segments (0x29d04 : word) = Some W_29d04.
Proof. vm_refl. Qed.
Lemma D_29d04 : decode_any W_29d04 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d08 : bv 32 := 0x02113423.
Lemma F_29d08 : fetch_word Ubsan.M.loaded_segments (0x29d08 : word) = Some W_29d08.
Proof. vm_refl. Qed.
Lemma D_29d08 : decode_any W_29d08 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d0c : bv 32 := 0x02813023.
Lemma F_29d0c : fetch_word Ubsan.M.loaded_segments (0x29d0c : word) = Some W_29d0c.
Proof. vm_refl. Qed.
Lemma D_29d0c : decode_any W_29d0c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d10 : bv 32 := 0x00913c23.
Lemma F_29d10 : fetch_word Ubsan.M.loaded_segments (0x29d10 : word) = Some W_29d10.
Proof. vm_refl. Qed.
Lemma D_29d10 : decode_any W_29d10 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d14 : bv 32 := 0x01213823.
Lemma F_29d14 : fetch_word Ubsan.M.loaded_segments (0x29d14 : word) = Some W_29d14.
Proof. vm_refl. Qed.
Lemma D_29d14 : decode_any W_29d14 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d18 : bv 32 := 0x01313423.
Lemma F_29d18 : fetch_word Ubsan.M.loaded_segments (0x29d18 : word) = Some W_29d18.
Proof. vm_refl. Qed.
Lemma D_29d18 : decode_any W_29d18 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d1c : bv 32 := 0x0003a517.
Lemma F_29d1c : fetch_word Ubsan.M.loaded_segments (0x29d1c : word) = Some W_29d1c.
Proof. vm_refl. Qed.
Lemma D_29d1c : decode_any W_29d1c = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d20 : bv 32 := 0x46450913.
Lemma F_29d20 : fetch_word Ubsan.M.loaded_segments (0x29d20 : word) = Some W_29d20.
Proof. vm_refl. Qed.
Lemma D_29d20 : decode_any W_29d20 = Some (OpImm ALU_ADD 18 10 1124, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d24 : bv 32 := 0x00490413.
Lemma F_29d24 : fetch_word Ubsan.M.loaded_segments (0x29d24 : word) = Some W_29d24.
Proof. vm_refl. Qed.
Lemma D_29d24 : decode_any W_29d24 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d28 : bv 32 := 0x00040513.
Lemma F_29d28 : fetch_word Ubsan.M.loaded_segments (0x29d28 : word) = Some W_29d28.
Proof. vm_refl. Qed.
Lemma D_29d28 : decode_any W_29d28 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d2c : bv 32 := 0x3f9070ef.
Lemma F_29d2c : fetch_word Ubsan.M.loaded_segments (0x29d2c : word) = Some W_29d2c.
Proof. vm_refl. Qed.
Lemma D_29d2c : decode_any W_29d2c = Some (Jal 1 31736, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d30 : bv 32 := 0x01093503.
Lemma F_29d30 : fetch_word Ubsan.M.loaded_segments (0x29d30 : word) = Some W_29d30.
Proof. vm_refl. Qed.
Lemma D_29d30 : decode_any W_29d30 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d34 : bv 32 := 0x06050863.
Lemma F_29d34 : fetch_word Ubsan.M.loaded_segments (0x29d34 : word) = Some W_29d34.
Proof. vm_refl. Qed.
Lemma D_29d34 : decode_any W_29d34 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d38 : bv 32 := 0x00892583.
Lemma F_29d38 : fetch_word Ubsan.M.loaded_segments (0x29d38 : word) = Some W_29d38.
Proof. vm_refl. Qed.
Lemma D_29d38 : decode_any W_29d38 = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d3c : bv 32 := 0x0180006f.
Lemma F_29d3c : fetch_word Ubsan.M.loaded_segments (0x29d3c : word) = Some W_29d3c.
Proof. vm_refl. Qed.
Lemma D_29d3c : decode_any W_29d3c = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d40 : bv 32 := 0x00053503.
Lemma F_29d40 : fetch_word Ubsan.M.loaded_segments (0x29d40 : word) = Some W_29d40.
Proof. vm_refl. Qed.
Lemma D_29d40 : decode_any W_29d40 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d44 : bv 32 := 0x02000593.
Lemma F_29d44 : fetch_word Ubsan.M.loaded_segments (0x29d44 : word) = Some W_29d44.
Proof. vm_refl. Qed.
Lemma D_29d44 : decode_any W_29d44 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d48 : bv 32 := 0x00b92423.
Lemma F_29d48 : fetch_word Ubsan.M.loaded_segments (0x29d48 : word) = Some W_29d48.
Proof. vm_refl. Qed.
Lemma D_29d48 : decode_any W_29d48 = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d4c : bv 32 := 0x00a93823.
Lemma F_29d4c : fetch_word Ubsan.M.loaded_segments (0x29d4c : word) = Some W_29d4c.
Proof. vm_refl. Qed.
Lemma D_29d4c : decode_any W_29d4c = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d50 : bv 32 := 0x04050a63.
Lemma F_29d50 : fetch_word Ubsan.M.loaded_segments (0x29d50 : word) = Some W_29d50.
Proof. vm_refl. Qed.
Lemma D_29d50 : decode_any W_29d50 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d54 : bv 32 := 0xfff5861b.
Lemma F_29d54 : fetch_word Ubsan.M.loaded_segments (0x29d54 : word) = Some W_29d54.
Proof. vm_refl. Qed.
Lemma D_29d54 : decode_any W_29d54 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d58 : bv 32 := 0x00c92423.
Lemma F_29d58 : fetch_word Ubsan.M.loaded_segments (0x29d58 : word) = Some W_29d58.
Proof. vm_refl. Qed.
Lemma D_29d58 : decode_any W_29d58 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d5c : bv 32 := 0xfeb052e3.
Lemma F_29d5c : fetch_word Ubsan.M.loaded_segments (0x29d5c : word) = Some W_29d5c.
Proof. vm_refl. Qed.
Lemma D_29d5c : decode_any W_29d5c = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d60 : bv 32 := 0x01093503.
Lemma F_29d60 : fetch_word Ubsan.M.loaded_segments (0x29d60 : word) = Some W_29d60.
Proof. vm_refl. Qed.
Lemma D_29d60 : decode_any W_29d60 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d64 : bv 32 := 0x00361613.
Lemma F_29d64 : fetch_word Ubsan.M.loaded_segments (0x29d64 : word) = Some W_29d64.
Proof. vm_refl. Qed.
Lemma D_29d64 : decode_any W_29d64 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d68 : bv 32 := 0x00c50533.
Lemma F_29d68 : fetch_word Ubsan.M.loaded_segments (0x29d68 : word) = Some W_29d68.
Proof. vm_refl. Qed.
Lemma D_29d68 : decode_any W_29d68 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d6c : bv 32 := 0x00853983.
Lemma F_29d6c : fetch_word Ubsan.M.loaded_segments (0x29d6c : word) = Some W_29d6c.
Proof. vm_refl. Qed.
Lemma D_29d6c : decode_any W_29d6c = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d70 : bv 32 := 0x10853483.
Lemma F_29d70 : fetch_word Ubsan.M.loaded_segments (0x29d70 : word) = Some W_29d70.
Proof. vm_refl. Qed.
Lemma D_29d70 : decode_any W_29d70 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d74 : bv 32 := 0x00040513.
Lemma F_29d74 : fetch_word Ubsan.M.loaded_segments (0x29d74 : word) = Some W_29d74.
Proof. vm_refl. Qed.
Lemma D_29d74 : decode_any W_29d74 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d78 : bv 32 := 0x635070ef.
Lemma F_29d78 : fetch_word Ubsan.M.loaded_segments (0x29d78 : word) = Some W_29d78.
Proof. vm_refl. Qed.
Lemma D_29d78 : decode_any W_29d78 = Some (Jal 1 32308, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d7c : bv 32 := 0x00048513.
Lemma F_29d7c : fetch_word Ubsan.M.loaded_segments (0x29d7c : word) = Some W_29d7c.
Proof. vm_refl. Qed.
Lemma D_29d7c : decode_any W_29d7c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d80 : bv 32 := 0x000980e7.
Lemma F_29d80 : fetch_word Ubsan.M.loaded_segments (0x29d80 : word) = Some W_29d80.
Proof. vm_refl. Qed.
Lemma D_29d80 : decode_any W_29d80 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d84 : bv 32 := 0x00040513.
Lemma F_29d84 : fetch_word Ubsan.M.loaded_segments (0x29d84 : word) = Some W_29d84.
Proof. vm_refl. Qed.
Lemma D_29d84 : decode_any W_29d84 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d88 : bv 32 := 0x39d070ef.
Lemma F_29d88 : fetch_word Ubsan.M.loaded_segments (0x29d88 : word) = Some W_29d88.
Proof. vm_refl. Qed.
Lemma D_29d88 : decode_any W_29d88 = Some (Jal 1 31644, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d8c : bv 32 := 0x00892503.
Lemma F_29d8c : fetch_word Ubsan.M.loaded_segments (0x29d8c : word) = Some W_29d8c.
Proof. vm_refl. Qed.
Lemma D_29d8c : decode_any W_29d8c = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d90 : bv 32 := 0xfff5061b.
Lemma F_29d90 : fetch_word Ubsan.M.loaded_segments (0x29d90 : word) = Some W_29d90.
Proof. vm_refl. Qed.
Lemma D_29d90 : decode_any W_29d90 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d94 : bv 32 := 0x00c92423.
Lemma F_29d94 : fetch_word Ubsan.M.loaded_segments (0x29d94 : word) = Some W_29d94.
Proof. vm_refl. Qed.
Lemma D_29d94 : decode_any W_29d94 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d98 : bv 32 := 0xfca044e3.
Lemma F_29d98 : fetch_word Ubsan.M.loaded_segments (0x29d98 : word) = Some W_29d98.
Proof. vm_refl. Qed.
Lemma D_29d98 : decode_any W_29d98 = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_29d9c : bv 32 := 0x01093503.
Lemma F_29d9c : fetch_word Ubsan.M.loaded_segments (0x29d9c : word) = Some W_29d9c.
Proof. vm_refl. Qed.
Lemma D_29d9c : decode_any W_29d9c = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_29da0 : bv 32 := 0xfa1ff06f.
Lemma F_29da0 : fetch_word Ubsan.M.loaded_segments (0x29da0 : word) = Some W_29da0.
Proof. vm_refl. Qed.
Lemma D_29da0 : decode_any W_29da0 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

Definition W_29da4 : bv 32 := 0x00100513.
Lemma F_29da4 : fetch_word Ubsan.M.loaded_segments (0x29da4 : word) = Some W_29da4.
Proof. vm_refl. Qed.
Lemma D_29da4 : decode_any W_29da4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_29da8 : bv 32 := 0x00a90023.
Lemma F_29da8 : fetch_word Ubsan.M.loaded_segments (0x29da8 : word) = Some W_29da8.
Proof. vm_refl. Qed.
Lemma D_29da8 : decode_any W_29da8 = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29dac : bv 32 := 0x00040513.
Lemma F_29dac : fetch_word Ubsan.M.loaded_segments (0x29dac : word) = Some W_29dac.
Proof. vm_refl. Qed.
Lemma D_29dac : decode_any W_29dac = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29db0 : bv 32 := 0x02813083.
Lemma F_29db0 : fetch_word Ubsan.M.loaded_segments (0x29db0 : word) = Some W_29db0.
Proof. vm_refl. Qed.
Lemma D_29db0 : decode_any W_29db0 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_29db4 : bv 32 := 0x02013403.
Lemma F_29db4 : fetch_word Ubsan.M.loaded_segments (0x29db4 : word) = Some W_29db4.
Proof. vm_refl. Qed.
Lemma D_29db4 : decode_any W_29db4 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_29db8 : bv 32 := 0x01813483.
Lemma F_29db8 : fetch_word Ubsan.M.loaded_segments (0x29db8 : word) = Some W_29db8.
Proof. vm_refl. Qed.
Lemma D_29db8 : decode_any W_29db8 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_29dbc : bv 32 := 0x01013903.
Lemma F_29dbc : fetch_word Ubsan.M.loaded_segments (0x29dbc : word) = Some W_29dbc.
Proof. vm_refl. Qed.
Lemma D_29dbc : decode_any W_29dbc = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_29dc0 : bv 32 := 0x00813983.
Lemma F_29dc0 : fetch_word Ubsan.M.loaded_segments (0x29dc0 : word) = Some W_29dc0.
Proof. vm_refl. Qed.
Lemma D_29dc0 : decode_any W_29dc0 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_29dc4 : bv 32 := 0x03010113.
Lemma F_29dc4 : fetch_word Ubsan.M.loaded_segments (0x29dc4 : word) = Some W_29dc4.
Proof. vm_refl. Qed.
Lemma D_29dc4 : decode_any W_29dc4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_29dc8 : bv 32 := 0x5e50706f.
Lemma F_29dc8 : fetch_word Ubsan.M.loaded_segments (0x29dc8 : word) = Some W_29dc8.
Proof. vm_refl. Qed.
Lemma D_29dc8 : decode_any W_29dc8 = Some (Jal 0 32228, 4%Z).
Proof. vm_refl. Qed.

Definition W_29dcc : bv 32 := 0x00008067.
Lemma F_29dcc : fetch_word Ubsan.M.loaded_segments (0x29dcc : word) = Some W_29dcc.
Proof. vm_refl. Qed.
Lemma D_29dcc : decode_any W_29dcc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29dd0 : bv 32 := 0xfd010113.
Lemma F_29dd0 : fetch_word Ubsan.M.loaded_segments (0x29dd0 : word) = Some W_29dd0.
Proof. vm_refl. Qed.
Lemma D_29dd0 : decode_any W_29dd0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_29dd4 : bv 32 := 0x02113423.
Lemma F_29dd4 : fetch_word Ubsan.M.loaded_segments (0x29dd4 : word) = Some W_29dd4.
Proof. vm_refl. Qed.
Lemma D_29dd4 : decode_any W_29dd4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_29dd8 : bv 32 := 0x02813023.
Lemma F_29dd8 : fetch_word Ubsan.M.loaded_segments (0x29dd8 : word) = Some W_29dd8.
Proof. vm_refl. Qed.
Lemma D_29dd8 : decode_any W_29dd8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_29ddc : bv 32 := 0x00913c23.
Lemma F_29ddc : fetch_word Ubsan.M.loaded_segments (0x29ddc : word) = Some W_29ddc.
Proof. vm_refl. Qed.
Lemma D_29ddc : decode_any W_29ddc = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_29de0 : bv 32 := 0x01213823.
Lemma F_29de0 : fetch_word Ubsan.M.loaded_segments (0x29de0 : word) = Some W_29de0.
Proof. vm_refl. Qed.
Lemma D_29de0 : decode_any W_29de0 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_29de4 : bv 32 := 0x01313423.
Lemma F_29de4 : fetch_word Ubsan.M.loaded_segments (0x29de4 : word) = Some W_29de4.
Proof. vm_refl. Qed.
Lemma D_29de4 : decode_any W_29de4 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_29de8 : bv 32 := 0x00050493.
Lemma F_29de8 : fetch_word Ubsan.M.loaded_segments (0x29de8 : word) = Some W_29de8.
Proof. vm_refl. Qed.
Lemma D_29de8 : decode_any W_29de8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29dec : bv 32 := 0x0003a517.
Lemma F_29dec : fetch_word Ubsan.M.loaded_segments (0x29dec : word) = Some W_29dec.
Proof. vm_refl. Qed.
Lemma D_29dec : decode_any W_29dec = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_29df0 : bv 32 := 0x39450993.
Lemma F_29df0 : fetch_word Ubsan.M.loaded_segments (0x29df0 : word) = Some W_29df0.
Proof. vm_refl. Qed.
Lemma D_29df0 : decode_any W_29df0 = Some (OpImm ALU_ADD 19 10 916, 4%Z).
Proof. vm_refl. Qed.

Definition W_29df4 : bv 32 := 0x00498413.
Lemma F_29df4 : fetch_word Ubsan.M.loaded_segments (0x29df4 : word) = Some W_29df4.
Proof. vm_refl. Qed.
Lemma D_29df4 : decode_any W_29df4 = Some (OpImm ALU_ADD 8 19 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_29df8 : bv 32 := 0x00040513.
Lemma F_29df8 : fetch_word Ubsan.M.loaded_segments (0x29df8 : word) = Some W_29df8.
Proof. vm_refl. Qed.
Lemma D_29df8 : decode_any W_29df8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29dfc : bv 32 := 0x329070ef.
Lemma F_29dfc : fetch_word Ubsan.M.loaded_segments (0x29dfc : word) = Some W_29dfc.
Proof. vm_refl. Qed.
Lemma D_29dfc : decode_any W_29dfc = Some (Jal 1 31528, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e00 : bv 32 := 0x0009c503.
Lemma F_29e00 : fetch_word Ubsan.M.loaded_segments (0x29e00 : word) = Some W_29e00.
Proof. vm_refl. Qed.
Lemma D_29e00 : decode_any W_29e00 = Some (Load SZ1 false 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e04 : bv 32 := 0xfff00913.
Lemma F_29e04 : fetch_word Ubsan.M.loaded_segments (0x29e04 : word) = Some W_29e04.
Proof. vm_refl. Qed.
Lemma D_29e04 : decode_any W_29e04 = Some (OpImm ALU_ADD 18 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e08 : bv 32 := 0x06051263.
Lemma F_29e08 : fetch_word Ubsan.M.loaded_segments (0x29e08 : word) = Some W_29e08.
Proof. vm_refl. Qed.
Lemma D_29e08 : decode_any W_29e08 = Some (Branch BC_NE 10 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e0c : bv 32 := 0x0109b503.
Lemma F_29e0c : fetch_word Ubsan.M.loaded_segments (0x29e0c : word) = Some W_29e0c.
Proof. vm_refl. Qed.
Lemma D_29e0c : decode_any W_29e0c = Some (Load SZ8 true 10 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e10 : bv 32 := 0x00051663.
Lemma F_29e10 : fetch_word Ubsan.M.loaded_segments (0x29e10 : word) = Some W_29e10.
Proof. vm_refl. Qed.
Lemma D_29e10 : decode_any W_29e10 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e14 : bv 32 := 0x01898513.
Lemma F_29e14 : fetch_word Ubsan.M.loaded_segments (0x29e14 : word) = Some W_29e14.
Proof. vm_refl. Qed.
Lemma D_29e14 : decode_any W_29e14 = Some (OpImm ALU_ADD 10 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e18 : bv 32 := 0x00a9b823.
Lemma F_29e18 : fetch_word Ubsan.M.loaded_segments (0x29e18 : word) = Some W_29e18.
Proof. vm_refl. Qed.
Lemma D_29e18 : decode_any W_29e18 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e1c : bv 32 := 0x0089a583.
Lemma F_29e1c : fetch_word Ubsan.M.loaded_segments (0x29e1c : word) = Some W_29e1c.
Proof. vm_refl. Qed.
Lemma D_29e1c : decode_any W_29e1c = Some (Load SZ4 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e20 : bv 32 := 0x02000613.
Lemma F_29e20 : fetch_word Ubsan.M.loaded_segments (0x29e20 : word) = Some W_29e20.
Proof. vm_refl. Qed.
Lemma D_29e20 : decode_any W_29e20 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e24 : bv 32 := 0x02c59263.
Lemma F_29e24 : fetch_word Ubsan.M.loaded_segments (0x29e24 : word) = Some W_29e24.
Proof. vm_refl. Qed.
Lemma D_29e24 : decode_any W_29e24 = Some (Branch BC_NE 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e28 : bv 32 := 0x20800513.
Lemma F_29e28 : fetch_word Ubsan.M.loaded_segments (0x29e28 : word) = Some W_29e28.
Proof. vm_refl. Qed.
Lemma D_29e28 : decode_any W_29e28 = Some (OpImm ALU_ADD 10 0 520, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e2c : bv 32 := 0x00100593.
Lemma F_29e2c : fetch_word Ubsan.M.loaded_segments (0x29e2c : word) = Some W_29e2c.
Proof. vm_refl. Qed.
Lemma D_29e2c : decode_any W_29e2c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e30 : bv 32 := 0x3f4000ef.
Lemma F_29e30 : fetch_word Ubsan.M.loaded_segments (0x29e30 : word) = Some W_29e30.
Proof. vm_refl. Qed.
Lemma D_29e30 : decode_any W_29e30 = Some (Jal 1 1012, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e34 : bv 32 := 0x02050c63.
Lemma F_29e34 : fetch_word Ubsan.M.loaded_segments (0x29e34 : word) = Some W_29e34.
Proof. vm_refl. Qed.
Lemma D_29e34 : decode_any W_29e34 = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e38 : bv 32 := 0x00000593.
Lemma F_29e38 : fetch_word Ubsan.M.loaded_segments (0x29e38 : word) = Some W_29e38.
Proof. vm_refl. Qed.
Lemma D_29e38 : decode_any W_29e38 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e3c : bv 32 := 0x0109b603.
Lemma F_29e3c : fetch_word Ubsan.M.loaded_segments (0x29e3c : word) = Some W_29e3c.
Proof. vm_refl. Qed.
Lemma D_29e3c : decode_any W_29e3c = Some (Load SZ8 true 12 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e40 : bv 32 := 0x00c53023.
Lemma F_29e40 : fetch_word Ubsan.M.loaded_segments (0x29e40 : word) = Some W_29e40.
Proof. vm_refl. Qed.
Lemma D_29e40 : decode_any W_29e40 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e44 : bv 32 := 0x00a9b823.
Lemma F_29e44 : fetch_word Ubsan.M.loaded_segments (0x29e44 : word) = Some W_29e44.
Proof. vm_refl. Qed.
Lemma D_29e44 : decode_any W_29e44 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e48 : bv 32 := 0x00000913.
Lemma F_29e48 : fetch_word Ubsan.M.loaded_segments (0x29e48 : word) = Some W_29e48.
Proof. vm_refl. Qed.
Lemma D_29e48 : decode_any W_29e48 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e4c : bv 32 := 0x00359613.
Lemma F_29e4c : fetch_word Ubsan.M.loaded_segments (0x29e4c : word) = Some W_29e4c.
Proof. vm_refl. Qed.
Lemma D_29e4c : decode_any W_29e4c = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e50 : bv 32 := 0x00c50533.
Lemma F_29e50 : fetch_word Ubsan.M.loaded_segments (0x29e50 : word) = Some W_29e50.
Proof. vm_refl. Qed.
Lemma D_29e50 : decode_any W_29e50 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e54 : bv 32 := 0x00000617.
Lemma F_29e54 : fetch_word Ubsan.M.loaded_segments (0x29e54 : word) = Some W_29e54.
Proof. vm_refl. Qed.
Lemma D_29e54 : decode_any W_29e54 = Some (Auipc 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e58 : bv 32 := 0x00158593.
Lemma F_29e58 : fetch_word Ubsan.M.loaded_segments (0x29e58 : word) = Some W_29e58.
Proof. vm_refl. Qed.
Lemma D_29e58 : decode_any W_29e58 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e5c : bv 32 := 0x04060613.
Lemma F_29e5c : fetch_word Ubsan.M.loaded_segments (0x29e5c : word) = Some W_29e5c.
Proof. vm_refl. Qed.
Lemma D_29e5c : decode_any W_29e5c = Some (OpImm ALU_ADD 12 12 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e60 : bv 32 := 0x00c53423.
Lemma F_29e60 : fetch_word Ubsan.M.loaded_segments (0x29e60 : word) = Some W_29e60.
Proof. vm_refl. Qed.
Lemma D_29e60 : decode_any W_29e60 = Some (Store SZ8 10 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e64 : bv 32 := 0x10953423.
Lemma F_29e64 : fetch_word Ubsan.M.loaded_segments (0x29e64 : word) = Some W_29e64.
Proof. vm_refl. Qed.
Lemma D_29e64 : decode_any W_29e64 = Some (Store SZ8 10 9 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e68 : bv 32 := 0x00b9a423.
Lemma F_29e68 : fetch_word Ubsan.M.loaded_segments (0x29e68 : word) = Some W_29e68.
Proof. vm_refl. Qed.
Lemma D_29e68 : decode_any W_29e68 = Some (Store SZ4 19 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e6c : bv 32 := 0x00040513.
Lemma F_29e6c : fetch_word Ubsan.M.loaded_segments (0x29e6c : word) = Some W_29e6c.
Proof. vm_refl. Qed.
Lemma D_29e6c : decode_any W_29e6c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e70 : bv 32 := 0x53d070ef.
Lemma F_29e70 : fetch_word Ubsan.M.loaded_segments (0x29e70 : word) = Some W_29e70.
Proof. vm_refl. Qed.
Lemma D_29e70 : decode_any W_29e70 = Some (Jal 1 32060, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e74 : bv 32 := 0x00090513.
Lemma F_29e74 : fetch_word Ubsan.M.loaded_segments (0x29e74 : word) = Some W_29e74.
Proof. vm_refl. Qed.
Lemma D_29e74 : decode_any W_29e74 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e78 : bv 32 := 0x02813083.
Lemma F_29e78 : fetch_word Ubsan.M.loaded_segments (0x29e78 : word) = Some W_29e78.
Proof. vm_refl. Qed.
Lemma D_29e78 : decode_any W_29e78 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e7c : bv 32 := 0x02013403.
Lemma F_29e7c : fetch_word Ubsan.M.loaded_segments (0x29e7c : word) = Some W_29e7c.
Proof. vm_refl. Qed.
Lemma D_29e7c : decode_any W_29e7c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e80 : bv 32 := 0x01813483.
Lemma F_29e80 : fetch_word Ubsan.M.loaded_segments (0x29e80 : word) = Some W_29e80.
Proof. vm_refl. Qed.
Lemma D_29e80 : decode_any W_29e80 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e84 : bv 32 := 0x01013903.
Lemma F_29e84 : fetch_word Ubsan.M.loaded_segments (0x29e84 : word) = Some W_29e84.
Proof. vm_refl. Qed.
Lemma D_29e84 : decode_any W_29e84 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e88 : bv 32 := 0x00813983.
Lemma F_29e88 : fetch_word Ubsan.M.loaded_segments (0x29e88 : word) = Some W_29e88.
Proof. vm_refl. Qed.
Lemma D_29e88 : decode_any W_29e88 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e8c : bv 32 := 0x03010113.
Lemma F_29e8c : fetch_word Ubsan.M.loaded_segments (0x29e8c : word) = Some W_29e8c.
Proof. vm_refl. Qed.
Lemma D_29e8c : decode_any W_29e8c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e90 : bv 32 := 0x00008067.
Lemma F_29e90 : fetch_word Ubsan.M.loaded_segments (0x29e90 : word) = Some W_29e90.
Proof. vm_refl. Qed.
Lemma D_29e90 : decode_any W_29e90 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e94 : bv 32 := 0x00050067.
Lemma F_29e94 : fetch_word Ubsan.M.loaded_segments (0x29e94 : word) = Some W_29e94.
Proof. vm_refl. Qed.
Lemma D_29e94 : decode_any W_29e94 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e98 : bv 32 := 0x00008067.
Lemma F_29e98 : fetch_word Ubsan.M.loaded_segments (0x29e98 : word) = Some W_29e98.
Proof. vm_refl. Qed.
Lemma D_29e98 : decode_any W_29e98 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29e9c : bv 32 := 0xfe010113.
Lemma F_29e9c : fetch_word Ubsan.M.loaded_segments (0x29e9c : word) = Some W_29e9c.
Proof. vm_refl. Qed.
Lemma D_29e9c : decode_any W_29e9c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_29ea0 : bv 32 := 0x00113c23.
Lemma F_29ea0 : fetch_word Ubsan.M.loaded_segments (0x29ea0 : word) = Some W_29ea0.
Proof. vm_refl. Qed.
Lemma D_29ea0 : decode_any W_29ea0 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_29ea4 : bv 32 := 0x00813823.
Lemma F_29ea4 : fetch_word Ubsan.M.loaded_segments (0x29ea4 : word) = Some W_29ea4.
Proof. vm_refl. Qed.
Lemma D_29ea4 : decode_any W_29ea4 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_29ea8 : bv 32 := 0x00913423.
Lemma F_29ea8 : fetch_word Ubsan.M.loaded_segments (0x29ea8 : word) = Some W_29ea8.
Proof. vm_refl. Qed.
Lemma D_29ea8 : decode_any W_29ea8 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_29eac : bv 32 := 0x00009517.
Lemma F_29eac : fetch_word Ubsan.M.loaded_segments (0x29eac : word) = Some W_29eac.
Proof. vm_refl. Qed.
Lemma D_29eac : decode_any W_29eac = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_29eb0 : bv 32 := 0x00009597.
Lemma F_29eb0 : fetch_word Ubsan.M.loaded_segments (0x29eb0 : word) = Some W_29eb0.
Proof. vm_refl. Qed.
Lemma D_29eb0 : decode_any W_29eb0 = Some (Auipc 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_29eb4 : bv 32 := 0xefc53503.
Lemma F_29eb4 : fetch_word Ubsan.M.loaded_segments (0x29eb4 : word) = Some W_29eb4.
Proof. vm_refl. Qed.
Lemma D_29eb4 : decode_any W_29eb4 = Some (Load SZ8 true 10 10 3836, 4%Z).
Proof. vm_refl. Qed.

Definition W_29eb8 : bv 32 := 0xf005b403.
Lemma F_29eb8 : fetch_word Ubsan.M.loaded_segments (0x29eb8 : word) = Some W_29eb8.
Proof. vm_refl. Qed.
Lemma D_29eb8 : decode_any W_29eb8 = Some (Load SZ8 true 8 11 3840, 4%Z).
Proof. vm_refl. Qed.

Definition W_29ebc : bv 32 := 0x00a47c63.
Lemma F_29ebc : fetch_word Ubsan.M.loaded_segments (0x29ebc : word) = Some W_29ebc.
Proof. vm_refl. Qed.
Lemma D_29ebc : decode_any W_29ebc = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_29ec0 : bv 32 := 0xff853583.
Lemma F_29ec0 : fetch_word Ubsan.M.loaded_segments (0x29ec0 : word) = Some W_29ec0.
Proof. vm_refl. Qed.
Lemma D_29ec0 : decode_any W_29ec0 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_29ec4 : bv 32 := 0xff850493.
Lemma F_29ec4 : fetch_word Ubsan.M.loaded_segments (0x29ec4 : word) = Some W_29ec4.
Proof. vm_refl. Qed.
Lemma D_29ec4 : decode_any W_29ec4 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_29ec8 : bv 32 := 0x000580e7.
Lemma F_29ec8 : fetch_word Ubsan.M.loaded_segments (0x29ec8 : word) = Some W_29ec8.
Proof. vm_refl. Qed.
Lemma D_29ec8 : decode_any W_29ec8 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29ecc : bv 32 := 0x00048513.
Lemma F_29ecc : fetch_word Ubsan.M.loaded_segments (0x29ecc : word) = Some W_29ecc.
Proof. vm_refl. Qed.
Lemma D_29ecc : decode_any W_29ecc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29ed0 : bv 32 := 0xfe9468e3.
Lemma F_29ed0 : fetch_word Ubsan.M.loaded_segments (0x29ed0 : word) = Some W_29ed0.
Proof. vm_refl. Qed.
Lemma D_29ed0 : decode_any W_29ed0 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_29ed4 : bv 32 := 0x01813083.
Lemma F_29ed4 : fetch_word Ubsan.M.loaded_segments (0x29ed4 : word) = Some W_29ed4.
Proof. vm_refl. Qed.
Lemma D_29ed4 : decode_any W_29ed4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_29ed8 : bv 32 := 0x01013403.
Lemma F_29ed8 : fetch_word Ubsan.M.loaded_segments (0x29ed8 : word) = Some W_29ed8.
Proof. vm_refl. Qed.
Lemma D_29ed8 : decode_any W_29ed8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_29edc : bv 32 := 0x00813483.
Lemma F_29edc : fetch_word Ubsan.M.loaded_segments (0x29edc : word) = Some W_29edc.
Proof. vm_refl. Qed.
Lemma D_29edc : decode_any W_29edc = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_29ee0 : bv 32 := 0x02010113.
Lemma F_29ee0 : fetch_word Ubsan.M.loaded_segments (0x29ee0 : word) = Some W_29ee0.
Proof. vm_refl. Qed.
Lemma D_29ee0 : decode_any W_29ee0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_29ee4 : bv 32 := 0xfb5ff06f.
Lemma F_29ee4 : fetch_word Ubsan.M.loaded_segments (0x29ee4 : word) = Some W_29ee4.
Proof. vm_refl. Qed.
Lemma D_29ee4 : decode_any W_29ee4 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

Definition W_29ee8 : bv 32 := 0xff010113.
Lemma F_29ee8 : fetch_word Ubsan.M.loaded_segments (0x29ee8 : word) = Some W_29ee8.
Proof. vm_refl. Qed.
Lemma D_29ee8 : decode_any W_29ee8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_29eec : bv 32 := 0x00113423.
Lemma F_29eec : fetch_word Ubsan.M.loaded_segments (0x29eec : word) = Some W_29eec.
Proof. vm_refl. Qed.
Lemma D_29eec : decode_any W_29eec = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_29ef0 : bv 32 := 0x00813023.
Lemma F_29ef0 : fetch_word Ubsan.M.loaded_segments (0x29ef0 : word) = Some W_29ef0.
Proof. vm_refl. Qed.
Lemma D_29ef0 : decode_any W_29ef0 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29ef4 : bv 32 := 0x00000593.
Lemma F_29ef4 : fetch_word Ubsan.M.loaded_segments (0x29ef4 : word) = Some W_29ef4.
Proof. vm_refl. Qed.
Lemma D_29ef4 : decode_any W_29ef4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29ef8 : bv 32 := 0x00020613.
Lemma F_29ef8 : fetch_word Ubsan.M.loaded_segments (0x29ef8 : word) = Some W_29ef8.
Proof. vm_refl. Qed.
Lemma D_29ef8 : decode_any W_29ef8 = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29efc : bv 32 := 0xf5862603.
Lemma F_29efc : fetch_word Ubsan.M.loaded_segments (0x29efc : word) = Some W_29efc.
Proof. vm_refl. Qed.
Lemma D_29efc : decode_any W_29efc = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

Definition W_29f00 : bv 32 := 0x0003a697.
Lemma F_29f00 : fetch_word Ubsan.M.loaded_segments (0x29f00 : word) = Some W_29f00.
Proof. vm_refl. Qed.
Lemma D_29f00 : decode_any W_29f00 = Some (Auipc 13 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_29f04 : bv 32 := 0x4a068693.
Lemma F_29f04 : fetch_word Ubsan.M.loaded_segments (0x29f04 : word) = Some W_29f04.
Proof. vm_refl. Qed.
Lemma D_29f04 : decode_any W_29f04 = Some (OpImm ALU_ADD 13 13 1184, 4%Z).
Proof. vm_refl. Qed.

Definition W_29f08 : bv 32 := 0x1606a72f.
Lemma F_29f08 : fetch_word Ubsan.M.loaded_segments (0x29f08 : word) = Some W_29f08.
Proof. vm_refl. Qed.
Lemma D_29f08 : decode_any W_29f08 = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_29f0c : bv 32 := 0x00b71663.
Lemma F_29f0c : fetch_word Ubsan.M.loaded_segments (0x29f0c : word) = Some W_29f0c.
Proof. vm_refl. Qed.
Lemma D_29f0c : decode_any W_29f0c = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_29f10 : bv 32 := 0x1ec6a7af.
Lemma F_29f10 : fetch_word Ubsan.M.loaded_segments (0x29f10 : word) = Some W_29f10.
Proof. vm_refl. Qed.
Lemma D_29f10 : decode_any W_29f10 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_29f14 : bv 32 := 0xfe079ae3.
Lemma F_29f14 : fetch_word Ubsan.M.loaded_segments (0x29f14 : word) = Some W_29f14.
Proof. vm_refl. Qed.
Lemma D_29f14 : decode_any W_29f14 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_29f18 : bv 32 := 0x0007059b.
Lemma F_29f18 : fetch_word Ubsan.M.loaded_segments (0x29f18 : word) = Some W_29f18.
Proof. vm_refl. Qed.
Lemma D_29f18 : decode_any W_29f18 = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29f1c : bv 32 := 0x02c58263.
Lemma F_29f1c : fetch_word Ubsan.M.loaded_segments (0x29f1c : word) = Some W_29f1c.
Proof. vm_refl. Qed.
Lemma D_29f1c : decode_any W_29f1c = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_29f20 : bv 32 := 0x02058263.
Lemma F_29f20 : fetch_word Ubsan.M.loaded_segments (0x29f20 : word) = Some W_29f20.
Proof. vm_refl. Qed.
Lemma D_29f20 : decode_any W_29f20 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_29f24 : bv 32 := 0x04900893.
Lemma F_29f24 : fetch_word Ubsan.M.loaded_segments (0x29f24 : word) = Some W_29f24.
Proof. vm_refl. Qed.
Lemma D_29f24 : decode_any W_29f24 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

Definition W_29f28 : bv 32 := 0x00000593.
Lemma F_29f28 : fetch_word Ubsan.M.loaded_segments (0x29f28 : word) = Some W_29f28.
Proof. vm_refl. Qed.
Lemma D_29f28 : decode_any W_29f28 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29f2c : bv 32 := 0x00000613.
Lemma F_29f2c : fetch_word Ubsan.M.loaded_segments (0x29f2c : word) = Some W_29f2c.
Proof. vm_refl. Qed.
Lemma D_29f2c : decode_any W_29f2c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29f30 : bv 32 := 0x00000693.
Lemma F_29f30 : fetch_word Ubsan.M.loaded_segments (0x29f30 : word) = Some W_29f30.
Proof. vm_refl. Qed.
Lemma D_29f30 : decode_any W_29f30 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29f34 : bv 32 := 0x00000513.
Lemma F_29f34 : fetch_word Ubsan.M.loaded_segments (0x29f34 : word) = Some W_29f34.
Proof. vm_refl. Qed.
Lemma D_29f34 : decode_any W_29f34 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29f38 : bv 32 := 0x00000073.
Lemma F_29f38 : fetch_word Ubsan.M.loaded_segments (0x29f38 : word) = Some W_29f38.
Proof. vm_refl. Qed.
Lemma E_29f38 : is_ecall W_29f38 = true.
Proof. vm_refl. Qed.

Definition W_29f3c : bv 32 := 0xff9ff06f.
Lemma F_29f3c : fetch_word Ubsan.M.loaded_segments (0x29f3c : word) = Some W_29f3c.
Proof. vm_refl. Qed.
Lemma D_29f3c : decode_any W_29f3c = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

Definition W_29f40 : bv 32 := 0x00000023.
Lemma F_29f40 : fetch_word Ubsan.M.loaded_segments (0x29f40 : word) = Some W_29f40.
Proof. vm_refl. Qed.
Lemma D_29f40 : decode_any W_29f40 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29f44 : bv 32 := 0x00050413.
Lemma F_29f44 : fetch_word Ubsan.M.loaded_segments (0x29f44 : word) = Some W_29f44.
Proof. vm_refl. Qed.
Lemma D_29f44 : decode_any W_29f44 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29f48 : bv 32 := 0xdbdff0ef.
Lemma F_29f48 : fetch_word Ubsan.M.loaded_segments (0x29f48 : word) = Some W_29f48.
Proof. vm_refl. Qed.
Lemma D_29f48 : decode_any W_29f48 = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

Definition W_29f4c : bv 32 := 0xf51ff0ef.
Lemma F_29f4c : fetch_word Ubsan.M.loaded_segments (0x29f4c : word) = Some W_29f4c.
Proof. vm_refl. Qed.
Lemma D_29f4c : decode_any W_29f4c = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

Definition W_29f50 : bv 32 := 0x160020ef.
Lemma F_29f50 : fetch_word Ubsan.M.loaded_segments (0x29f50 : word) = Some W_29f50.
Proof. vm_refl. Qed.
Lemma D_29f50 : decode_any W_29f50 = Some (Jal 1 8544, 4%Z).
Proof. vm_refl. Qed.

Definition W_29f54 : bv 32 := 0x00040513.
Lemma F_29f54 : fetch_word Ubsan.M.loaded_segments (0x29f54 : word) = Some W_29f54.
Proof. vm_refl. Qed.
Lemma D_29f54 : decode_any W_29f54 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_29f58 : bv 32 := 0xd91ff0ef.
Lemma F_29f58 : fetch_word Ubsan.M.loaded_segments (0x29f58 : word) = Some W_29f58.
Proof. vm_refl. Qed.
Lemma D_29f58 : decode_any W_29f58 = Some (Jal 1 2096528, 4%Z).
Proof. vm_refl. Qed.

Definition W_31924 : bv 32 := 0x00033597.
Lemma F_31924 : fetch_word Ubsan.M.loaded_segments (0x31924 : word) = Some W_31924.
Proof. vm_refl. Qed.
Lemma D_31924 : decode_any W_31924 = Some (Auipc 11 51, 4%Z).
Proof. vm_refl. Qed.

Definition W_31928 : bv 32 := 0xaa758683.
Lemma F_31928 : fetch_word Ubsan.M.loaded_segments (0x31928 : word) = Some W_31928.
Proof. vm_refl. Qed.
Lemma D_31928 : decode_any W_31928 = Some (Load SZ1 true 13 11 2727, 4%Z).
Proof. vm_refl. Qed.

Definition W_3192c : bv 32 := 0x1e068863.
Lemma F_3192c : fetch_word Ubsan.M.loaded_segments (0x3192c : word) = Some W_3192c.
Proof. vm_refl. Qed.
Lemma D_3192c : decode_any W_3192c = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

Definition W_31b1c : bv 32 := 0x00008067.
Lemma F_31b1c : fetch_word Ubsan.M.loaded_segments (0x31b1c : word) = Some W_31b1c.
Proof. vm_refl. Qed.
Lemma D_31b1c : decode_any W_31b1c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_31bac : bv 32 := 0x00052583.
Lemma F_31bac : fetch_word Ubsan.M.loaded_segments (0x31bac : word) = Some W_31bac.
Proof. vm_refl. Qed.
Lemma D_31bac : decode_any W_31bac = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_31bb0 : bv 32 := 0x0005c463.
Lemma F_31bb0 : fetch_word Ubsan.M.loaded_segments (0x31bb0 : word) = Some W_31bb0.
Proof. vm_refl. Qed.
Lemma D_31bb0 : decode_any W_31bb0 = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_31bb4 : bv 32 := 0x00008067.
Lemma F_31bb4 : fetch_word Ubsan.M.loaded_segments (0x31bb4 : word) = Some W_31bb4.
Proof. vm_refl. Qed.
Lemma D_31bb4 : decode_any W_31bb4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
