(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushU23.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_a6f20 : bv 32 := 0xf3010113.
Lemma F_a6f20 : fetch_word Ubsan.M.loaded_segments (0xa6f20 : word) = Some W_a6f20.
Proof. vm_refl. Qed.
Lemma D_a6f20 : decode_any W_a6f20 = Some (OpImm ALU_ADD 2 2 3888, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f24 : bv 32 := 0x0c113423.
Lemma F_a6f24 : fetch_word Ubsan.M.loaded_segments (0xa6f24 : word) = Some W_a6f24.
Proof. vm_refl. Qed.
Lemma D_a6f24 : decode_any W_a6f24 = Some (Store SZ8 2 1 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f28 : bv 32 := 0x0c813023.
Lemma F_a6f28 : fetch_word Ubsan.M.loaded_segments (0xa6f28 : word) = Some W_a6f28.
Proof. vm_refl. Qed.
Lemma D_a6f28 : decode_any W_a6f28 = Some (Store SZ8 2 8 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f2c : bv 32 := 0x0a913c23.
Lemma F_a6f2c : fetch_word Ubsan.M.loaded_segments (0xa6f2c : word) = Some W_a6f2c.
Proof. vm_refl. Qed.
Lemma D_a6f2c : decode_any W_a6f2c = Some (Store SZ8 2 9 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f30 : bv 32 := 0x0b213823.
Lemma F_a6f30 : fetch_word Ubsan.M.loaded_segments (0xa6f30 : word) = Some W_a6f30.
Proof. vm_refl. Qed.
Lemma D_a6f30 : decode_any W_a6f30 = Some (Store SZ8 2 18 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f34 : bv 32 := 0x0b313423.
Lemma F_a6f34 : fetch_word Ubsan.M.loaded_segments (0xa6f34 : word) = Some W_a6f34.
Proof. vm_refl. Qed.
Lemma D_a6f34 : decode_any W_a6f34 = Some (Store SZ8 2 19 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f38 : bv 32 := 0x0b413023.
Lemma F_a6f38 : fetch_word Ubsan.M.loaded_segments (0xa6f38 : word) = Some W_a6f38.
Proof. vm_refl. Qed.
Lemma D_a6f38 : decode_any W_a6f38 = Some (Store SZ8 2 20 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f3c : bv 32 := 0x09513c23.
Lemma F_a6f3c : fetch_word Ubsan.M.loaded_segments (0xa6f3c : word) = Some W_a6f3c.
Proof. vm_refl. Qed.
Lemma D_a6f3c : decode_any W_a6f3c = Some (Store SZ8 2 21 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f40 : bv 32 := 0x09613823.
Lemma F_a6f40 : fetch_word Ubsan.M.loaded_segments (0xa6f40 : word) = Some W_a6f40.
Proof. vm_refl. Qed.
Lemma D_a6f40 : decode_any W_a6f40 = Some (Store SZ8 2 22 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f44 : bv 32 := 0x09713423.
Lemma F_a6f44 : fetch_word Ubsan.M.loaded_segments (0xa6f44 : word) = Some W_a6f44.
Proof. vm_refl. Qed.
Lemma D_a6f44 : decode_any W_a6f44 = Some (Store SZ8 2 23 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f48 : bv 32 := 0x09813023.
Lemma F_a6f48 : fetch_word Ubsan.M.loaded_segments (0xa6f48 : word) = Some W_a6f48.
Proof. vm_refl. Qed.
Lemma D_a6f48 : decode_any W_a6f48 = Some (Store SZ8 2 24 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f4c : bv 32 := 0x07913c23.
Lemma F_a6f4c : fetch_word Ubsan.M.loaded_segments (0xa6f4c : word) = Some W_a6f4c.
Proof. vm_refl. Qed.
Lemma D_a6f4c : decode_any W_a6f4c = Some (Store SZ8 2 25 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f50 : bv 32 := 0x07a13823.
Lemma F_a6f50 : fetch_word Ubsan.M.loaded_segments (0xa6f50 : word) = Some W_a6f50.
Proof. vm_refl. Qed.
Lemma D_a6f50 : decode_any W_a6f50 = Some (Store SZ8 2 26 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f54 : bv 32 := 0x07b13423.
Lemma F_a6f54 : fetch_word Ubsan.M.loaded_segments (0xa6f54 : word) = Some W_a6f54.
Proof. vm_refl. Qed.
Lemma D_a6f54 : decode_any W_a6f54 = Some (Store SZ8 2 27 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f58 : bv 32 := 0x04050863.
Lemma F_a6f58 : fetch_word Ubsan.M.loaded_segments (0xa6f58 : word) = Some W_a6f58.
Proof. vm_refl. Qed.
Lemma D_a6f58 : decode_any W_a6f58 = Some (Branch BC_EQ 10 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f5c : bv 32 := 0x00058a13.
Lemma F_a6f5c : fetch_word Ubsan.M.loaded_segments (0xa6f5c : word) = Some W_a6f5c.
Proof. vm_refl. Qed.
Lemma D_a6f5c : decode_any W_a6f5c = Some (OpImm ALU_ADD 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f60 : bv 32 := 0x00050913.
Lemma F_a6f60 : fetch_word Ubsan.M.loaded_segments (0xa6f60 : word) = Some W_a6f60.
Proof. vm_refl. Qed.
Lemma D_a6f60 : decode_any W_a6f60 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f64 : bv 32 := 0x00060a93.
Lemma F_a6f64 : fetch_word Ubsan.M.loaded_segments (0xa6f64 : word) = Some W_a6f64.
Proof. vm_refl. Qed.
Lemma D_a6f64 : decode_any W_a6f64 = Some (OpImm ALU_ADD 21 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f68 : bv 32 := 0x9acc80ef.
Lemma F_a6f68 : fetch_word Ubsan.M.loaded_segments (0xa6f68 : word) = Some W_a6f68.
Proof. vm_refl. Qed.
Lemma D_a6f68 : decode_any W_a6f68 = Some (Jal 1 1868204, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f6c : bv 32 := 0x00100593.
Lemma F_a6f6c : fetch_word Ubsan.M.loaded_segments (0xa6f6c : word) = Some W_a6f6c.
Proof. vm_refl. Qed.
Lemma D_a6f6c : decode_any W_a6f6c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f70 : bv 32 := 0x06b51063.
Lemma F_a6f70 : fetch_word Ubsan.M.loaded_segments (0xa6f70 : word) = Some W_a6f70.
Proof. vm_refl. Qed.
Lemma D_a6f70 : decode_any W_a6f70 = Some (Branch BC_NE 10 11 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f74 : bv 32 := 0xffba051b.
Lemma F_a6f74 : fetch_word Ubsan.M.loaded_segments (0xa6f74 : word) = Some W_a6f74.
Proof. vm_refl. Qed.
Lemma D_a6f74 : decode_any W_a6f74 = Some (OpImm32 10 20 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f78 : bv 32 := 0xffb00593.
Lemma F_a6f78 : fetch_word Ubsan.M.loaded_segments (0xa6f78 : word) = Some W_a6f78.
Proof. vm_refl. Qed.
Lemma D_a6f78 : decode_any W_a6f78 = Some (OpImm ALU_ADD 11 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f7c : bv 32 := 0x0aa5ec63.
Lemma F_a6f7c : fetch_word Ubsan.M.loaded_segments (0xa6f7c : word) = Some W_a6f7c.
Proof. vm_refl. Qed.
Lemma D_a6f7c : decode_any W_a6f7c = Some (Branch BC_LTU 11 10 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f80 : bv 32 := 0x00080517.
Lemma F_a6f80 : fetch_word Ubsan.M.loaded_segments (0xa6f80 : word) = Some W_a6f80.
Proof. vm_refl. Qed.
Lemma D_a6f80 : decode_any W_a6f80 = Some (Auipc 10 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f84 : bv 32 := 0xaf053503.
Lemma F_a6f84 : fetch_word Ubsan.M.loaded_segments (0xa6f84 : word) = Some W_a6f84.
Proof. vm_refl. Qed.
Lemma D_a6f84 : decode_any W_a6f84 = Some (Load SZ8 true 10 10 2800, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f88 : bv 32 := 0x00052503.
Lemma F_a6f88 : fetch_word Ubsan.M.loaded_segments (0xa6f88 : word) = Some W_a6f88.
Proof. vm_refl. Qed.
Lemma D_a6f88 : decode_any W_a6f88 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f8c : bv 32 := 0x00500593.
Lemma F_a6f8c : fetch_word Ubsan.M.loaded_segments (0xa6f8c : word) = Some W_a6f8c.
Proof. vm_refl. Qed.
Lemma D_a6f8c : decode_any W_a6f8c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f90 : bv 32 := 0x2ca5cae3.
Lemma F_a6f90 : fetch_word Ubsan.M.loaded_segments (0xa6f90 : word) = Some W_a6f90.
Proof. vm_refl. Qed.
Lemma D_a6f90 : decode_any W_a6f90 = Some (Branch BC_LT 11 10 2772, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f94 : bv 32 := 0xfff75517.
Lemma F_a6f94 : fetch_word Ubsan.M.loaded_segments (0xa6f94 : word) = Some W_a6f94.
Proof. vm_refl. Qed.
Lemma D_a6f94 : decode_any W_a6f94 = Some (Auipc 10 1048437, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f98 : bv 32 := 0xfff6f597.
Lemma F_a6f98 : fetch_word Ubsan.M.loaded_segments (0xa6f98 : word) = Some W_a6f98.
Proof. vm_refl. Qed.
Lemma D_a6f98 : decode_any W_a6f98 = Some (Auipc 11 1048431, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f9c : bv 32 := 0xcd050513.
Lemma F_a6f9c : fetch_word Ubsan.M.loaded_segments (0xa6f9c : word) = Some W_a6f9c.
Proof. vm_refl. Qed.
Lemma D_a6f9c : decode_any W_a6f9c = Some (OpImm ALU_ADD 10 10 3280, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6fa0 : bv 32 := 0x3ee58593.
Lemma F_a6fa0 : fetch_word Ubsan.M.loaded_segments (0xa6fa0 : word) = Some W_a6fa0.
Proof. vm_refl. Qed.
Lemma D_a6fa0 : decode_any W_a6fa0 = Some (OpImm ALU_ADD 11 11 1006, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6fa4 : bv 32 := 0x0500006f.
Lemma F_a6fa4 : fetch_word Ubsan.M.loaded_segments (0xa6fa4 : word) = Some W_a6fa4.
Proof. vm_refl. Qed.
Lemma D_a6fa4 : decode_any W_a6fa4 = Some (Jal 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6fa8 : bv 32 := 0x00080517.
Lemma F_a6fa8 : fetch_word Ubsan.M.loaded_segments (0xa6fa8 : word) = Some W_a6fa8.
Proof. vm_refl. Qed.
Lemma D_a6fa8 : decode_any W_a6fa8 = Some (Auipc 10 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6fac : bv 32 := 0xac853503.
Lemma F_a6fac : fetch_word Ubsan.M.loaded_segments (0xa6fac : word) = Some W_a6fac.
Proof. vm_refl. Qed.
Lemma D_a6fac : decode_any W_a6fac = Some (Load SZ8 true 10 10 2760, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6fb0 : bv 32 := 0x00052503.
Lemma F_a6fb0 : fetch_word Ubsan.M.loaded_segments (0xa6fb0 : word) = Some W_a6fb0.
Proof. vm_refl. Qed.
Lemma D_a6fb0 : decode_any W_a6fb0 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6fb4 : bv 32 := 0x00500593.
Lemma F_a6fb4 : fetch_word Ubsan.M.loaded_segments (0xa6fb4 : word) = Some W_a6fb4.
Proof. vm_refl. Qed.
Lemma D_a6fb4 : decode_any W_a6fb4 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6fb8 : bv 32 := 0x2aa5c6e3.
Lemma F_a6fb8 : fetch_word Ubsan.M.loaded_segments (0xa6fb8 : word) = Some W_a6fb8.
Proof. vm_refl. Qed.
Lemma D_a6fb8 : decode_any W_a6fb8 = Some (Branch BC_LT 11 10 2732, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6fbc : bv 32 := 0xfff69517.
Lemma F_a6fbc : fetch_word Ubsan.M.loaded_segments (0xa6fbc : word) = Some W_a6fbc.
Proof. vm_refl. Qed.
Lemma D_a6fbc : decode_any W_a6fbc = Some (Auipc 10 1048425, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6fc0 : bv 32 := 0xfff6f597.
Lemma F_a6fc0 : fetch_word Ubsan.M.loaded_segments (0xa6fc0 : word) = Some W_a6fc0.
Proof. vm_refl. Qed.
Lemma D_a6fc0 : decode_any W_a6fc0 = Some (Auipc 11 1048431, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6fc4 : bv 32 := 0x39950513.
Lemma F_a6fc4 : fetch_word Ubsan.M.loaded_segments (0xa6fc4 : word) = Some W_a6fc4.
Proof. vm_refl. Qed.
Lemma D_a6fc4 : decode_any W_a6fc4 = Some (OpImm ALU_ADD 10 10 921, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6fc8 : bv 32 := 0x3c658593.
Lemma F_a6fc8 : fetch_word Ubsan.M.loaded_segments (0xa6fc8 : word) = Some W_a6fc8.
Proof. vm_refl. Qed.
Lemma D_a6fc8 : decode_any W_a6fc8 = Some (OpImm ALU_ADD 11 11 966, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6fcc : bv 32 := 0x0280006f.
Lemma F_a6fcc : fetch_word Ubsan.M.loaded_segments (0xa6fcc : word) = Some W_a6fcc.
Proof. vm_refl. Qed.
Lemma D_a6fcc : decode_any W_a6fcc = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6fd0 : bv 32 := 0x00080517.
Lemma F_a6fd0 : fetch_word Ubsan.M.loaded_segments (0xa6fd0 : word) = Some W_a6fd0.
Proof. vm_refl. Qed.
Lemma D_a6fd0 : decode_any W_a6fd0 = Some (Auipc 10 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6fd4 : bv 32 := 0xaa053503.
Lemma F_a6fd4 : fetch_word Ubsan.M.loaded_segments (0xa6fd4 : word) = Some W_a6fd4.
Proof. vm_refl. Qed.
Lemma D_a6fd4 : decode_any W_a6fd4 = Some (Load SZ8 true 10 10 2720, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6fd8 : bv 32 := 0x00052503.
Lemma F_a6fd8 : fetch_word Ubsan.M.loaded_segments (0xa6fd8 : word) = Some W_a6fd8.
Proof. vm_refl. Qed.
Lemma D_a6fd8 : decode_any W_a6fd8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6fdc : bv 32 := 0x00500593.
Lemma F_a6fdc : fetch_word Ubsan.M.loaded_segments (0xa6fdc : word) = Some W_a6fdc.
Proof. vm_refl. Qed.
Lemma D_a6fdc : decode_any W_a6fdc = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6fe0 : bv 32 := 0x28a5c2e3.
Lemma F_a6fe0 : fetch_word Ubsan.M.loaded_segments (0xa6fe0 : word) = Some W_a6fe0.
Proof. vm_refl. Qed.
Lemma D_a6fe0 : decode_any W_a6fe0 = Some (Branch BC_LT 11 10 2692, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6fe4 : bv 32 := 0xfff76517.
Lemma F_a6fe4 : fetch_word Ubsan.M.loaded_segments (0xa6fe4 : word) = Some W_a6fe4.
Proof. vm_refl. Qed.
Lemma D_a6fe4 : decode_any W_a6fe4 = Some (Auipc 10 1048438, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6fe8 : bv 32 := 0xfff6f597.
Lemma F_a6fe8 : fetch_word Ubsan.M.loaded_segments (0xa6fe8 : word) = Some W_a6fe8.
Proof. vm_refl. Qed.
Lemma D_a6fe8 : decode_any W_a6fe8 = Some (Auipc 11 1048431, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6fec : bv 32 := 0x98650513.
Lemma F_a6fec : fetch_word Ubsan.M.loaded_segments (0xa6fec : word) = Some W_a6fec.
Proof. vm_refl. Qed.
Lemma D_a6fec : decode_any W_a6fec = Some (OpImm ALU_ADD 10 10 2438, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6ff0 : bv 32 := 0x39e58593.
Lemma F_a6ff0 : fetch_word Ubsan.M.loaded_segments (0xa6ff0 : word) = Some W_a6ff0.
Proof. vm_refl. Qed.
Lemma D_a6ff0 : decode_any W_a6ff0 = Some (OpImm ALU_ADD 11 11 926, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6ff4 : bv 32 := 0x00000613.
Lemma F_a6ff4 : fetch_word Ubsan.M.loaded_segments (0xa6ff4 : word) = Some W_a6ff4.
Proof. vm_refl. Qed.
Lemma D_a6ff4 : decode_any W_a6ff4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6ff8 : bv 32 := 0x0c813083.
Lemma F_a6ff8 : fetch_word Ubsan.M.loaded_segments (0xa6ff8 : word) = Some W_a6ff8.
Proof. vm_refl. Qed.
Lemma D_a6ff8 : decode_any W_a6ff8 = Some (Load SZ8 true 1 2 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6ffc : bv 32 := 0x0c013403.
Lemma F_a6ffc : fetch_word Ubsan.M.loaded_segments (0xa6ffc : word) = Some W_a6ffc.
Proof. vm_refl. Qed.
Lemma D_a6ffc : decode_any W_a6ffc = Some (Load SZ8 true 8 2 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7000 : bv 32 := 0x0b813483.
Lemma F_a7000 : fetch_word Ubsan.M.loaded_segments (0xa7000 : word) = Some W_a7000.
Proof. vm_refl. Qed.
Lemma D_a7000 : decode_any W_a7000 = Some (Load SZ8 true 9 2 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7004 : bv 32 := 0x0b013903.
Lemma F_a7004 : fetch_word Ubsan.M.loaded_segments (0xa7004 : word) = Some W_a7004.
Proof. vm_refl. Qed.
Lemma D_a7004 : decode_any W_a7004 = Some (Load SZ8 true 18 2 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7008 : bv 32 := 0x0a813983.
Lemma F_a7008 : fetch_word Ubsan.M.loaded_segments (0xa7008 : word) = Some W_a7008.
Proof. vm_refl. Qed.
Lemma D_a7008 : decode_any W_a7008 = Some (Load SZ8 true 19 2 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_a700c : bv 32 := 0x0a013a03.
Lemma F_a700c : fetch_word Ubsan.M.loaded_segments (0xa700c : word) = Some W_a700c.
Proof. vm_refl. Qed.
Lemma D_a700c : decode_any W_a700c = Some (Load SZ8 true 20 2 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7010 : bv 32 := 0x09813a83.
Lemma F_a7010 : fetch_word Ubsan.M.loaded_segments (0xa7010 : word) = Some W_a7010.
Proof. vm_refl. Qed.
Lemma D_a7010 : decode_any W_a7010 = Some (Load SZ8 true 21 2 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7014 : bv 32 := 0x09013b03.
Lemma F_a7014 : fetch_word Ubsan.M.loaded_segments (0xa7014 : word) = Some W_a7014.
Proof. vm_refl. Qed.
Lemma D_a7014 : decode_any W_a7014 = Some (Load SZ8 true 22 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7018 : bv 32 := 0x08813b83.
Lemma F_a7018 : fetch_word Ubsan.M.loaded_segments (0xa7018 : word) = Some W_a7018.
Proof. vm_refl. Qed.
Lemma D_a7018 : decode_any W_a7018 = Some (Load SZ8 true 23 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_a701c : bv 32 := 0x08013c03.
Lemma F_a701c : fetch_word Ubsan.M.loaded_segments (0xa701c : word) = Some W_a701c.
Proof. vm_refl. Qed.
Lemma D_a701c : decode_any W_a701c = Some (Load SZ8 true 24 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7020 : bv 32 := 0x07813c83.
Lemma F_a7020 : fetch_word Ubsan.M.loaded_segments (0xa7020 : word) = Some W_a7020.
Proof. vm_refl. Qed.
Lemma D_a7020 : decode_any W_a7020 = Some (Load SZ8 true 25 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7024 : bv 32 := 0x07013d03.
Lemma F_a7024 : fetch_word Ubsan.M.loaded_segments (0xa7024 : word) = Some W_a7024.
Proof. vm_refl. Qed.
Lemma D_a7024 : decode_any W_a7024 = Some (Load SZ8 true 26 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7028 : bv 32 := 0x06813d83.
Lemma F_a7028 : fetch_word Ubsan.M.loaded_segments (0xa7028 : word) = Some W_a7028.
Proof. vm_refl. Qed.
Lemma D_a7028 : decode_any W_a7028 = Some (Load SZ8 true 27 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_a702c : bv 32 := 0x0d010113.
Lemma F_a702c : fetch_word Ubsan.M.loaded_segments (0xa702c : word) = Some W_a702c.
Proof. vm_refl. Qed.
Lemma D_a702c : decode_any W_a702c = Some (OpImm ALU_ADD 2 2 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7030 : bv 32 := 0xf10bc06f.
Lemma F_a7030 : fetch_word Ubsan.M.loaded_segments (0xa7030 : word) = Some W_a7030.
Proof. vm_refl. Qed.
Lemma D_a7030 : decode_any W_a7030 = Some (Jal 0 1820432, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7034 : bv 32 := 0x06410593.
Lemma F_a7034 : fetch_word Ubsan.M.loaded_segments (0xa7034 : word) = Some W_a7034.
Proof. vm_refl. Qed.
Lemma D_a7034 : decode_any W_a7034 = Some (OpImm ALU_ADD 11 2 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7038 : bv 32 := 0x06010613.
Lemma F_a7038 : fetch_word Ubsan.M.loaded_segments (0xa7038 : word) = Some W_a7038.
Proof. vm_refl. Qed.
Lemma D_a7038 : decode_any W_a7038 = Some (OpImm ALU_ADD 12 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_a703c : bv 32 := 0x00090513.
Lemma F_a703c : fetch_word Ubsan.M.loaded_segments (0xa703c : word) = Some W_a703c.
Proof. vm_refl. Qed.
Lemma D_a703c : decode_any W_a703c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7040 : bv 32 := 0x00000693.
Lemma F_a7040 : fetch_word Ubsan.M.loaded_segments (0xa7040 : word) = Some W_a7040.
Proof. vm_refl. Qed.
Lemma D_a7040 : decode_any W_a7040 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7044 : bv 32 := 0xa60c70ef.
Lemma F_a7044 : fetch_word Ubsan.M.loaded_segments (0xa7044 : word) = Some W_a7044.
Proof. vm_refl. Qed.
Lemma D_a7044 : decode_any W_a7044 = Some (Jal 1 1864288, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7048 : bv 32 := 0x06012503.
Lemma F_a7048 : fetch_word Ubsan.M.loaded_segments (0xa7048 : word) = Some W_a7048.
Proof. vm_refl. Qed.
Lemma D_a7048 : decode_any W_a7048 = Some (Load SZ4 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_a704c : bv 32 := 0x00100593.
Lemma F_a704c : fetch_word Ubsan.M.loaded_segments (0xa704c : word) = Some W_a704c.
Proof. vm_refl. Qed.
Lemma D_a704c : decode_any W_a704c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7050 : bv 32 := 0x02a5c663.
Lemma F_a7050 : fetch_word Ubsan.M.loaded_segments (0xa7050 : word) = Some W_a7050.
Proof. vm_refl. Qed.
Lemma D_a7050 : decode_any W_a7050 = Some (Branch BC_LT 11 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7054 : bv 32 := 0x00080517.
Lemma F_a7054 : fetch_word Ubsan.M.loaded_segments (0xa7054 : word) = Some W_a7054.
Proof. vm_refl. Qed.
Lemma D_a7054 : decode_any W_a7054 = Some (Auipc 10 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7058 : bv 32 := 0xa1c53503.
Lemma F_a7058 : fetch_word Ubsan.M.loaded_segments (0xa7058 : word) = Some W_a7058.
Proof. vm_refl. Qed.
Lemma D_a7058 : decode_any W_a7058 = Some (Load SZ8 true 10 10 2588, 4%Z).
Proof. vm_refl. Qed.

Definition W_a705c : bv 32 := 0x00052503.
Lemma F_a705c : fetch_word Ubsan.M.loaded_segments (0xa705c : word) = Some W_a705c.
Proof. vm_refl. Qed.
Lemma D_a705c : decode_any W_a705c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7060 : bv 32 := 0x00500593.
Lemma F_a7060 : fetch_word Ubsan.M.loaded_segments (0xa7060 : word) = Some W_a7060.
Proof. vm_refl. Qed.
Lemma D_a7060 : decode_any W_a7060 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7064 : bv 32 := 0x20a5c0e3.
Lemma F_a7064 : fetch_word Ubsan.M.loaded_segments (0xa7064 : word) = Some W_a7064.
Proof. vm_refl. Qed.
Lemma D_a7064 : decode_any W_a7064 = Some (Branch BC_LT 11 10 2560, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7068 : bv 32 := 0xfff6f517.
Lemma F_a7068 : fetch_word Ubsan.M.loaded_segments (0xa7068 : word) = Some W_a7068.
Proof. vm_refl. Qed.
Lemma D_a7068 : decode_any W_a7068 = Some (Auipc 10 1048431, 4%Z).
Proof. vm_refl. Qed.

Definition W_a706c : bv 32 := 0xfff6f597.
Lemma F_a706c : fetch_word Ubsan.M.loaded_segments (0xa706c : word) = Some W_a706c.
Proof. vm_refl. Qed.
Lemma D_a706c : decode_any W_a706c = Some (Auipc 11 1048431, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7070 : bv 32 := 0x30850513.
Lemma F_a7070 : fetch_word Ubsan.M.loaded_segments (0xa7070 : word) = Some W_a7070.
Proof. vm_refl. Qed.
Lemma D_a7070 : decode_any W_a7070 = Some (OpImm ALU_ADD 10 10 776, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7074 : bv 32 := 0x31a58593.
Lemma F_a7074 : fetch_word Ubsan.M.loaded_segments (0xa7074 : word) = Some W_a7074.
Proof. vm_refl. Qed.
Lemma D_a7074 : decode_any W_a7074 = Some (OpImm ALU_ADD 11 11 794, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7078 : bv 32 := 0x3340006f.
Lemma F_a7078 : fetch_word Ubsan.M.loaded_segments (0xa7078 : word) = Some W_a7078.
Proof. vm_refl. Qed.
Lemma D_a7078 : decode_any W_a7078 = Some (Jal 0 820, 4%Z).
Proof. vm_refl. Qed.

Definition W_a707c : bv 32 := 0x00090513.
Lemma F_a707c : fetch_word Ubsan.M.loaded_segments (0xa707c : word) = Some W_a707c.
Proof. vm_refl. Qed.
Lemma D_a707c : decode_any W_a707c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7080 : bv 32 := 0xecdc60ef.
Lemma F_a7080 : fetch_word Ubsan.M.loaded_segments (0xa7080 : word) = Some W_a7080.
Proof. vm_refl. Qed.
Lemma D_a7080 : decode_any W_a7080 = Some (Jal 1 1863372, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7084 : bv 32 := 0x04a13423.
Lemma F_a7084 : fetch_word Ubsan.M.loaded_segments (0xa7084 : word) = Some W_a7084.
Proof. vm_refl. Qed.
Lemma D_a7084 : decode_any W_a7084 = Some (Store SZ8 2 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7088 : bv 32 := 0x00090513.
Lemma F_a7088 : fetch_word Ubsan.M.loaded_segments (0xa7088 : word) = Some W_a7088.
Proof. vm_refl. Qed.
Lemma D_a7088 : decode_any W_a7088 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a708c : bv 32 := 0x960c80ef.
Lemma F_a708c : fetch_word Ubsan.M.loaded_segments (0xa708c : word) = Some W_a708c.
Proof. vm_refl. Qed.
Lemma D_a708c : decode_any W_a708c = Some (Jal 1 1868128, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7090 : bv 32 := 0x04a13823.
Lemma F_a7090 : fetch_word Ubsan.M.loaded_segments (0xa7090 : word) = Some W_a7090.
Proof. vm_refl. Qed.
Lemma D_a7090 : decode_any W_a7090 = Some (Store SZ8 2 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7094 : bv 32 := 0x00090513.
Lemma F_a7094 : fetch_word Ubsan.M.loaded_segments (0xa7094 : word) = Some W_a7094.
Proof. vm_refl. Qed.
Lemma D_a7094 : decode_any W_a7094 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7098 : bv 32 := 0x00000593.
Lemma F_a7098 : fetch_word Ubsan.M.loaded_segments (0xa7098 : word) = Some W_a7098.
Proof. vm_refl. Qed.
Lemma D_a7098 : decode_any W_a7098 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a709c : bv 32 := 0x9b9c90ef.
Lemma F_a709c : fetch_word Ubsan.M.loaded_segments (0xa709c : word) = Some W_a709c.
Proof. vm_refl. Qed.
Lemma D_a709c : decode_any W_a709c = Some (Jal 1 1874360, 4%Z).
Proof. vm_refl. Qed.

Definition W_a70a0 : bv 32 := 0x06412503.
Lemma F_a70a0 : fetch_word Ubsan.M.loaded_segments (0xa70a0 : word) = Some W_a70a0.
Proof. vm_refl. Qed.
Lemma D_a70a0 : decode_any W_a70a0 = Some (Load SZ4 true 10 2 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_a70a4 : bv 32 := 0x06012583.
Lemma F_a70a4 : fetch_word Ubsan.M.loaded_segments (0xa70a4 : word) = Some W_a70a4.
Proof. vm_refl. Qed.
Lemma D_a70a4 : decode_any W_a70a4 = Some (Load SZ4 true 11 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_a70a8 : bv 32 := 0x01f5561b.
Lemma F_a70a8 : fetch_word Ubsan.M.loaded_segments (0xa70a8 : word) = Some W_a70a8.
Proof. vm_refl. Qed.
Lemma D_a70a8 : decode_any W_a70a8 = Some (ShiftImm32 ALU_SRL 12 10 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_a70ac : bv 32 := 0x00c50533.
Lemma F_a70ac : fetch_word Ubsan.M.loaded_segments (0xa70ac : word) = Some W_a70ac.
Proof. vm_refl. Qed.
Lemma D_a70ac : decode_any W_a70ac = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a70b0 : bv 32 := 0x01f5d61b.
Lemma F_a70b0 : fetch_word Ubsan.M.loaded_segments (0xa70b0 : word) = Some W_a70b0.
Proof. vm_refl. Qed.
Lemma D_a70b0 : decode_any W_a70b0 = Some (ShiftImm32 ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_a70b4 : bv 32 := 0x00c585b3.
Lemma F_a70b4 : fetch_word Ubsan.M.loaded_segments (0xa70b4 : word) = Some W_a70b4.
Proof. vm_refl. Qed.
Lemma D_a70b4 : decode_any W_a70b4 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a70b8 : bv 32 := 0x4015551b.
Lemma F_a70b8 : fetch_word Ubsan.M.loaded_segments (0xa70b8 : word) = Some W_a70b8.
Proof. vm_refl. Qed.
Lemma D_a70b8 : decode_any W_a70b8 = Some (ShiftImm32 ALU_SRA 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a70bc : bv 32 := 0x4015d59b.
Lemma F_a70bc : fetch_word Ubsan.M.loaded_segments (0xa70bc : word) = Some W_a70bc.
Proof. vm_refl. Qed.
Lemma D_a70bc : decode_any W_a70bc = Some (ShiftImm32 ALU_SRA 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a70c0 : bv 32 := 0x00100613.
Lemma F_a70c0 : fetch_word Ubsan.M.loaded_segments (0xa70c0 : word) = Some W_a70c0.
Proof. vm_refl. Qed.
Lemma D_a70c0 : decode_any W_a70c0 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a70c4 : bv 32 := 0x979c60ef.
Lemma F_a70c4 : fetch_word Ubsan.M.loaded_segments (0xa70c4 : word) = Some W_a70c4.
Proof. vm_refl. Qed.
Lemma D_a70c4 : decode_any W_a70c4 = Some (Jal 1 1862008, 4%Z).
Proof. vm_refl. Qed.

Definition W_a70c8 : bv 32 := 0x04a13c23.
Lemma F_a70c8 : fetch_word Ubsan.M.loaded_segments (0xa70c8 : word) = Some W_a70c8.
Proof. vm_refl. Qed.
Lemma D_a70c8 : decode_any W_a70c8 = Some (Store SZ8 2 10 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_a70cc : bv 32 := 0x2a050e63.
Lemma F_a70cc : fetch_word Ubsan.M.loaded_segments (0xa70cc : word) = Some W_a70cc.
Proof. vm_refl. Qed.
Lemma D_a70cc : decode_any W_a70cc = Some (Branch BC_EQ 10 0 700, 4%Z).
Proof. vm_refl. Qed.

Definition W_a70d0 : bv 32 := 0x00050993.
Lemma F_a70d0 : fetch_word Ubsan.M.loaded_segments (0xa70d0 : word) = Some W_a70d0.
Proof. vm_refl. Qed.
Lemma D_a70d0 : decode_any W_a70d0 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a70d4 : bv 32 := 0x00090593.
Lemma F_a70d4 : fetch_word Ubsan.M.loaded_segments (0xa70d4 : word) = Some W_a70d4.
Proof. vm_refl. Qed.
Lemma D_a70d4 : decode_any W_a70d4 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a70d8 : bv 32 := 0xb64c70ef.
Lemma F_a70d8 : fetch_word Ubsan.M.loaded_segments (0xa70d8 : word) = Some W_a70d8.
Proof. vm_refl. Qed.
Lemma D_a70d8 : decode_any W_a70d8 = Some (Jal 1 1864548, 4%Z).
Proof. vm_refl. Qed.

Definition W_a70dc : bv 32 := 0x3f000537.
Lemma F_a70dc : fetch_word Ubsan.M.loaded_segments (0xa70dc : word) = Some W_a70dc.
Proof. vm_refl. Qed.
Lemma D_a70dc : decode_any W_a70dc = Some (Lui 10 258048, 4%Z).
Proof. vm_refl. Qed.

Definition W_a70e0 : bv 32 := 0xf0050553.
Lemma F_a70e0 : fetch_word Ubsan.M.loaded_segments (0xa70e0 : word) = Some W_a70e0.
Proof. vm_refl. Qed.
Lemma D_a70e0 : decode_any W_a70e0 = Some (Fmv FMV_F_X FMT_S 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a70e4 : bv 32 := 0x00098513.
Lemma F_a70e4 : fetch_word Ubsan.M.loaded_segments (0xa70e4 : word) = Some W_a70e4.
Proof. vm_refl. Qed.
Lemma D_a70e4 : decode_any W_a70e4 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a70e8 : bv 32 := 0x20a505d3.
Lemma F_a70e8 : fetch_word Ubsan.M.loaded_segments (0xa70e8 : word) = Some W_a70e8.
Proof. vm_refl. Qed.
Lemma D_a70e8 : decode_any W_a70e8 = Some (Fsgnj F_SGNJ FMT_S 11 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a70ec : bv 32 := 0xe5cc80ef.
Lemma F_a70ec : fetch_word Ubsan.M.loaded_segments (0xa70ec : word) = Some W_a70ec.
Proof. vm_refl. Qed.
Lemma D_a70ec : decode_any W_a70ec = Some (Jal 1 1869404, 4%Z).
Proof. vm_refl. Qed.

Definition W_a70f0 : bv 32 := 0x00098513.
Lemma F_a70f0 : fetch_word Ubsan.M.loaded_segments (0xa70f0 : word) = Some W_a70f0.
Proof. vm_refl. Qed.
Lemma D_a70f0 : decode_any W_a70f0 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a70f4 : bv 32 := 0xe59c60ef.
Lemma F_a70f4 : fetch_word Ubsan.M.loaded_segments (0xa70f4 : word) = Some W_a70f4.
Proof. vm_refl. Qed.
Lemma D_a70f4 : decode_any W_a70f4 = Some (Jal 1 1863256, 4%Z).
Proof. vm_refl. Qed.

Definition W_a70f8 : bv 32 := 0x00050413.
Lemma F_a70f8 : fetch_word Ubsan.M.loaded_segments (0xa70f8 : word) = Some W_a70f8.
Proof. vm_refl. Qed.
Lemma D_a70f8 : decode_any W_a70f8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a70fc : bv 32 := 0x01313423.
Lemma F_a70fc : fetch_word Ubsan.M.loaded_segments (0xa70fc : word) = Some W_a70fc.
Proof. vm_refl. Qed.
Lemma D_a70fc : decode_any W_a70fc = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7100 : bv 32 := 0x00098513.
Lemma F_a7100 : fetch_word Ubsan.M.loaded_segments (0xa7100 : word) = Some W_a7100.
Proof. vm_refl. Qed.
Lemma D_a7100 : decode_any W_a7100 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7104 : bv 32 := 0x8e8c80ef.
Lemma F_a7104 : fetch_word Ubsan.M.loaded_segments (0xa7104 : word) = Some W_a7104.
Proof. vm_refl. Qed.
Lemma D_a7104 : decode_any W_a7104 = Some (Jal 1 1868008, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7108 : bv 32 := 0x00050913.
Lemma F_a7108 : fetch_word Ubsan.M.loaded_segments (0xa7108 : word) = Some W_a7108.
Proof. vm_refl. Qed.
Lemma D_a7108 : decode_any W_a7108 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a710c : bv 32 := 0x000a8613.
Lemma F_a710c : fetch_word Ubsan.M.loaded_segments (0xa710c : word) = Some W_a710c.
Proof. vm_refl. Qed.
Lemma D_a710c : decode_any W_a710c = Some (OpImm ALU_ADD 12 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7110 : bv 32 := 0x000a8593.
Lemma F_a7110 : fetch_word Ubsan.M.loaded_segments (0xa7110 : word) = Some W_a7110.
Proof. vm_refl. Qed.
Lemma D_a7110 : decode_any W_a7110 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7114 : bv 32 := 0x000a9a63.
Lemma F_a7114 : fetch_word Ubsan.M.loaded_segments (0xa7114 : word) = Some W_a7114.
Proof. vm_refl. Qed.
Lemma D_a7114 : decode_any W_a7114 = Some (Branch BC_NE 21 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7118 : bv 32 := 0xa5dff0ef.
Lemma F_a7118 : fetch_word Ubsan.M.loaded_segments (0xa7118 : word) = Some W_a7118.
Proof. vm_refl. Qed.
Lemma D_a7118 : decode_any W_a7118 = Some (Jal 1 2095708, 4%Z).
Proof. vm_refl. Qed.

Definition W_a711c : bv 32 := 0x000a8613.
Lemma F_a711c : fetch_word Ubsan.M.loaded_segments (0xa711c : word) = Some W_a711c.
Proof. vm_refl. Qed.
Lemma D_a711c : decode_any W_a711c = Some (OpImm ALU_ADD 12 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7120 : bv 32 := 0x00050593.
Lemma F_a7120 : fetch_word Ubsan.M.loaded_segments (0xa7120 : word) = Some W_a7120.
Proof. vm_refl. Qed.
Lemma D_a7120 : decode_any W_a7120 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7124 : bv 32 := 0x100508e3.
Lemma F_a7124 : fetch_word Ubsan.M.loaded_segments (0xa7124 : word) = Some W_a7124.
Proof. vm_refl. Qed.
Lemma D_a7124 : decode_any W_a7124 = Some (Branch BC_EQ 10 0 2320, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7128 : bv 32 := 0x00c13023.
Lemma F_a7128 : fetch_word Ubsan.M.loaded_segments (0xa7128 : word) = Some W_a7128.
Proof. vm_refl. Qed.
Lemma D_a7128 : decode_any W_a7128 = Some (Store SZ8 2 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a712c : bv 32 := 0x40000537.
Lemma F_a712c : fetch_word Ubsan.M.loaded_segments (0xa712c : word) = Some W_a712c.
Proof. vm_refl. Qed.
Lemma D_a712c : decode_any W_a712c = Some (Lui 10 262144, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7130 : bv 32 := 0x00a4063b.
Lemma F_a7130 : fetch_word Ubsan.M.loaded_segments (0xa7130 : word) = Some W_a7130.
Proof. vm_refl. Qed.
Lemma D_a7130 : decode_any W_a7130 = Some (Op32 ALU_ADD 12 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7134 : bv 32 := 0x160648e3.
Lemma F_a7134 : fetch_word Ubsan.M.loaded_segments (0xa7134 : word) = Some W_a7134.
Proof. vm_refl. Qed.
Lemma D_a7134 : decode_any W_a7134 = Some (Branch BC_LT 12 0 2416, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7138 : bv 32 := 0x0014161b.
Lemma F_a7138 : fetch_word Ubsan.M.loaded_segments (0xa7138 : word) = Some W_a7138.
Proof. vm_refl. Qed.
Lemma D_a7138 : decode_any W_a7138 = Some (ShiftImm32 ALU_SLL 12 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a713c : bv 32 := 0x04813683.
Lemma F_a713c : fetch_word Ubsan.M.loaded_segments (0xa713c : word) = Some W_a713c.
Proof. vm_refl. Qed.
Lemma D_a713c : decode_any W_a713c = Some (Load SZ8 true 13 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7140 : bv 32 := 0x04d13023.
Lemma F_a7140 : fetch_word Ubsan.M.loaded_segments (0xa7140 : word) = Some W_a7140.
Proof. vm_refl. Qed.
Lemma D_a7140 : decode_any W_a7140 = Some (Store SZ8 2 13 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7144 : bv 32 := 0x00c6c463.
Lemma F_a7144 : fetch_word Ubsan.M.loaded_segments (0xa7144 : word) = Some W_a7144.
Proof. vm_refl. Qed.
Lemma D_a7144 : decode_any W_a7144 = Some (Branch BC_LT 13 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7148 : bv 32 := 0x04c13023.
Lemma F_a7148 : fetch_word Ubsan.M.loaded_segments (0xa7148 : word) = Some W_a7148.
Proof. vm_refl. Qed.
Lemma D_a7148 : decode_any W_a7148 = Some (Store SZ8 2 12 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a714c : bv 32 := 0x06012603.
Lemma F_a714c : fetch_word Ubsan.M.loaded_segments (0xa714c : word) = Some W_a714c.
Proof. vm_refl. Qed.
Lemma D_a714c : decode_any W_a714c = Some (Load SZ4 true 12 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7150 : bv 32 := 0xfff6051b.
Lemma F_a7150 : fetch_word Ubsan.M.loaded_segments (0xa7150 : word) = Some W_a7150.
Proof. vm_refl. Qed.
Lemma D_a7150 : decode_any W_a7150 = Some (OpImm32 10 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7154 : bv 32 := 0x02a13c23.
Lemma F_a7154 : fetch_word Ubsan.M.loaded_segments (0xa7154 : word) = Some W_a7154.
Proof. vm_refl. Qed.
Lemma D_a7154 : decode_any W_a7154 = Some (Store SZ8 2 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7158 : bv 32 := 0x00c52633.
Lemma F_a7158 : fetch_word Ubsan.M.loaded_segments (0xa7158 : word) = Some W_a7158.
Proof. vm_refl. Qed.
Lemma D_a7158 : decode_any W_a7158 = Some (Op ALU_SLT 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a715c : bv 32 := 0x00200693.
Lemma F_a715c : fetch_word Ubsan.M.loaded_segments (0xa715c : word) = Some W_a715c.
Proof. vm_refl. Qed.
Lemma D_a715c : decode_any W_a715c = Some (OpImm ALU_ADD 13 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7160 : bv 32 := 0x00164613.
Lemma F_a7160 : fetch_word Ubsan.M.loaded_segments (0xa7160 : word) = Some W_a7160.
Proof. vm_refl. Qed.
Lemma D_a7160 : decode_any W_a7160 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7164 : bv 32 := 0x00040513.
Lemma F_a7164 : fetch_word Ubsan.M.loaded_segments (0xa7164 : word) = Some W_a7164.
Proof. vm_refl. Qed.
Lemma D_a7164 : decode_any W_a7164 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7168 : bv 32 := 0x2546c863.
Lemma F_a7168 : fetch_word Ubsan.M.loaded_segments (0xa7168 : word) = Some W_a7168.
Proof. vm_refl. Qed.
Lemma D_a7168 : decode_any W_a7168 = Some (Branch BC_LT 13 20 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_a716c : bv 32 := 0x00100693.
Lemma F_a716c : fetch_word Ubsan.M.loaded_segments (0xa716c : word) = Some W_a716c.
Proof. vm_refl. Qed.
Lemma D_a716c : decode_any W_a716c = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7170 : bv 32 := 0x46da1c63.
Lemma F_a7170 : fetch_word Ubsan.M.loaded_segments (0xa7170 : word) = Some W_a7170.
Proof. vm_refl. Qed.
Lemma D_a7170 : decode_any W_a7170 = Some (Branch BC_NE 20 13 1144, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7174 : bv 32 := 0x120618e3.
Lemma F_a7174 : fetch_word Ubsan.M.loaded_segments (0xa7174 : word) = Some W_a7174.
Proof. vm_refl. Qed.
Lemma D_a7174 : decode_any W_a7174 = Some (Branch BC_NE 12 0 2352, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7178 : bv 32 := 0x03813603.
Lemma F_a7178 : fetch_word Ubsan.M.loaded_segments (0xa7178 : word) = Some W_a7178.
Proof. vm_refl. Qed.
Lemma D_a7178 : decode_any W_a7178 = Some (Load SZ8 true 12 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a717c : bv 32 := 0x0ac050e3.
Lemma F_a717c : fetch_word Ubsan.M.loaded_segments (0xa717c : word) = Some W_a717c.
Proof. vm_refl. Qed.
Lemma D_a717c : decode_any W_a717c = Some (Branch BC_GE 0 12 2208, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7180 : bv 32 := 0x00000793.
Lemma F_a7180 : fetch_word Ubsan.M.loaded_segments (0xa7180 : word) = Some W_a7180.
Proof. vm_refl. Qed.
Lemma D_a7180 : decode_any W_a7180 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7184 : bv 32 := 0x00000813.
Lemma F_a7184 : fetch_word Ubsan.M.loaded_segments (0xa7184 : word) = Some W_a7184.
Proof. vm_refl. Qed.
Lemma D_a7184 : decode_any W_a7184 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7188 : bv 32 := 0x00000893.
Lemma F_a7188 : fetch_word Ubsan.M.loaded_segments (0xa7188 : word) = Some W_a7188.
Proof. vm_refl. Qed.
Lemma D_a7188 : decode_any W_a7188 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a718c : bv 32 := 0x00000293.
Lemma F_a718c : fetch_word Ubsan.M.loaded_segments (0xa718c : word) = Some W_a718c.
Proof. vm_refl. Qed.
Lemma D_a718c : decode_any W_a718c = Some (OpImm ALU_ADD 5 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7190 : bv 32 := 0x04813703.
Lemma F_a7190 : fetch_word Ubsan.M.loaded_segments (0xa7190 : word) = Some W_a7190.
Proof. vm_refl. Qed.
Lemma D_a7190 : decode_any W_a7190 = Some (Load SZ8 true 14 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7194 : bv 32 := 0x00271613.
Lemma F_a7194 : fetch_word Ubsan.M.loaded_segments (0xa7194 : word) = Some W_a7194.
Proof. vm_refl. Qed.
Lemma D_a7194 : decode_any W_a7194 = Some (ShiftImm ALU_SLL 12 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7198 : bv 32 := 0x02c13023.
Lemma F_a7198 : fetch_word Ubsan.M.loaded_segments (0xa7198 : word) = Some W_a7198.
Proof. vm_refl. Qed.
Lemma D_a7198 : decode_any W_a7198 = Some (Store SZ8 2 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a719c : bv 32 := 0xfff5c393.
Lemma F_a719c : fetch_word Ubsan.M.loaded_segments (0xa719c : word) = Some W_a719c.
Proof. vm_refl. Qed.
Lemma D_a719c : decode_any W_a719c = Some (OpImm ALU_XOR 7 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a71a0 : bv 32 := 0x05013303.
Lemma F_a71a0 : fetch_word Ubsan.M.loaded_segments (0xa71a0 : word) = Some W_a71a0.
Proof. vm_refl. Qed.
Lemma D_a71a0 : decode_any W_a71a0 = Some (Load SZ8 true 6 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a71a4 : bv 32 := 0x00337613.
Lemma F_a71a4 : fetch_word Ubsan.M.loaded_segments (0xa71a4 : word) = Some W_a71a4.
Proof. vm_refl. Qed.
Lemma D_a71a4 : decode_any W_a71a4 = Some (OpImm ALU_AND 12 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a71a8 : bv 32 := 0x00197e13.
Lemma F_a71a8 : fetch_word Ubsan.M.loaded_segments (0xa71a8 : word) = Some W_a71a8.
Proof. vm_refl. Qed.
Lemma D_a71a8 : decode_any W_a71a8 = Some (OpImm ALU_AND 28 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a71ac : bv 32 := 0x00603eb3.
Lemma F_a71ac : fetch_word Ubsan.M.loaded_segments (0xa71ac : word) = Some W_a71ac.
Proof. vm_refl. Qed.
Lemma D_a71ac : decode_any W_a71ac = Some (Op ALU_SLTU 29 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_a71b0 : bv 32 := 0xaaaab6b7.
Lemma F_a71b0 : fetch_word Ubsan.M.loaded_segments (0xa71b0 : word) = Some W_a71b0.
Proof. vm_refl. Qed.
Lemma D_a71b0 : decode_any W_a71b0 = Some (Lui 13 699051, 4%Z).
Proof. vm_refl. Qed.

Definition W_a71b4 : bv 32 := 0x00171f93.
Lemma F_a71b4 : fetch_word Ubsan.M.loaded_segments (0xa71b4 : word) = Some W_a71b4.
Proof. vm_refl. Qed.
Lemma D_a71b4 : decode_any W_a71b4 = Some (ShiftImm ALU_SLL 31 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a71b8 : bv 32 := 0x03f13423.
Lemma F_a71b8 : fetch_word Ubsan.M.loaded_segments (0xa71b8 : word) = Some W_a71b8.
Proof. vm_refl. Qed.
Lemma D_a71b8 : decode_any W_a71b8 = Some (Store SZ8 2 31 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a71bc : bv 32 := 0x00271f13.
Lemma F_a71bc : fetch_word Ubsan.M.loaded_segments (0xa71bc : word) = Some W_a71bc.
Proof. vm_refl. Qed.
Lemma D_a71bc : decode_any W_a71bc = Some (ShiftImm ALU_SLL 30 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a71c0 : bv 32 := 0x00200a13.
Lemma F_a71c0 : fetch_word Ubsan.M.loaded_segments (0xa71c0 : word) = Some W_a71c0.
Proof. vm_refl. Qed.
Lemma D_a71c0 : decode_any W_a71c0 = Some (OpImm ALU_ADD 20 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a71c4 : bv 32 := 0x400004b7.
Lemma F_a71c4 : fetch_word Ubsan.M.loaded_segments (0xa71c4 : word) = Some W_a71c4.
Proof. vm_refl. Qed.
Lemma D_a71c4 : decode_any W_a71c4 = Some (Lui 9 262144, 4%Z).
Proof. vm_refl. Qed.

Definition W_a71c8 : bv 32 := 0x00163613.
Lemma F_a71c8 : fetch_word Ubsan.M.loaded_segments (0xa71c8 : word) = Some W_a71c8.
Proof. vm_refl. Qed.
Lemma D_a71c8 : decode_any W_a71c8 = Some (OpImm ALU_SLTU 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a71cc : bv 32 := 0xaaa68b13.
Lemma F_a71cc : fetch_word Ubsan.M.loaded_segments (0xa71cc : word) = Some W_a71cc.
Proof. vm_refl. Qed.
Lemma D_a71cc : decode_any W_a71cc = Some (OpImm ALU_ADD 22 13 2730, 4%Z).
Proof. vm_refl. Qed.

Definition W_a71d0 : bv 32 := 0x000f0713.
Lemma F_a71d0 : fetch_word Ubsan.M.loaded_segments (0xa71d0 : word) = Some W_a71d0.
Proof. vm_refl. Qed.
Lemma D_a71d0 : decode_any W_a71d0 = Some (OpImm ALU_ADD 14 30 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a71d4 : bv 32 := 0x01e30333.
Lemma F_a71d4 : fetch_word Ubsan.M.loaded_segments (0xa71d4 : word) = Some W_a71d4.
Proof. vm_refl. Qed.
Lemma D_a71d4 : decode_any W_a71d4 = Some (Op ALU_ADD 6 6 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_a71d8 : bv 32 := 0x00613c23.
Lemma F_a71d8 : fetch_word Ubsan.M.loaded_segments (0xa71d8 : word) = Some W_a71d8.
Proof. vm_refl. Qed.
Lemma D_a71d8 : decode_any W_a71d8 = Some (Store SZ8 2 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a71dc : bv 32 := 0x01d67c33.
Lemma F_a71dc : fetch_word Ubsan.M.loaded_segments (0xa71dc : word) = Some W_a71dc.
Proof. vm_refl. Qed.
Lemma D_a71dc : decode_any W_a71dc = Some (Op ALU_AND 24 12 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_a71e0 : bv 32 := 0xfff4849b.
Lemma F_a71e0 : fetch_word Ubsan.M.loaded_segments (0xa71e0 : word) = Some W_a71e0.
Proof. vm_refl. Qed.
Lemma D_a71e0 : decode_any W_a71e0 = Some (OpImm32 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a71e4 : bv 32 := 0x02913823.
Lemma F_a71e4 : fetch_word Ubsan.M.loaded_segments (0xa71e4 : word) = Some W_a71e4.
Proof. vm_refl. Qed.
Lemma D_a71e4 : decode_any W_a71e4 = Some (Store SZ8 2 9 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a71e8 : bv 32 := 0x04813683.
Lemma F_a71e8 : fetch_word Ubsan.M.loaded_segments (0xa71e8 : word) = Some W_a71e8.
Proof. vm_refl. Qed.
Lemma D_a71e8 : decode_any W_a71e8 = Some (Load SZ8 true 13 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a71ec : bv 32 := 0x02d28633.
Lemma F_a71ec : fetch_word Ubsan.M.loaded_segments (0xa71ec : word) = Some W_a71ec.
Proof. vm_refl. Qed.
Lemma D_a71ec : decode_any W_a71ec = Some (Mul M_MUL 12 5 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a71f0 : bv 32 := 0x02d286bb.
Lemma F_a71f0 : fetch_word Ubsan.M.loaded_segments (0xa71f0 : word) = Some W_a71f0.
Proof. vm_refl. Qed.
Lemma D_a71f0 : decode_any W_a71f0 = Some (Mul32 M_MUL 13 5 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a71f4 : bv 32 := 0x0ac698e3.
Lemma F_a71f4 : fetch_word Ubsan.M.loaded_segments (0xa71f4 : word) = Some W_a71f4.
Proof. vm_refl. Qed.
Lemma D_a71f4 : decode_any W_a71f4 = Some (Branch BC_NE 13 12 2224, 4%Z).
Proof. vm_refl. Qed.

Definition W_a71f8 : bv 32 := 0x0006061b.
Lemma F_a71f8 : fetch_word Ubsan.M.loaded_segments (0xa71f8 : word) = Some W_a71f8.
Proof. vm_refl. Qed.
Lemma D_a71f8 : decode_any W_a71f8 = Some (OpImm32 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a71fc : bv 32 := 0x00261d13.
Lemma F_a71fc : fetch_word Ubsan.M.loaded_segments (0xa71fc : word) = Some W_a71fc.
Proof. vm_refl. Qed.
Lemma D_a71fc : decode_any W_a71fc = Some (ShiftImm ALU_SLL 26 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7200 : bv 32 := 0x05013683.
Lemma F_a7200 : fetch_word Ubsan.M.loaded_segments (0xa7200 : word) = Some W_a7200.
Proof. vm_refl. Qed.
Lemma D_a7200 : decode_any W_a7200 = Some (Load SZ8 true 13 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7204 : bv 32 := 0x01a68d33.
Lemma F_a7204 : fetch_word Ubsan.M.loaded_segments (0xa7204 : word) = Some W_a7204.
Proof. vm_refl. Qed.
Lemma D_a7204 : decode_any W_a7204 = Some (Op ALU_ADD 26 13 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7208 : bv 32 := 0x001d3693.
Lemma F_a7208 : fetch_word Ubsan.M.loaded_segments (0xa7208 : word) = Some W_a7208.
Proof. vm_refl. Qed.
Lemma D_a7208 : decode_any W_a7208 = Some (OpImm ALU_SLTU 13 26 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a720c : bv 32 := 0x08de8ce3.
Lemma F_a720c : fetch_word Ubsan.M.loaded_segments (0xa720c : word) = Some W_a720c.
Proof. vm_refl. Qed.
Lemma D_a720c : decode_any W_a720c = Some (Branch BC_EQ 29 13 2200, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7210 : bv 32 := 0x05013683.
Lemma F_a7210 : fetch_word Ubsan.M.loaded_segments (0xa7210 : word) = Some W_a7210.
Proof. vm_refl. Qed.
Lemma D_a7210 : decode_any W_a7210 = Some (Load SZ8 true 13 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7214 : bv 32 := 0x00dd36b3.
Lemma F_a7214 : fetch_word Ubsan.M.loaded_segments (0xa7214 : word) = Some W_a7214.
Proof. vm_refl. Qed.
Lemma D_a7214 : decode_any W_a7214 = Some (Op ALU_SLTU 13 26 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7218 : bv 32 := 0x00062613.
Lemma F_a7218 : fetch_word Ubsan.M.loaded_segments (0xa7218 : word) = Some W_a7218.
Proof. vm_refl. Qed.
Lemma D_a7218 : decode_any W_a7218 = Some (OpImm ALU_SLT 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a721c : bv 32 := 0x00c6c633.
Lemma F_a721c : fetch_word Ubsan.M.loaded_segments (0xa721c : word) = Some W_a721c.
Proof. vm_refl. Qed.
Lemma D_a721c : decode_any W_a721c = Some (Op ALU_XOR 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7220 : bv 32 := 0x00164613.
Lemma F_a7220 : fetch_word Ubsan.M.loaded_segments (0xa7220 : word) = Some W_a7220.
Proof. vm_refl. Qed.
Lemma D_a7220 : decode_any W_a7220 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7224 : bv 32 := 0x080600e3.
Lemma F_a7224 : fetch_word Ubsan.M.loaded_segments (0xa7224 : word) = Some W_a7224.
Proof. vm_refl. Qed.
Lemma D_a7224 : decode_any W_a7224 = Some (Branch BC_EQ 12 0 2176, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7228 : bv 32 := 0x02a88633.
Lemma F_a7228 : fetch_word Ubsan.M.loaded_segments (0xa7228 : word) = Some W_a7228.
Proof. vm_refl. Qed.
Lemma D_a7228 : decode_any W_a7228 = Some (Mul M_MUL 12 17 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a722c : bv 32 := 0x02a886bb.
Lemma F_a722c : fetch_word Ubsan.M.loaded_segments (0xa722c : word) = Some W_a722c.
Proof. vm_refl. Qed.
Lemma D_a722c : decode_any W_a722c = Some (Mul32 M_MUL 13 17 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7230 : bv 32 := 0x06c69ae3.
Lemma F_a7230 : fetch_word Ubsan.M.loaded_segments (0xa7230 : word) = Some W_a7230.
Proof. vm_refl. Qed.
Lemma D_a7230 : decode_any W_a7230 = Some (Branch BC_NE 13 12 2164, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7234 : bv 32 := 0x01203db3.
Lemma F_a7234 : fetch_word Ubsan.M.loaded_segments (0xa7234 : word) = Some W_a7234.
Proof. vm_refl. Qed.
Lemma D_a7234 : decode_any W_a7234 = Some (Op ALU_SLTU 27 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7238 : bv 32 := 0x0006061b.
Lemma F_a7238 : fetch_word Ubsan.M.loaded_segments (0xa7238 : word) = Some W_a7238.
Proof. vm_refl. Qed.
Lemma D_a7238 : decode_any W_a7238 = Some (OpImm32 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a723c : bv 32 := 0x00261093.
Lemma F_a723c : fetch_word Ubsan.M.loaded_segments (0xa723c : word) = Some W_a723c.
Proof. vm_refl. Qed.
Lemma D_a723c : decode_any W_a723c = Some (ShiftImm ALU_SLL 1 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7240 : bv 32 := 0x001900b3.
Lemma F_a7240 : fetch_word Ubsan.M.loaded_segments (0xa7240 : word) = Some W_a7240.
Proof. vm_refl. Qed.
Lemma D_a7240 : decode_any W_a7240 = Some (Op ALU_ADD 1 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7244 : bv 32 := 0x0010b693.
Lemma F_a7244 : fetch_word Ubsan.M.loaded_segments (0xa7244 : word) = Some W_a7244.
Proof. vm_refl. Qed.
Lemma D_a7244 : decode_any W_a7244 = Some (OpImm ALU_SLTU 13 1 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7248 : bv 32 := 0x04dd8ee3.
Lemma F_a7248 : fetch_word Ubsan.M.loaded_segments (0xa7248 : word) = Some W_a7248.
Proof. vm_refl. Qed.
Lemma D_a7248 : decode_any W_a7248 = Some (Branch BC_EQ 27 13 2140, 4%Z).
Proof. vm_refl. Qed.

Definition W_a724c : bv 32 := 0x0120b6b3.
Lemma F_a724c : fetch_word Ubsan.M.loaded_segments (0xa724c : word) = Some W_a724c.
Proof. vm_refl. Qed.
Lemma D_a724c : decode_any W_a724c = Some (Op ALU_SLTU 13 1 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7250 : bv 32 := 0x00062613.
Lemma F_a7250 : fetch_word Ubsan.M.loaded_segments (0xa7250 : word) = Some W_a7250.
Proof. vm_refl. Qed.
Lemma D_a7250 : decode_any W_a7250 = Some (OpImm ALU_SLT 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7254 : bv 32 := 0x00c6c633.
Lemma F_a7254 : fetch_word Ubsan.M.loaded_segments (0xa7254 : word) = Some W_a7254.
Proof. vm_refl. Qed.
Lemma D_a7254 : decode_any W_a7254 = Some (Op ALU_XOR 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7258 : bv 32 := 0x00164613.
Lemma F_a7258 : fetch_word Ubsan.M.loaded_segments (0xa7258 : word) = Some W_a7258.
Proof. vm_refl. Qed.
Lemma D_a7258 : decode_any W_a7258 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a725c : bv 32 := 0x040604e3.
Lemma F_a725c : fetch_word Ubsan.M.loaded_segments (0xa725c : word) = Some W_a725c.
Proof. vm_refl. Qed.
Lemma D_a725c : decode_any W_a725c = Some (Branch BC_EQ 12 0 2120, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7260 : bv 32 := 0x04013603.
Lemma F_a7260 : fetch_word Ubsan.M.loaded_segments (0xa7260 : word) = Some W_a7260.
Proof. vm_refl. Qed.
Lemma D_a7260 : decode_any W_a7260 = Some (Load SZ8 true 12 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7264 : bv 32 := 0x0ec05e63.
Lemma F_a7264 : fetch_word Ubsan.M.loaded_segments (0xa7264 : word) = Some W_a7264.
Proof. vm_refl. Qed.
Lemma D_a7264 : decode_any W_a7264 = Some (Branch BC_GE 0 12 252, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7268 : bv 32 := 0x00000a93.
Lemma F_a7268 : fetch_word Ubsan.M.loaded_segments (0xa7268 : word) = Some W_a7268.
Proof. vm_refl. Qed.
Lemma D_a7268 : decode_any W_a7268 = Some (OpImm ALU_ADD 21 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a726c : bv 32 := 0x00281413.
Lemma F_a726c : fetch_word Ubsan.M.loaded_segments (0xa726c : word) = Some W_a726c.
Proof. vm_refl. Qed.
Lemma D_a726c : decode_any W_a726c = Some (ShiftImm ALU_SLL 8 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7270 : bv 32 := 0x00279613.
Lemma F_a7270 : fetch_word Ubsan.M.loaded_segments (0xa7270 : word) = Some W_a7270.
Proof. vm_refl. Qed.
Lemma D_a7270 : decode_any W_a7270 = Some (ShiftImm ALU_SLL 12 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7274 : bv 32 := 0x04813683.
Lemma F_a7274 : fetch_word Ubsan.M.loaded_segments (0xa7274 : word) = Some W_a7274.
Proof. vm_refl. Qed.
Lemma D_a7274 : decode_any W_a7274 = Some (Load SZ8 true 13 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7278 : bv 32 := 0x0006a693.
Lemma F_a7278 : fetch_word Ubsan.M.loaded_segments (0xa7278 : word) = Some W_a7278.
Proof. vm_refl. Qed.
Lemma D_a7278 : decode_any W_a7278 = Some (OpImm ALU_SLT 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a727c : bv 32 := 0x02013303.
Lemma F_a727c : fetch_word Ubsan.M.loaded_segments (0xa727c : word) = Some W_a727c.
Proof. vm_refl. Qed.
Lemma D_a727c : decode_any W_a727c = Some (Load SZ8 true 6 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7280 : bv 32 := 0x01a30333.
Lemma F_a7280 : fetch_word Ubsan.M.loaded_segments (0xa7280 : word) = Some W_a7280.
Proof. vm_refl. Qed.
Lemma D_a7280 : decode_any W_a7280 = Some (Op ALU_ADD 6 6 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7284 : bv 32 := 0x00ed0fb3.
Lemma F_a7284 : fetch_word Ubsan.M.loaded_segments (0xa7284 : word) = Some W_a7284.
Proof. vm_refl. Qed.
Lemma D_a7284 : decode_any W_a7284 = Some (Op ALU_ADD 31 26 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7288 : bv 32 := 0x00890433.
Lemma F_a7288 : fetch_word Ubsan.M.loaded_segments (0xa7288 : word) = Some W_a7288.
Proof. vm_refl. Qed.
Lemma D_a7288 : decode_any W_a7288 = Some (Op ALU_ADD 8 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a728c : bv 32 := 0x05013c83.
Lemma F_a728c : fetch_word Ubsan.M.loaded_segments (0xa728c : word) = Some W_a728c.
Proof. vm_refl. Qed.
Lemma D_a728c : decode_any W_a728c = Some (Load SZ8 true 25 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7290 : bv 32 := 0x00cc8cb3.
Lemma F_a7290 : fetch_word Ubsan.M.loaded_segments (0xa7290 : word) = Some W_a7290.
Proof. vm_refl. Qed.
Lemma D_a7290 : decode_any W_a7290 = Some (Op ALU_ADD 25 25 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7294 : bv 32 := 0x01813f03.
Lemma F_a7294 : fetch_word Ubsan.M.loaded_segments (0xa7294 : word) = Some W_a7294.
Proof. vm_refl. Qed.
Lemma D_a7294 : decode_any W_a7294 = Some (Load SZ8 true 30 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7298 : bv 32 := 0x00cf0633.
Lemma F_a7298 : fetch_word Ubsan.M.loaded_segments (0xa7298 : word) = Some W_a7298.
Proof. vm_refl. Qed.
Lemma D_a7298 : decode_any W_a7298 = Some (Op ALU_ADD 12 30 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a729c : bv 32 := 0x00603f33.
Lemma F_a729c : fetch_word Ubsan.M.loaded_segments (0xa729c : word) = Some W_a729c.
Proof. vm_refl. Qed.
Lemma D_a729c : decode_any W_a729c = Some (Op ALU_SLTU 30 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_a72a0 : bv 32 := 0x01a33333.
Lemma F_a72a0 : fetch_word Ubsan.M.loaded_segments (0xa72a0 : word) = Some W_a72a0.
Proof. vm_refl. Qed.
Lemma D_a72a0 : decode_any W_a72a0 = Some (Op ALU_SLTU 6 6 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_a72a4 : bv 32 := 0x00d346b3.
Lemma F_a72a4 : fetch_word Ubsan.M.loaded_segments (0xa72a4 : word) = Some W_a72a4.
Proof. vm_refl. Qed.
Lemma D_a72a4 : decode_any W_a72a4 = Some (Op ALU_XOR 13 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a72a8 : bv 32 := 0x0016c693.
Lemma F_a72a8 : fetch_word Ubsan.M.loaded_segments (0xa72a8 : word) = Some W_a72a8.
Proof. vm_refl. Qed.
Lemma D_a72a8 : decode_any W_a72a8 = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a72ac : bv 32 := 0x00df7f33.
Lemma F_a72ac : fetch_word Ubsan.M.loaded_segments (0xa72ac : word) = Some W_a72ac.
Proof. vm_refl. Qed.
Lemma D_a72ac : decode_any W_a72ac = Some (Op ALU_AND 30 30 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a72b0 : bv 32 := 0xffffc313.
Lemma F_a72b0 : fetch_word Ubsan.M.loaded_segments (0xa72b0 : word) = Some W_a72b0.
Proof. vm_refl. Qed.
Lemma D_a72b0 : decode_any W_a72b0 = Some (OpImm ALU_XOR 6 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a72b4 : bv 32 := 0x04013b83.
Lemma F_a72b4 : fetch_word Ubsan.M.loaded_segments (0xa72b4 : word) = Some W_a72b4.
Proof. vm_refl. Qed.
Lemma D_a72b4 : decode_any W_a72b4 = Some (Load SZ8 true 23 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a72b8 : bv 32 := 0x00040993.
Lemma F_a72b8 : fetch_word Ubsan.M.loaded_segments (0xa72b8 : word) = Some W_a72b8.
Proof. vm_refl. Qed.
Lemma D_a72b8 : decode_any W_a72b8 = Some (OpImm ALU_ADD 19 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a72bc : bv 32 := 0x015c8fb3.
Lemma F_a72bc : fetch_word Ubsan.M.loaded_segments (0xa72bc : word) = Some W_a72bc.
Proof. vm_refl. Qed.
Lemma D_a72bc : decode_any W_a72bc = Some (Op ALU_ADD 31 25 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_a72c0 : bv 32 := 0x7fafe263.
Lemma F_a72c0 : fetch_word Ubsan.M.loaded_segments (0xa72c0 : word) = Some W_a72c0.
Proof. vm_refl. Qed.
Lemma D_a72c0 : decode_any W_a72c0 = Some (Branch BC_LTU 31 26 2020, 4%Z).
Proof. vm_refl. Qed.

Definition W_a72c4 : bv 32 := 0x001fb693.
Lemma F_a72c4 : fetch_word Ubsan.M.loaded_segments (0xa72c4 : word) = Some W_a72c4.
Proof. vm_refl. Qed.
Lemma D_a72c4 : decode_any W_a72c4 = Some (OpImm ALU_SLTU 13 31 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a72c8 : bv 32 := 0x00dec6b3.
Lemma F_a72c8 : fetch_word Ubsan.M.loaded_segments (0xa72c8 : word) = Some W_a72c8.
Proof. vm_refl. Qed.
Lemma D_a72c8 : decode_any W_a72c8 = Some (Op ALU_XOR 13 29 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a72cc : bv 32 := 0x7c068c63.
Lemma F_a72cc : fetch_word Ubsan.M.loaded_segments (0xa72cc : word) = Some W_a72cc.
Proof. vm_refl. Qed.
Lemma D_a72cc : decode_any W_a72cc = Some (Branch BC_EQ 13 0 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_a72d0 : bv 32 := 0x7c0c0a63.
Lemma F_a72d0 : fetch_word Ubsan.M.loaded_segments (0xa72d0 : word) = Some W_a72d0.
Proof. vm_refl. Qed.
Lemma D_a72d0 : decode_any W_a72d0 = Some (Branch BC_EQ 24 0 2004, 4%Z).
Proof. vm_refl. Qed.

Definition W_a72d4 : bv 32 := 0x7c0f0863.
Lemma F_a72d4 : fetch_word Ubsan.M.loaded_segments (0xa72d4 : word) = Some W_a72d4.
Proof. vm_refl. Qed.
Lemma D_a72d4 : decode_any W_a72d4 = Some (Branch BC_EQ 30 0 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_a72d8 : bv 32 := 0x7d536663.
Lemma F_a72d8 : fetch_word Ubsan.M.loaded_segments (0xa72d8 : word) = Some W_a72d8.
Proof. vm_refl. Qed.
Lemma D_a72d8 : decode_any W_a72d8 = Some (Branch BC_LTU 6 21 1996, 4%Z).
Proof. vm_refl. Qed.

Definition W_a72dc : bv 32 := 0x015606b3.
Lemma F_a72dc : fetch_word Ubsan.M.loaded_segments (0xa72dc : word) = Some W_a72dc.
Proof. vm_refl. Qed.
Lemma D_a72dc : decode_any W_a72dc = Some (Op ALU_ADD 13 12 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_a72e0 : bv 32 := 0x000faf83.
Lemma F_a72e0 : fetch_word Ubsan.M.loaded_segments (0xa72e0 : word) = Some W_a72e0.
Proof. vm_refl. Qed.
Lemma D_a72e0 : decode_any W_a72e0 = Some (Load SZ4 true 31 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a72e4 : bv 32 := 0x0006a683.
Lemma F_a72e4 : fetch_word Ubsan.M.loaded_segments (0xa72e4 : word) = Some W_a72e4.
Proof. vm_refl. Qed.
Lemma D_a72e4 : decode_any W_a72e4 = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a72e8 : bv 32 := 0x01f6e6b3.
Lemma F_a72e8 : fetch_word Ubsan.M.loaded_segments (0xa72e8 : word) = Some W_a72e8.
Proof. vm_refl. Qed.
Lemma D_a72e8 : decode_any W_a72e8 = Some (Op ALU_OR 13 13 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_a72ec : bv 32 := 0x00169f93.
Lemma F_a72ec : fetch_word Ubsan.M.loaded_segments (0xa72ec : word) = Some W_a72ec.
Proof. vm_refl. Qed.
Lemma D_a72ec : decode_any W_a72ec = Some (ShiftImm ALU_SLL 31 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a72f0 : bv 32 := 0x00dfe6b3.
Lemma F_a72f0 : fetch_word Ubsan.M.loaded_segments (0xa72f0 : word) = Some W_a72f0.
Proof. vm_refl. Qed.
Lemma D_a72f0 : decode_any W_a72f0 = Some (Op ALU_OR 13 31 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a72f4 : bv 32 := 0x0166f6b3.
Lemma F_a72f4 : fetch_word Ubsan.M.loaded_segments (0xa72f4 : word) = Some W_a72f4.
Proof. vm_refl. Qed.
Lemma D_a72f4 : decode_any W_a72f4 = Some (Op ALU_AND 13 13 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_a72f8 : bv 32 := 0x00769f93.
Lemma F_a72f8 : fetch_word Ubsan.M.loaded_segments (0xa72f8 : word) = Some W_a72f8.
Proof. vm_refl. Qed.
Lemma D_a72f8 : decode_any W_a72f8 = Some (ShiftImm ALU_SLL 31 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_a72fc : bv 32 := 0x00df86b3.
Lemma F_a72fc : fetch_word Ubsan.M.loaded_segments (0xa72fc : word) = Some W_a72fc.
Proof. vm_refl. Qed.
Lemma D_a72fc : decode_any W_a72fc = Some (Op ALU_ADD 13 31 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7300 : bv 32 := 0x0186df9b.
Lemma F_a7300 : fetch_word Ubsan.M.loaded_segments (0xa7300 : word) = Some W_a7300.
Proof. vm_refl. Qed.
Lemma D_a7300 : decode_any W_a7300 = Some (ShiftImm32 ALU_SRL 31 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7304 : bv 32 := 0x7bf3e063.
Lemma F_a7304 : fetch_word Ubsan.M.loaded_segments (0xa7304 : word) = Some W_a7304.
Proof. vm_refl. Qed.
Lemma D_a7304 : decode_any W_a7304 = Some (Branch BC_LTU 7 31 1952, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7308 : bv 32 := 0x03069693.
Lemma F_a7308 : fetch_word Ubsan.M.loaded_segments (0xa7308 : word) = Some W_a7308.
Proof. vm_refl. Qed.
Lemma D_a7308 : decode_any W_a7308 = Some (ShiftImm ALU_SLL 13 13 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a730c : bv 32 := 0x0386d693.
Lemma F_a730c : fetch_word Ubsan.M.loaded_segments (0xa730c : word) = Some W_a730c.
Proof. vm_refl. Qed.
Lemma D_a730c : decode_any W_a730c = Some (ShiftImm ALU_SRL 13 13 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7310 : bv 32 := 0x78d3ea63.
Lemma F_a7310 : fetch_word Ubsan.M.loaded_segments (0xa7310 : word) = Some W_a7310.
Proof. vm_refl. Qed.
Lemma D_a7310 : decode_any W_a7310 = Some (Branch BC_LTU 7 13 1940, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7314 : bv 32 := 0x7819e863.
Lemma F_a7314 : fetch_word Ubsan.M.loaded_segments (0xa7314 : word) = Some W_a7314.
Proof. vm_refl. Qed.
Lemma D_a7314 : decode_any W_a7314 = Some (Branch BC_LTU 19 1 1936, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7318 : bv 32 := 0x0019b493.
Lemma F_a7318 : fetch_word Ubsan.M.loaded_segments (0xa7318 : word) = Some W_a7318.
Proof. vm_refl. Qed.
Lemma D_a7318 : decode_any W_a7318 = Some (OpImm ALU_SLTU 9 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a731c : bv 32 := 0x009dc4b3.
Lemma F_a731c : fetch_word Ubsan.M.loaded_segments (0xa731c : word) = Some W_a731c.
Proof. vm_refl. Qed.
Lemma D_a731c : decode_any W_a731c = Some (Op ALU_XOR 9 27 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7320 : bv 32 := 0x78048263.
Lemma F_a7320 : fetch_word Ubsan.M.loaded_segments (0xa7320 : word) = Some W_a7320.
Proof. vm_refl. Qed.
Lemma D_a7320 : decode_any W_a7320 = Some (Branch BC_EQ 9 0 1924, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7324 : bv 32 := 0x780e1063.
Lemma F_a7324 : fetch_word Ubsan.M.loaded_segments (0xa7324 : word) = Some W_a7324.
Proof. vm_refl. Qed.
Lemma D_a7324 : decode_any W_a7324 = Some (Branch BC_NE 28 0 1920, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7328 : bv 32 := 0x77440e63.
Lemma F_a7328 : fetch_word Ubsan.M.loaded_segments (0xa7328 : word) = Some W_a7328.
Proof. vm_refl. Qed.
Lemma D_a7328 : decode_any W_a7328 = Some (Branch BC_EQ 8 20 1916, 4%Z).
Proof. vm_refl. Qed.

Definition W_a732c : bv 32 := 0x00d586b3.
Lemma F_a732c : fetch_word Ubsan.M.loaded_segments (0xa732c : word) = Some W_a732c.
Proof. vm_refl. Qed.
Lemma D_a732c : decode_any W_a732c = Some (Op ALU_ADD 13 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7330 : bv 32 := 0x01f58fb3.
Lemma F_a7330 : fetch_word Ubsan.M.loaded_segments (0xa7330 : word) = Some W_a7330.
Proof. vm_refl. Qed.
Lemma D_a7330 : decode_any W_a7330 = Some (Op ALU_ADD 31 11 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7334 : bv 32 := 0x000fcf83.
Lemma F_a7334 : fetch_word Ubsan.M.loaded_segments (0xa7334 : word) = Some W_a7334.
Proof. vm_refl. Qed.
Lemma D_a7334 : decode_any W_a7334 = Some (Load SZ1 false 31 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7338 : bv 32 := 0x0006c683.
Lemma F_a7338 : fetch_word Ubsan.M.loaded_segments (0xa7338 : word) = Some W_a7338.
Proof. vm_refl. Qed.
Lemma D_a7338 : decode_any W_a7338 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a733c : bv 32 := 0x008f9f93.
Lemma F_a733c : fetch_word Ubsan.M.loaded_segments (0xa733c : word) = Some W_a733c.
Proof. vm_refl. Qed.
Lemma D_a733c : decode_any W_a733c = Some (ShiftImm ALU_SLL 31 31 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7340 : bv 32 := 0x00dfe6b3.
Lemma F_a7340 : fetch_word Ubsan.M.loaded_segments (0xa7340 : word) = Some W_a7340.
Proof. vm_refl. Qed.
Lemma D_a7340 : decode_any W_a7340 = Some (Op ALU_OR 13 31 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7344 : bv 32 := 0x0029cf93.
Lemma F_a7344 : fetch_word Ubsan.M.loaded_segments (0xa7344 : word) = Some W_a7344.
Proof. vm_refl. Qed.
Lemma D_a7344 : decode_any W_a7344 = Some (OpImm ALU_XOR 31 19 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7348 : bv 32 := 0x00298993.
Lemma F_a7348 : fetch_word Ubsan.M.loaded_segments (0xa7348 : word) = Some W_a7348.
Proof. vm_refl. Qed.
Lemma D_a7348 : decode_any W_a7348 = Some (OpImm ALU_ADD 19 19 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a734c : bv 32 := 0x004a8a93.
Lemma F_a734c : fetch_word Ubsan.M.loaded_segments (0xa734c : word) = Some W_a734c.
Proof. vm_refl. Qed.
Lemma D_a734c : decode_any W_a734c = Some (OpImm ALU_ADD 21 21 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7350 : bv 32 := 0xfffb8b93.
Lemma F_a7350 : fetch_word Ubsan.M.loaded_segments (0xa7350 : word) = Some W_a7350.
Proof. vm_refl. Qed.
Lemma D_a7350 : decode_any W_a7350 = Some (OpImm ALU_ADD 23 23 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7354 : bv 32 := 0x00df9023.
Lemma F_a7354 : fetch_word Ubsan.M.loaded_segments (0xa7354 : word) = Some W_a7354.
Proof. vm_refl. Qed.
Lemma D_a7354 : decode_any W_a7354 = Some (Store SZ2 31 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7358 : bv 32 := 0x00240413.
Lemma F_a7358 : fetch_word Ubsan.M.loaded_segments (0xa7358 : word) = Some W_a7358.
Proof. vm_refl. Qed.
Lemma D_a7358 : decode_any W_a7358 = Some (OpImm ALU_ADD 8 8 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a735c : bv 32 := 0xf60b90e3.
Lemma F_a735c : fetch_word Ubsan.M.loaded_segments (0xa735c : word) = Some W_a735c.
Proof. vm_refl. Qed.
Lemma D_a735c : decode_any W_a735c = Some (Branch BC_NE 23 0 8032, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7360 : bv 32 := 0x03013603.
Lemma F_a7360 : fetch_word Ubsan.M.loaded_segments (0xa7360 : word) = Some W_a7360.
Proof. vm_refl. Qed.
Lemma D_a7360 : decode_any W_a7360 = Some (Load SZ8 true 12 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7364 : bv 32 := 0x74c88063.
Lemma F_a7364 : fetch_word Ubsan.M.loaded_segments (0xa7364 : word) = Some W_a7364.
Proof. vm_refl. Qed.
Lemma D_a7364 : decode_any W_a7364 = Some (Branch BC_EQ 17 12 1856, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7368 : bv 32 := 0x0022829b.
Lemma F_a7368 : fetch_word Ubsan.M.loaded_segments (0xa7368 : word) = Some W_a7368.
Proof. vm_refl. Qed.
Lemma D_a7368 : decode_any W_a7368 = Some (OpImm32 5 5 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a736c : bv 32 := 0x0018889b.
Lemma F_a736c : fetch_word Ubsan.M.loaded_segments (0xa736c : word) = Some W_a736c.
Proof. vm_refl. Qed.
Lemma D_a736c : decode_any W_a736c = Some (OpImm32 17 17 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7370 : bv 32 := 0x00a8083b.
Lemma F_a7370 : fetch_word Ubsan.M.loaded_segments (0xa7370 : word) = Some W_a7370.
Proof. vm_refl. Qed.
Lemma D_a7370 : decode_any W_a7370 = Some (Op32 ALU_ADD 16 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7374 : bv 32 := 0x02813603.
Lemma F_a7374 : fetch_word Ubsan.M.loaded_segments (0xa7374 : word) = Some W_a7374.
Proof. vm_refl. Qed.
Lemma D_a7374 : decode_any W_a7374 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7378 : bv 32 := 0x00c787bb.
Lemma F_a7378 : fetch_word Ubsan.M.loaded_segments (0xa7378 : word) = Some W_a7378.
Proof. vm_refl. Qed.
Lemma D_a7378 : decode_any W_a7378 = Some (Op32 ALU_ADD 15 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a737c : bv 32 := 0x03813603.
Lemma F_a737c : fetch_word Ubsan.M.loaded_segments (0xa737c : word) = Some W_a737c.
Proof. vm_refl. Qed.
Lemma D_a737c : decode_any W_a737c = Some (Load SZ8 true 12 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7380 : bv 32 := 0xe6c2c4e3.
Lemma F_a7380 : fetch_word Ubsan.M.loaded_segments (0xa7380 : word) = Some W_a7380.
Proof. vm_refl. Qed.
Lemma D_a7380 : decode_any W_a7380 = Some (Branch BC_LT 5 12 7784, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7384 : bv 32 := 0x6980006f.
Lemma F_a7384 : fetch_word Ubsan.M.loaded_segments (0xa7384 : word) = Some W_a7384.
Proof. vm_refl. Qed.
Lemma D_a7384 : decode_any W_a7384 = Some (Jal 0 1688, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7388 : bv 32 := 0x0007f517.
Lemma F_a7388 : fetch_word Ubsan.M.loaded_segments (0xa7388 : word) = Some W_a7388.
Proof. vm_refl. Qed.
Lemma D_a7388 : decode_any W_a7388 = Some (Auipc 10 127, 4%Z).
Proof. vm_refl. Qed.

Definition W_a738c : bv 32 := 0x6e853503.
Lemma F_a738c : fetch_word Ubsan.M.loaded_segments (0xa738c : word) = Some W_a738c.
Proof. vm_refl. Qed.
Lemma D_a738c : decode_any W_a738c = Some (Load SZ8 true 10 10 1768, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7390 : bv 32 := 0x00052503.
Lemma F_a7390 : fetch_word Ubsan.M.loaded_segments (0xa7390 : word) = Some W_a7390.
Proof. vm_refl. Qed.
Lemma D_a7390 : decode_any W_a7390 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7394 : bv 32 := 0x00500593.
Lemma F_a7394 : fetch_word Ubsan.M.loaded_segments (0xa7394 : word) = Some W_a7394.
Proof. vm_refl. Qed.
Lemma D_a7394 : decode_any W_a7394 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7398 : bv 32 := 0x6ca5c663.
Lemma F_a7398 : fetch_word Ubsan.M.loaded_segments (0xa7398 : word) = Some W_a7398.
Proof. vm_refl. Qed.
Lemma D_a7398 : decode_any W_a7398 = Some (Branch BC_LT 11 10 1740, 4%Z).
Proof. vm_refl. Qed.

Definition W_a739c : bv 32 := 0xfff6b517.
Lemma F_a739c : fetch_word Ubsan.M.loaded_segments (0xa739c : word) = Some W_a739c.
Proof. vm_refl. Qed.
Lemma D_a739c : decode_any W_a739c = Some (Auipc 10 1048427, 4%Z).
Proof. vm_refl. Qed.

Definition W_a73a0 : bv 32 := 0xfff6f597.
Lemma F_a73a0 : fetch_word Ubsan.M.loaded_segments (0xa73a0 : word) = Some W_a73a0.
Proof. vm_refl. Qed.
Lemma D_a73a0 : decode_any W_a73a0 = Some (Auipc 11 1048431, 4%Z).
Proof. vm_refl. Qed.

Definition W_a73a4 : bv 32 := 0x33e50513.
Lemma F_a73a4 : fetch_word Ubsan.M.loaded_segments (0xa73a4 : word) = Some W_a73a4.
Proof. vm_refl. Qed.
Lemma D_a73a4 : decode_any W_a73a4 = Some (OpImm ALU_ADD 10 10 830, 4%Z).
Proof. vm_refl. Qed.

Definition W_a73a8 : bv 32 := 0xfe658593.
Lemma F_a73a8 : fetch_word Ubsan.M.loaded_segments (0xa73a8 : word) = Some W_a73a8.
Proof. vm_refl. Qed.
Lemma D_a73a8 : decode_any W_a73a8 = Some (OpImm ALU_ADD 11 11 4070, 4%Z).
Proof. vm_refl. Qed.

Definition W_a73ac : bv 32 := 0x00000613.
Lemma F_a73ac : fetch_word Ubsan.M.loaded_segments (0xa73ac : word) = Some W_a73ac.
Proof. vm_refl. Qed.
Lemma D_a73ac : decode_any W_a73ac = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a73b0 : bv 32 := 0xb90bc0ef.
Lemma F_a73b0 : fetch_word Ubsan.M.loaded_segments (0xa73b0 : word) = Some W_a73b0.
Proof. vm_refl. Qed.
Lemma D_a73b0 : decode_any W_a73b0 = Some (Jal 1 1819536, 4%Z).
Proof. vm_refl. Qed.

Definition W_a73b4 : bv 32 := 0x6b40006f.
Lemma F_a73b4 : fetch_word Ubsan.M.loaded_segments (0xa73b4 : word) = Some W_a73b4.
Proof. vm_refl. Qed.
Lemma D_a73b4 : decode_any W_a73b4 = Some (Jal 0 1716, 4%Z).
Proof. vm_refl. Qed.

Definition W_a73b8 : bv 32 := 0x00300693.
Lemma F_a73b8 : fetch_word Ubsan.M.loaded_segments (0xa73b8 : word) = Some W_a73b8.
Proof. vm_refl. Qed.
Lemma D_a73b8 : decode_any W_a73b8 = Some (OpImm ALU_ADD 13 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a73bc : bv 32 := 0x44da1a63.
Lemma F_a73bc : fetch_word Ubsan.M.loaded_segments (0xa73bc : word) = Some W_a73bc.
Proof. vm_refl. Qed.
Lemma D_a73bc : decode_any W_a73bc = Some (Branch BC_NE 20 13 1108, 4%Z).
Proof. vm_refl. Qed.

Definition W_a73c0 : bv 32 := 0x6e061263.
Lemma F_a73c0 : fetch_word Ubsan.M.loaded_segments (0xa73c0 : word) = Some W_a73c0.
Proof. vm_refl. Qed.
Lemma D_a73c0 : decode_any W_a73c0 = Some (Branch BC_NE 12 0 1764, 4%Z).
Proof. vm_refl. Qed.

Definition W_a73c4 : bv 32 := 0x03813603.
Lemma F_a73c4 : fetch_word Ubsan.M.loaded_segments (0xa73c4 : word) = Some W_a73c4.
Proof. vm_refl. Qed.
Lemma D_a73c4 : decode_any W_a73c4 = Some (Load SZ8 true 12 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a73c8 : bv 32 := 0x64c05a63.
Lemma F_a73c8 : fetch_word Ubsan.M.loaded_segments (0xa73c8 : word) = Some W_a73c8.
Proof. vm_refl. Qed.
Lemma D_a73c8 : decode_any W_a73c8 = Some (Branch BC_GE 0 12 1620, 4%Z).
Proof. vm_refl. Qed.

Definition W_a73cc : bv 32 := 0x00000793.
Lemma F_a73cc : fetch_word Ubsan.M.loaded_segments (0xa73cc : word) = Some W_a73cc.
Proof. vm_refl. Qed.
Lemma D_a73cc : decode_any W_a73cc = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a73d0 : bv 32 := 0x00000813.
Lemma F_a73d0 : fetch_word Ubsan.M.loaded_segments (0xa73d0 : word) = Some W_a73d0.
Proof. vm_refl. Qed.
Lemma D_a73d0 : decode_any W_a73d0 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a73d4 : bv 32 := 0x00000893.
Lemma F_a73d4 : fetch_word Ubsan.M.loaded_segments (0xa73d4 : word) = Some W_a73d4.
Proof. vm_refl. Qed.
Lemma D_a73d4 : decode_any W_a73d4 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a73d8 : bv 32 := 0x00000293.
Lemma F_a73d8 : fetch_word Ubsan.M.loaded_segments (0xa73d8 : word) = Some W_a73d8.
Proof. vm_refl. Qed.
Lemma D_a73d8 : decode_any W_a73d8 = Some (OpImm ALU_ADD 5 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a73dc : bv 32 := 0x04813703.
Lemma F_a73dc : fetch_word Ubsan.M.loaded_segments (0xa73dc : word) = Some W_a73dc.
Proof. vm_refl. Qed.
Lemma D_a73dc : decode_any W_a73dc = Some (Load SZ8 true 14 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a73e0 : bv 32 := 0x00271613.
Lemma F_a73e0 : fetch_word Ubsan.M.loaded_segments (0xa73e0 : word) = Some W_a73e0.
Proof. vm_refl. Qed.
Lemma D_a73e0 : decode_any W_a73e0 = Some (ShiftImm ALU_SLL 12 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a73e4 : bv 32 := 0x02c13023.
Lemma F_a73e4 : fetch_word Ubsan.M.loaded_segments (0xa73e4 : word) = Some W_a73e4.
Proof. vm_refl. Qed.
Lemma D_a73e4 : decode_any W_a73e4 = Some (Store SZ8 2 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a73e8 : bv 32 := 0xfff5c393.
Lemma F_a73e8 : fetch_word Ubsan.M.loaded_segments (0xa73e8 : word) = Some W_a73e8.
Proof. vm_refl. Qed.
Lemma D_a73e8 : decode_any W_a73e8 = Some (OpImm ALU_XOR 7 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a73ec : bv 32 := 0x05013f03.
Lemma F_a73ec : fetch_word Ubsan.M.loaded_segments (0xa73ec : word) = Some W_a73ec.
Proof. vm_refl. Qed.
Lemma D_a73ec : decode_any W_a73ec = Some (Load SZ8 true 30 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a73f0 : bv 32 := 0x003f7613.
Lemma F_a73f0 : fetch_word Ubsan.M.loaded_segments (0xa73f0 : word) = Some W_a73f0.
Proof. vm_refl. Qed.
Lemma D_a73f0 : decode_any W_a73f0 = Some (OpImm ALU_AND 12 30 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a73f4 : bv 32 := 0x00197e13.
Lemma F_a73f4 : fetch_word Ubsan.M.loaded_segments (0xa73f4 : word) = Some W_a73f4.
Proof. vm_refl. Qed.
Lemma D_a73f4 : decode_any W_a73f4 = Some (OpImm ALU_AND 28 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a73f8 : bv 32 := 0x01e03eb3.
Lemma F_a73f8 : fetch_word Ubsan.M.loaded_segments (0xa73f8 : word) = Some W_a73f8.
Proof. vm_refl. Qed.
Lemma D_a73f8 : decode_any W_a73f8 = Some (Op ALU_SLTU 29 0 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_a73fc : bv 32 := 0xaaaab6b7.
Lemma F_a73fc : fetch_word Ubsan.M.loaded_segments (0xa73fc : word) = Some W_a73fc.
Proof. vm_refl. Qed.
Lemma D_a73fc : decode_any W_a73fc = Some (Lui 13 699051, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7400 : bv 32 := 0x00171313.
Lemma F_a7400 : fetch_word Ubsan.M.loaded_segments (0xa7400 : word) = Some W_a7400.
Proof. vm_refl. Qed.
Lemma D_a7400 : decode_any W_a7400 = Some (ShiftImm ALU_SLL 6 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7404 : bv 32 := 0x02613423.
Lemma F_a7404 : fetch_word Ubsan.M.loaded_segments (0xa7404 : word) = Some W_a7404.
Proof. vm_refl. Qed.
Lemma D_a7404 : decode_any W_a7404 = Some (Store SZ8 2 6 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7408 : bv 32 := 0x00271713.
Lemma F_a7408 : fetch_word Ubsan.M.loaded_segments (0xa7408 : word) = Some W_a7408.
Proof. vm_refl. Qed.
Lemma D_a7408 : decode_any W_a7408 = Some (ShiftImm ALU_SLL 14 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a740c : bv 32 := 0x00200a13.
Lemma F_a740c : fetch_word Ubsan.M.loaded_segments (0xa740c : word) = Some W_a740c.
Proof. vm_refl. Qed.
Lemma D_a740c : decode_any W_a740c = Some (OpImm ALU_ADD 20 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7410 : bv 32 := 0x40000337.
Lemma F_a7410 : fetch_word Ubsan.M.loaded_segments (0xa7410 : word) = Some W_a7410.
Proof. vm_refl. Qed.
Lemma D_a7410 : decode_any W_a7410 = Some (Lui 6 262144, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7414 : bv 32 := 0x00163613.
Lemma F_a7414 : fetch_word Ubsan.M.loaded_segments (0xa7414 : word) = Some W_a7414.
Proof. vm_refl. Qed.
Lemma D_a7414 : decode_any W_a7414 = Some (OpImm ALU_SLTU 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7418 : bv 32 := 0xaaa68b13.
Lemma F_a7418 : fetch_word Ubsan.M.loaded_segments (0xa7418 : word) = Some W_a7418.
Proof. vm_refl. Qed.
Lemma D_a7418 : decode_any W_a7418 = Some (OpImm ALU_ADD 22 13 2730, 4%Z).
Proof. vm_refl. Qed.

Definition W_a741c : bv 32 := 0x00e13c23.
Lemma F_a741c : fetch_word Ubsan.M.loaded_segments (0xa741c : word) = Some W_a741c.
Proof. vm_refl. Qed.
Lemma D_a741c : decode_any W_a741c = Some (Store SZ8 2 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7420 : bv 32 := 0x00ef0733.
Lemma F_a7420 : fetch_word Ubsan.M.loaded_segments (0xa7420 : word) = Some W_a7420.
Proof. vm_refl. Qed.
Lemma D_a7420 : decode_any W_a7420 = Some (Op ALU_ADD 14 30 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7424 : bv 32 := 0x00e13823.
Lemma F_a7424 : fetch_word Ubsan.M.loaded_segments (0xa7424 : word) = Some W_a7424.
Proof. vm_refl. Qed.
Lemma D_a7424 : decode_any W_a7424 = Some (Store SZ8 2 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7428 : bv 32 := 0x01d67c33.
Lemma F_a7428 : fetch_word Ubsan.M.loaded_segments (0xa7428 : word) = Some W_a7428.
Proof. vm_refl. Qed.
Lemma D_a7428 : decode_any W_a7428 = Some (Op ALU_AND 24 12 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_a742c : bv 32 := 0xfff3031b.
Lemma F_a742c : fetch_word Ubsan.M.loaded_segments (0xa742c : word) = Some W_a742c.
Proof. vm_refl. Qed.
Lemma D_a742c : decode_any W_a742c = Some (OpImm32 6 6 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7430 : bv 32 := 0x02613823.
Lemma F_a7430 : fetch_word Ubsan.M.loaded_segments (0xa7430 : word) = Some W_a7430.
Proof. vm_refl. Qed.
Lemma D_a7430 : decode_any W_a7430 = Some (Store SZ8 2 6 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7434 : bv 32 := 0x04813683.
Lemma F_a7434 : fetch_word Ubsan.M.loaded_segments (0xa7434 : word) = Some W_a7434.
Proof. vm_refl. Qed.
Lemma D_a7434 : decode_any W_a7434 = Some (Load SZ8 true 13 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7438 : bv 32 := 0x02d28633.
Lemma F_a7438 : fetch_word Ubsan.M.loaded_segments (0xa7438 : word) = Some W_a7438.
Proof. vm_refl. Qed.
Lemma D_a7438 : decode_any W_a7438 = Some (Mul M_MUL 12 5 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a743c : bv 32 := 0x02d286bb.
Lemma F_a743c : fetch_word Ubsan.M.loaded_segments (0xa743c : word) = Some W_a743c.
Proof. vm_refl. Qed.
Lemma D_a743c : decode_any W_a743c = Some (Mul32 M_MUL 13 5 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7440 : bv 32 := 0x66c69263.
Lemma F_a7440 : fetch_word Ubsan.M.loaded_segments (0xa7440 : word) = Some W_a7440.
Proof. vm_refl. Qed.
Lemma D_a7440 : decode_any W_a7440 = Some (Branch BC_NE 13 12 1636, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7444 : bv 32 := 0x0006061b.
Lemma F_a7444 : fetch_word Ubsan.M.loaded_segments (0xa7444 : word) = Some W_a7444.
Proof. vm_refl. Qed.
Lemma D_a7444 : decode_any W_a7444 = Some (OpImm32 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7448 : bv 32 := 0x00261d13.
Lemma F_a7448 : fetch_word Ubsan.M.loaded_segments (0xa7448 : word) = Some W_a7448.
Proof. vm_refl. Qed.
Lemma D_a7448 : decode_any W_a7448 = Some (ShiftImm ALU_SLL 26 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a744c : bv 32 := 0x05013683.
Lemma F_a744c : fetch_word Ubsan.M.loaded_segments (0xa744c : word) = Some W_a744c.
Proof. vm_refl. Qed.
Lemma D_a744c : decode_any W_a744c = Some (Load SZ8 true 13 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7450 : bv 32 := 0x01a68d33.
Lemma F_a7450 : fetch_word Ubsan.M.loaded_segments (0xa7450 : word) = Some W_a7450.
Proof. vm_refl. Qed.
Lemma D_a7450 : decode_any W_a7450 = Some (Op ALU_ADD 26 13 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7454 : bv 32 := 0x001d3693.
Lemma F_a7454 : fetch_word Ubsan.M.loaded_segments (0xa7454 : word) = Some W_a7454.
Proof. vm_refl. Qed.
Lemma D_a7454 : decode_any W_a7454 = Some (OpImm ALU_SLTU 13 26 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7458 : bv 32 := 0x64de8663.
Lemma F_a7458 : fetch_word Ubsan.M.loaded_segments (0xa7458 : word) = Some W_a7458.
Proof. vm_refl. Qed.
Lemma D_a7458 : decode_any W_a7458 = Some (Branch BC_EQ 29 13 1612, 4%Z).
Proof. vm_refl. Qed.

Definition W_a745c : bv 32 := 0x05013683.
Lemma F_a745c : fetch_word Ubsan.M.loaded_segments (0xa745c : word) = Some W_a745c.
Proof. vm_refl. Qed.
Lemma D_a745c : decode_any W_a745c = Some (Load SZ8 true 13 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7460 : bv 32 := 0x00dd36b3.
Lemma F_a7460 : fetch_word Ubsan.M.loaded_segments (0xa7460 : word) = Some W_a7460.
Proof. vm_refl. Qed.
Lemma D_a7460 : decode_any W_a7460 = Some (Op ALU_SLTU 13 26 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7464 : bv 32 := 0x00062613.
Lemma F_a7464 : fetch_word Ubsan.M.loaded_segments (0xa7464 : word) = Some W_a7464.
Proof. vm_refl. Qed.
Lemma D_a7464 : decode_any W_a7464 = Some (OpImm ALU_SLT 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7468 : bv 32 := 0x00c6c633.
Lemma F_a7468 : fetch_word Ubsan.M.loaded_segments (0xa7468 : word) = Some W_a7468.
Proof. vm_refl. Qed.
Lemma D_a7468 : decode_any W_a7468 = Some (Op ALU_XOR 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a746c : bv 32 := 0x00164613.
Lemma F_a746c : fetch_word Ubsan.M.loaded_segments (0xa746c : word) = Some W_a746c.
Proof. vm_refl. Qed.
Lemma D_a746c : decode_any W_a746c = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7470 : bv 32 := 0x62060a63.
Lemma F_a7470 : fetch_word Ubsan.M.loaded_segments (0xa7470 : word) = Some W_a7470.
Proof. vm_refl. Qed.
Lemma D_a7470 : decode_any W_a7470 = Some (Branch BC_EQ 12 0 1588, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7474 : bv 32 := 0x02a88633.
Lemma F_a7474 : fetch_word Ubsan.M.loaded_segments (0xa7474 : word) = Some W_a7474.
Proof. vm_refl. Qed.
Lemma D_a7474 : decode_any W_a7474 = Some (Mul M_MUL 12 17 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7478 : bv 32 := 0x02a886bb.
Lemma F_a7478 : fetch_word Ubsan.M.loaded_segments (0xa7478 : word) = Some W_a7478.
Proof. vm_refl. Qed.
Lemma D_a7478 : decode_any W_a7478 = Some (Mul32 M_MUL 13 17 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a747c : bv 32 := 0x62c69463.
Lemma F_a747c : fetch_word Ubsan.M.loaded_segments (0xa747c : word) = Some W_a747c.
Proof. vm_refl. Qed.
Lemma D_a747c : decode_any W_a747c = Some (Branch BC_NE 13 12 1576, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7480 : bv 32 := 0x01203db3.
Lemma F_a7480 : fetch_word Ubsan.M.loaded_segments (0xa7480 : word) = Some W_a7480.
Proof. vm_refl. Qed.
Lemma D_a7480 : decode_any W_a7480 = Some (Op ALU_SLTU 27 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7484 : bv 32 := 0x0006061b.
Lemma F_a7484 : fetch_word Ubsan.M.loaded_segments (0xa7484 : word) = Some W_a7484.
Proof. vm_refl. Qed.
Lemma D_a7484 : decode_any W_a7484 = Some (OpImm32 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7488 : bv 32 := 0x00261093.
Lemma F_a7488 : fetch_word Ubsan.M.loaded_segments (0xa7488 : word) = Some W_a7488.
Proof. vm_refl. Qed.
Lemma D_a7488 : decode_any W_a7488 = Some (ShiftImm ALU_SLL 1 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a748c : bv 32 := 0x001900b3.
Lemma F_a748c : fetch_word Ubsan.M.loaded_segments (0xa748c : word) = Some W_a748c.
Proof. vm_refl. Qed.
Lemma D_a748c : decode_any W_a748c = Some (Op ALU_ADD 1 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7490 : bv 32 := 0x0010b693.
Lemma F_a7490 : fetch_word Ubsan.M.loaded_segments (0xa7490 : word) = Some W_a7490.
Proof. vm_refl. Qed.
Lemma D_a7490 : decode_any W_a7490 = Some (OpImm ALU_SLTU 13 1 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7494 : bv 32 := 0x60dd8863.
Lemma F_a7494 : fetch_word Ubsan.M.loaded_segments (0xa7494 : word) = Some W_a7494.
Proof. vm_refl. Qed.
Lemma D_a7494 : decode_any W_a7494 = Some (Branch BC_EQ 27 13 1552, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7498 : bv 32 := 0x0120b6b3.
Lemma F_a7498 : fetch_word Ubsan.M.loaded_segments (0xa7498 : word) = Some W_a7498.
Proof. vm_refl. Qed.
Lemma D_a7498 : decode_any W_a7498 = Some (Op ALU_SLTU 13 1 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_a749c : bv 32 := 0x00062613.
Lemma F_a749c : fetch_word Ubsan.M.loaded_segments (0xa749c : word) = Some W_a749c.
Proof. vm_refl. Qed.
Lemma D_a749c : decode_any W_a749c = Some (OpImm ALU_SLT 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a74a0 : bv 32 := 0x00c6c633.
Lemma F_a74a0 : fetch_word Ubsan.M.loaded_segments (0xa74a0 : word) = Some W_a74a0.
Proof. vm_refl. Qed.
Lemma D_a74a0 : decode_any W_a74a0 = Some (Op ALU_XOR 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a74a4 : bv 32 := 0x00164613.
Lemma F_a74a4 : fetch_word Ubsan.M.loaded_segments (0xa74a4 : word) = Some W_a74a4.
Proof. vm_refl. Qed.
Lemma D_a74a4 : decode_any W_a74a4 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a74a8 : bv 32 := 0x5e060e63.
Lemma F_a74a8 : fetch_word Ubsan.M.loaded_segments (0xa74a8 : word) = Some W_a74a8.
Proof. vm_refl. Qed.
Lemma D_a74a8 : decode_any W_a74a8 = Some (Branch BC_EQ 12 0 1532, 4%Z).
Proof. vm_refl. Qed.

Definition W_a74ac : bv 32 := 0x04013603.
Lemma F_a74ac : fetch_word Ubsan.M.loaded_segments (0xa74ac : word) = Some W_a74ac.
Proof. vm_refl. Qed.
Lemma D_a74ac : decode_any W_a74ac = Some (Load SZ8 true 12 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a74b0 : bv 32 := 0x10c05863.
Lemma F_a74b0 : fetch_word Ubsan.M.loaded_segments (0xa74b0 : word) = Some W_a74b0.
Proof. vm_refl. Qed.
Lemma D_a74b0 : decode_any W_a74b0 = Some (Branch BC_GE 0 12 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_a74b4 : bv 32 := 0x00000a93.
Lemma F_a74b4 : fetch_word Ubsan.M.loaded_segments (0xa74b4 : word) = Some W_a74b4.
Proof. vm_refl. Qed.
Lemma D_a74b4 : decode_any W_a74b4 = Some (OpImm ALU_ADD 21 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a74b8 : bv 32 := 0x00281993.
Lemma F_a74b8 : fetch_word Ubsan.M.loaded_segments (0xa74b8 : word) = Some W_a74b8.
Proof. vm_refl. Qed.
Lemma D_a74b8 : decode_any W_a74b8 = Some (ShiftImm ALU_SLL 19 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a74bc : bv 32 := 0x00279c93.
Lemma F_a74bc : fetch_word Ubsan.M.loaded_segments (0xa74bc : word) = Some W_a74bc.
Proof. vm_refl. Qed.
Lemma D_a74bc : decode_any W_a74bc = Some (ShiftImm ALU_SLL 25 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a74c0 : bv 32 := 0x04813603.
Lemma F_a74c0 : fetch_word Ubsan.M.loaded_segments (0xa74c0 : word) = Some W_a74c0.
Proof. vm_refl. Qed.
Lemma D_a74c0 : decode_any W_a74c0 = Some (Load SZ8 true 12 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a74c4 : bv 32 := 0x00062613.
Lemma F_a74c4 : fetch_word Ubsan.M.loaded_segments (0xa74c4 : word) = Some W_a74c4.
Proof. vm_refl. Qed.
Lemma D_a74c4 : decode_any W_a74c4 = Some (OpImm ALU_SLT 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a74c8 : bv 32 := 0x02013683.
Lemma F_a74c8 : fetch_word Ubsan.M.loaded_segments (0xa74c8 : word) = Some W_a74c8.
Proof. vm_refl. Qed.
Lemma D_a74c8 : decode_any W_a74c8 = Some (Load SZ8 true 13 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a74cc : bv 32 := 0x01a686b3.
Lemma F_a74cc : fetch_word Ubsan.M.loaded_segments (0xa74cc : word) = Some W_a74cc.
Proof. vm_refl. Qed.
Lemma D_a74cc : decode_any W_a74cc = Some (Op ALU_ADD 13 13 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_a74d0 : bv 32 := 0x01813703.
Lemma F_a74d0 : fetch_word Ubsan.M.loaded_segments (0xa74d0 : word) = Some W_a74d0.
Proof. vm_refl. Qed.
Lemma D_a74d0 : decode_any W_a74d0 = Some (Load SZ8 true 14 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a74d4 : bv 32 := 0x00ed0733.
Lemma F_a74d4 : fetch_word Ubsan.M.loaded_segments (0xa74d4 : word) = Some W_a74d4.
Proof. vm_refl. Qed.
Lemma D_a74d4 : decode_any W_a74d4 = Some (Op ALU_ADD 14 26 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_a74d8 : bv 32 := 0x013909b3.
Lemma F_a74d8 : fetch_word Ubsan.M.loaded_segments (0xa74d8 : word) = Some W_a74d8.
Proof. vm_refl. Qed.
Lemma D_a74d8 : decode_any W_a74d8 = Some (Op ALU_ADD 19 18 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_a74dc : bv 32 := 0x05013483.
Lemma F_a74dc : fetch_word Ubsan.M.loaded_segments (0xa74dc : word) = Some W_a74dc.
Proof. vm_refl. Qed.
Lemma D_a74dc : decode_any W_a74dc = Some (Load SZ8 true 9 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a74e0 : bv 32 := 0x019484b3.
Lemma F_a74e0 : fetch_word Ubsan.M.loaded_segments (0xa74e0 : word) = Some W_a74e0.
Proof. vm_refl. Qed.
Lemma D_a74e0 : decode_any W_a74e0 = Some (Op ALU_ADD 9 9 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_a74e4 : bv 32 := 0x01013303.
Lemma F_a74e4 : fetch_word Ubsan.M.loaded_segments (0xa74e4 : word) = Some W_a74e4.
Proof. vm_refl. Qed.
Lemma D_a74e4 : decode_any W_a74e4 = Some (Load SZ8 true 6 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a74e8 : bv 32 := 0x01930cb3.
Lemma F_a74e8 : fetch_word Ubsan.M.loaded_segments (0xa74e8 : word) = Some W_a74e8.
Proof. vm_refl. Qed.
Lemma D_a74e8 : decode_any W_a74e8 = Some (Op ALU_ADD 25 6 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_a74ec : bv 32 := 0x00d03f33.
Lemma F_a74ec : fetch_word Ubsan.M.loaded_segments (0xa74ec : word) = Some W_a74ec.
Proof. vm_refl. Qed.
Lemma D_a74ec : decode_any W_a74ec = Some (Op ALU_SLTU 30 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a74f0 : bv 32 := 0x01a6b6b3.
Lemma F_a74f0 : fetch_word Ubsan.M.loaded_segments (0xa74f0 : word) = Some W_a74f0.
Proof. vm_refl. Qed.
Lemma D_a74f0 : decode_any W_a74f0 = Some (Op ALU_SLTU 13 13 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_a74f4 : bv 32 := 0x00c6c633.
Lemma F_a74f4 : fetch_word Ubsan.M.loaded_segments (0xa74f4 : word) = Some W_a74f4.
Proof. vm_refl. Qed.
Lemma D_a74f4 : decode_any W_a74f4 = Some (Op ALU_XOR 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a74f8 : bv 32 := 0x00164613.
Lemma F_a74f8 : fetch_word Ubsan.M.loaded_segments (0xa74f8 : word) = Some W_a74f8.
Proof. vm_refl. Qed.
Lemma D_a74f8 : decode_any W_a74f8 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a74fc : bv 32 := 0x00cf7633.
Lemma F_a74fc : fetch_word Ubsan.M.loaded_segments (0xa74fc : word) = Some W_a74fc.
Proof. vm_refl. Qed.
Lemma D_a74fc : decode_any W_a74fc = Some (Op ALU_AND 12 30 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7500 : bv 32 := 0xfff74f93.
Lemma F_a7500 : fetch_word Ubsan.M.loaded_segments (0xa7500 : word) = Some W_a7500.
Proof. vm_refl. Qed.
Lemma D_a7500 : decode_any W_a7500 = Some (OpImm ALU_XOR 31 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7504 : bv 32 := 0x04013683.
Lemma F_a7504 : fetch_word Ubsan.M.loaded_segments (0xa7504 : word) = Some W_a7504.
Proof. vm_refl. Qed.
Lemma D_a7504 : decode_any W_a7504 = Some (Load SZ8 true 13 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7508 : bv 32 := 0x00098f13.
Lemma F_a7508 : fetch_word Ubsan.M.loaded_segments (0xa7508 : word) = Some W_a7508.
Proof. vm_refl. Qed.
Lemma D_a7508 : decode_any W_a7508 = Some (OpImm ALU_ADD 30 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a750c : bv 32 := 0x01548433.
Lemma F_a750c : fetch_word Ubsan.M.loaded_segments (0xa750c : word) = Some W_a750c.
Proof. vm_refl. Qed.
Lemma D_a750c : decode_any W_a750c = Some (Op ALU_ADD 8 9 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7510 : bv 32 := 0x59a46a63.
Lemma F_a7510 : fetch_word Ubsan.M.loaded_segments (0xa7510 : word) = Some W_a7510.
Proof. vm_refl. Qed.
Lemma D_a7510 : decode_any W_a7510 = Some (Branch BC_LTU 8 26 1428, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7514 : bv 32 := 0x00143713.
Lemma F_a7514 : fetch_word Ubsan.M.loaded_segments (0xa7514 : word) = Some W_a7514.
Proof. vm_refl. Qed.
Lemma D_a7514 : decode_any W_a7514 = Some (OpImm ALU_SLTU 14 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7518 : bv 32 := 0x00eec733.
Lemma F_a7518 : fetch_word Ubsan.M.loaded_segments (0xa7518 : word) = Some W_a7518.
Proof. vm_refl. Qed.
Lemma D_a7518 : decode_any W_a7518 = Some (Op ALU_XOR 14 29 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_a751c : bv 32 := 0x58070463.
Lemma F_a751c : fetch_word Ubsan.M.loaded_segments (0xa751c : word) = Some W_a751c.
Proof. vm_refl. Qed.
Lemma D_a751c : decode_any W_a751c = Some (Branch BC_EQ 14 0 1416, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7520 : bv 32 := 0x580c0263.
Lemma F_a7520 : fetch_word Ubsan.M.loaded_segments (0xa7520 : word) = Some W_a7520.
Proof. vm_refl. Qed.
Lemma D_a7520 : decode_any W_a7520 = Some (Branch BC_EQ 24 0 1412, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7524 : bv 32 := 0x58060063.
Lemma F_a7524 : fetch_word Ubsan.M.loaded_segments (0xa7524 : word) = Some W_a7524.
Proof. vm_refl. Qed.
Lemma D_a7524 : decode_any W_a7524 = Some (Branch BC_EQ 12 0 1408, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7528 : bv 32 := 0x575fee63.
Lemma F_a7528 : fetch_word Ubsan.M.loaded_segments (0xa7528 : word) = Some W_a7528.
Proof. vm_refl. Qed.
Lemma D_a7528 : decode_any W_a7528 = Some (Branch BC_LTU 31 21 1404, 4%Z).
Proof. vm_refl. Qed.

Definition W_a752c : bv 32 := 0x015c8733.
Lemma F_a752c : fetch_word Ubsan.M.loaded_segments (0xa752c : word) = Some W_a752c.
Proof. vm_refl. Qed.
Lemma D_a752c : decode_any W_a752c = Some (Op ALU_ADD 14 25 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7530 : bv 32 := 0x00042403.
Lemma F_a7530 : fetch_word Ubsan.M.loaded_segments (0xa7530 : word) = Some W_a7530.
Proof. vm_refl. Qed.
Lemma D_a7530 : decode_any W_a7530 = Some (Load SZ4 true 8 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7534 : bv 32 := 0x00072703.
Lemma F_a7534 : fetch_word Ubsan.M.loaded_segments (0xa7534 : word) = Some W_a7534.
Proof. vm_refl. Qed.
Lemma D_a7534 : decode_any W_a7534 = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7538 : bv 32 := 0x00877bb3.
Lemma F_a7538 : fetch_word Ubsan.M.loaded_segments (0xa7538 : word) = Some W_a7538.
Proof. vm_refl. Qed.
Lemma D_a7538 : decode_any W_a7538 = Some (Op ALU_AND 23 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a753c : bv 32 := 0x00876733.
Lemma F_a753c : fetch_word Ubsan.M.loaded_segments (0xa753c : word) = Some W_a753c.
Proof. vm_refl. Qed.
Lemma D_a753c : decode_any W_a753c = Some (Op ALU_OR 14 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7540 : bv 32 := 0x001b9413.
Lemma F_a7540 : fetch_word Ubsan.M.loaded_segments (0xa7540 : word) = Some W_a7540.
Proof. vm_refl. Qed.
Lemma D_a7540 : decode_any W_a7540 = Some (ShiftImm ALU_SLL 8 23 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7544 : bv 32 := 0x00171313.
Lemma F_a7544 : fetch_word Ubsan.M.loaded_segments (0xa7544 : word) = Some W_a7544.
Proof. vm_refl. Qed.
Lemma D_a7544 : decode_any W_a7544 = Some (ShiftImm ALU_SLL 6 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7548 : bv 32 := 0x01677733.
Lemma F_a7548 : fetch_word Ubsan.M.loaded_segments (0xa7548 : word) = Some W_a7548.
Proof. vm_refl. Qed.
Lemma D_a7548 : decode_any W_a7548 = Some (Op ALU_AND 14 14 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_a754c : bv 32 := 0x01746433.
Lemma F_a754c : fetch_word Ubsan.M.loaded_segments (0xa754c : word) = Some W_a754c.
Proof. vm_refl. Qed.
Lemma D_a754c : decode_any W_a754c = Some (Op ALU_OR 8 8 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7550 : bv 32 := 0x00677733.
Lemma F_a7550 : fetch_word Ubsan.M.loaded_segments (0xa7550 : word) = Some W_a7550.
Proof. vm_refl. Qed.
Lemma D_a7550 : decode_any W_a7550 = Some (Op ALU_AND 14 14 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7554 : bv 32 := 0x00877733.
Lemma F_a7554 : fetch_word Ubsan.M.loaded_segments (0xa7554 : word) = Some W_a7554.
Proof. vm_refl. Qed.
Lemma D_a7554 : decode_any W_a7554 = Some (Op ALU_AND 14 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7558 : bv 32 := 0x00771b93.
Lemma F_a7558 : fetch_word Ubsan.M.loaded_segments (0xa7558 : word) = Some W_a7558.
Proof. vm_refl. Qed.
Lemma D_a7558 : decode_any W_a7558 = Some (ShiftImm ALU_SLL 23 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_a755c : bv 32 := 0x00eb8bb3.
Lemma F_a755c : fetch_word Ubsan.M.loaded_segments (0xa755c : word) = Some W_a755c.
Proof. vm_refl. Qed.
Lemma D_a755c : decode_any W_a755c = Some (Op ALU_ADD 23 23 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7560 : bv 32 := 0x018bd41b.
Lemma F_a7560 : fetch_word Ubsan.M.loaded_segments (0xa7560 : word) = Some W_a7560.
Proof. vm_refl. Qed.
Lemma D_a7560 : decode_any W_a7560 = Some (ShiftImm32 ALU_SRL 8 23 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7564 : bv 32 := 0x5483e063.
Lemma F_a7564 : fetch_word Ubsan.M.loaded_segments (0xa7564 : word) = Some W_a7564.
Proof. vm_refl. Qed.
Lemma D_a7564 : decode_any W_a7564 = Some (Branch BC_LTU 7 8 1344, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7568 : bv 32 := 0x030b9b93.
Lemma F_a7568 : fetch_word Ubsan.M.loaded_segments (0xa7568 : word) = Some W_a7568.
Proof. vm_refl. Qed.
Lemma D_a7568 : decode_any W_a7568 = Some (ShiftImm ALU_SLL 23 23 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a756c : bv 32 := 0x038bdb93.
Lemma F_a756c : fetch_word Ubsan.M.loaded_segments (0xa756c : word) = Some W_a756c.
Proof. vm_refl. Qed.
Lemma D_a756c : decode_any W_a756c = Some (ShiftImm ALU_SRL 23 23 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7570 : bv 32 := 0x5373ea63.
Lemma F_a7570 : fetch_word Ubsan.M.loaded_segments (0xa7570 : word) = Some W_a7570.
Proof. vm_refl. Qed.
Lemma D_a7570 : decode_any W_a7570 = Some (Branch BC_LTU 7 23 1332, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7574 : bv 32 := 0x521f6863.
Lemma F_a7574 : fetch_word Ubsan.M.loaded_segments (0xa7574 : word) = Some W_a7574.
Proof. vm_refl. Qed.
Lemma D_a7574 : decode_any W_a7574 = Some (Branch BC_LTU 30 1 1328, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7578 : bv 32 := 0x001f3713.
Lemma F_a7578 : fetch_word Ubsan.M.loaded_segments (0xa7578 : word) = Some W_a7578.
Proof. vm_refl. Qed.
Lemma D_a7578 : decode_any W_a7578 = Some (OpImm ALU_SLTU 14 30 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a757c : bv 32 := 0x00edc733.
Lemma F_a757c : fetch_word Ubsan.M.loaded_segments (0xa757c : word) = Some W_a757c.
Proof. vm_refl. Qed.
Lemma D_a757c : decode_any W_a757c = Some (Op ALU_XOR 14 27 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7580 : bv 32 := 0x52070263.
Lemma F_a7580 : fetch_word Ubsan.M.loaded_segments (0xa7580 : word) = Some W_a7580.
Proof. vm_refl. Qed.
Lemma D_a7580 : decode_any W_a7580 = Some (Branch BC_EQ 14 0 1316, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7584 : bv 32 := 0x520e1063.
Lemma F_a7584 : fetch_word Ubsan.M.loaded_segments (0xa7584 : word) = Some W_a7584.
Proof. vm_refl. Qed.
Lemma D_a7584 : decode_any W_a7584 = Some (Branch BC_NE 28 0 1312, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7588 : bv 32 := 0x51498e63.
Lemma F_a7588 : fetch_word Ubsan.M.loaded_segments (0xa7588 : word) = Some W_a7588.
Proof. vm_refl. Qed.
Lemma D_a7588 : decode_any W_a7588 = Some (Branch BC_EQ 19 20 1308, 4%Z).
Proof. vm_refl. Qed.

Definition W_a758c : bv 32 := 0x01758bb3.
Lemma F_a758c : fetch_word Ubsan.M.loaded_segments (0xa758c : word) = Some W_a758c.
Proof. vm_refl. Qed.
Lemma D_a758c : decode_any W_a758c = Some (Op ALU_ADD 23 11 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7590 : bv 32 := 0x00858433.
Lemma F_a7590 : fetch_word Ubsan.M.loaded_segments (0xa7590 : word) = Some W_a7590.
Proof. vm_refl. Qed.
Lemma D_a7590 : decode_any W_a7590 = Some (Op ALU_ADD 8 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7594 : bv 32 := 0x00044703.
Lemma F_a7594 : fetch_word Ubsan.M.loaded_segments (0xa7594 : word) = Some W_a7594.
Proof. vm_refl. Qed.
Lemma D_a7594 : decode_any W_a7594 = Some (Load SZ1 false 14 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7598 : bv 32 := 0x000bc303.
Lemma F_a7598 : fetch_word Ubsan.M.loaded_segments (0xa7598 : word) = Some W_a7598.
Proof. vm_refl. Qed.
Lemma D_a7598 : decode_any W_a7598 = Some (Load SZ1 false 6 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a759c : bv 32 := 0x00871713.
Lemma F_a759c : fetch_word Ubsan.M.loaded_segments (0xa759c : word) = Some W_a759c.
Proof. vm_refl. Qed.
Lemma D_a759c : decode_any W_a759c = Some (ShiftImm ALU_SLL 14 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a75a0 : bv 32 := 0x00676733.
Lemma F_a75a0 : fetch_word Ubsan.M.loaded_segments (0xa75a0 : word) = Some W_a75a0.
Proof. vm_refl. Qed.
Lemma D_a75a0 : decode_any W_a75a0 = Some (Op ALU_OR 14 14 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_a75a4 : bv 32 := 0x002f4313.
Lemma F_a75a4 : fetch_word Ubsan.M.loaded_segments (0xa75a4 : word) = Some W_a75a4.
Proof. vm_refl. Qed.
Lemma D_a75a4 : decode_any W_a75a4 = Some (OpImm ALU_XOR 6 30 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a75a8 : bv 32 := 0x002f0f13.
Lemma F_a75a8 : fetch_word Ubsan.M.loaded_segments (0xa75a8 : word) = Some W_a75a8.
Proof. vm_refl. Qed.
Lemma D_a75a8 : decode_any W_a75a8 = Some (OpImm ALU_ADD 30 30 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a75ac : bv 32 := 0x004a8a93.
Lemma F_a75ac : fetch_word Ubsan.M.loaded_segments (0xa75ac : word) = Some W_a75ac.
Proof. vm_refl. Qed.
Lemma D_a75ac : decode_any W_a75ac = Some (OpImm ALU_ADD 21 21 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a75b0 : bv 32 := 0xfff68693.
Lemma F_a75b0 : fetch_word Ubsan.M.loaded_segments (0xa75b0 : word) = Some W_a75b0.
Proof. vm_refl. Qed.
Lemma D_a75b0 : decode_any W_a75b0 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a75b4 : bv 32 := 0x00e31023.
Lemma F_a75b4 : fetch_word Ubsan.M.loaded_segments (0xa75b4 : word) = Some W_a75b4.
Proof. vm_refl. Qed.
Lemma D_a75b4 : decode_any W_a75b4 = Some (Store SZ2 6 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a75b8 : bv 32 := 0x00298993.
Lemma F_a75b8 : fetch_word Ubsan.M.loaded_segments (0xa75b8 : word) = Some W_a75b8.
Proof. vm_refl. Qed.
Lemma D_a75b8 : decode_any W_a75b8 = Some (OpImm ALU_ADD 19 19 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a75bc : bv 32 := 0xf40698e3.
Lemma F_a75bc : fetch_word Ubsan.M.loaded_segments (0xa75bc : word) = Some W_a75bc.
Proof. vm_refl. Qed.
Lemma D_a75bc : decode_any W_a75bc = Some (Branch BC_NE 13 0 8016, 4%Z).
Proof. vm_refl. Qed.

Definition W_a75c0 : bv 32 := 0x03013603.
Lemma F_a75c0 : fetch_word Ubsan.M.loaded_segments (0xa75c0 : word) = Some W_a75c0.
Proof. vm_refl. Qed.
Lemma D_a75c0 : decode_any W_a75c0 = Some (Load SZ8 true 12 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a75c4 : bv 32 := 0x4ec88063.
Lemma F_a75c4 : fetch_word Ubsan.M.loaded_segments (0xa75c4 : word) = Some W_a75c4.
Proof. vm_refl. Qed.
Lemma D_a75c4 : decode_any W_a75c4 = Some (Branch BC_EQ 17 12 1248, 4%Z).
Proof. vm_refl. Qed.

Definition W_a75c8 : bv 32 := 0x0022829b.
Lemma F_a75c8 : fetch_word Ubsan.M.loaded_segments (0xa75c8 : word) = Some W_a75c8.
Proof. vm_refl. Qed.
Lemma D_a75c8 : decode_any W_a75c8 = Some (OpImm32 5 5 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a75cc : bv 32 := 0x0018889b.
Lemma F_a75cc : fetch_word Ubsan.M.loaded_segments (0xa75cc : word) = Some W_a75cc.
Proof. vm_refl. Qed.
Lemma D_a75cc : decode_any W_a75cc = Some (OpImm32 17 17 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a75d0 : bv 32 := 0x00a8083b.
Lemma F_a75d0 : fetch_word Ubsan.M.loaded_segments (0xa75d0 : word) = Some W_a75d0.
Proof. vm_refl. Qed.
Lemma D_a75d0 : decode_any W_a75d0 = Some (Op32 ALU_ADD 16 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a75d4 : bv 32 := 0x02813603.
Lemma F_a75d4 : fetch_word Ubsan.M.loaded_segments (0xa75d4 : word) = Some W_a75d4.
Proof. vm_refl. Qed.
Lemma D_a75d4 : decode_any W_a75d4 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a75d8 : bv 32 := 0x00c787bb.
Lemma F_a75d8 : fetch_word Ubsan.M.loaded_segments (0xa75d8 : word) = Some W_a75d8.
Proof. vm_refl. Qed.
Lemma D_a75d8 : decode_any W_a75d8 = Some (Op32 ALU_ADD 15 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a75dc : bv 32 := 0x03813603.
Lemma F_a75dc : fetch_word Ubsan.M.loaded_segments (0xa75dc : word) = Some W_a75dc.
Proof. vm_refl. Qed.
Lemma D_a75dc : decode_any W_a75dc = Some (Load SZ8 true 12 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a75e0 : bv 32 := 0xe4c2cae3.
Lemma F_a75e0 : fetch_word Ubsan.M.loaded_segments (0xa75e0 : word) = Some W_a75e0.
Proof. vm_refl. Qed.
Lemma D_a75e0 : decode_any W_a75e0 = Some (Branch BC_LT 5 12 7764, 4%Z).
Proof. vm_refl. Qed.

Definition W_a75e4 : bv 32 := 0x4380006f.
Lemma F_a75e4 : fetch_word Ubsan.M.loaded_segments (0xa75e4 : word) = Some W_a75e4.
Proof. vm_refl. Qed.
Lemma D_a75e4 : decode_any W_a75e4 = Some (Jal 0 1080, 4%Z).
Proof. vm_refl. Qed.

Definition W_a75e8 : bv 32 := 0x4a061e63.
Lemma F_a75e8 : fetch_word Ubsan.M.loaded_segments (0xa75e8 : word) = Some W_a75e8.
Proof. vm_refl. Qed.
Lemma D_a75e8 : decode_any W_a75e8 = Some (Branch BC_NE 12 0 1212, 4%Z).
Proof. vm_refl. Qed.

Definition W_a75ec : bv 32 := 0x03813603.
Lemma F_a75ec : fetch_word Ubsan.M.loaded_segments (0xa75ec : word) = Some W_a75ec.
Proof. vm_refl. Qed.
Lemma D_a75ec : decode_any W_a75ec = Some (Load SZ8 true 12 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a75f0 : bv 32 := 0x42c05663.
Lemma F_a75f0 : fetch_word Ubsan.M.loaded_segments (0xa75f0 : word) = Some W_a75f0.
Proof. vm_refl. Qed.
Lemma D_a75f0 : decode_any W_a75f0 = Some (Branch BC_GE 0 12 1068, 4%Z).
Proof. vm_refl. Qed.

Definition W_a75f4 : bv 32 := 0x00000793.
Lemma F_a75f4 : fetch_word Ubsan.M.loaded_segments (0xa75f4 : word) = Some W_a75f4.
Proof. vm_refl. Qed.
Lemma D_a75f4 : decode_any W_a75f4 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a75f8 : bv 32 := 0x00000813.
Lemma F_a75f8 : fetch_word Ubsan.M.loaded_segments (0xa75f8 : word) = Some W_a75f8.
Proof. vm_refl. Qed.
Lemma D_a75f8 : decode_any W_a75f8 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a75fc : bv 32 := 0x00000893.
Lemma F_a75fc : fetch_word Ubsan.M.loaded_segments (0xa75fc : word) = Some W_a75fc.
Proof. vm_refl. Qed.
Lemma D_a75fc : decode_any W_a75fc = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7600 : bv 32 := 0x00000293.
Lemma F_a7600 : fetch_word Ubsan.M.loaded_segments (0xa7600 : word) = Some W_a7600.
Proof. vm_refl. Qed.
Lemma D_a7600 : decode_any W_a7600 = Some (OpImm ALU_ADD 5 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7604 : bv 32 := 0x04813703.
Lemma F_a7604 : fetch_word Ubsan.M.loaded_segments (0xa7604 : word) = Some W_a7604.
Proof. vm_refl. Qed.
Lemma D_a7604 : decode_any W_a7604 = Some (Load SZ8 true 14 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7608 : bv 32 := 0x00271613.
Lemma F_a7608 : fetch_word Ubsan.M.loaded_segments (0xa7608 : word) = Some W_a7608.
Proof. vm_refl. Qed.
Lemma D_a7608 : decode_any W_a7608 = Some (ShiftImm ALU_SLL 12 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a760c : bv 32 := 0x02c13023.
Lemma F_a760c : fetch_word Ubsan.M.loaded_segments (0xa760c : word) = Some W_a760c.
Proof. vm_refl. Qed.
Lemma D_a760c : decode_any W_a760c = Some (Store SZ8 2 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7610 : bv 32 := 0xfff5c393.
Lemma F_a7610 : fetch_word Ubsan.M.loaded_segments (0xa7610 : word) = Some W_a7610.
Proof. vm_refl. Qed.
Lemma D_a7610 : decode_any W_a7610 = Some (OpImm ALU_XOR 7 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7614 : bv 32 := 0x05013303.
Lemma F_a7614 : fetch_word Ubsan.M.loaded_segments (0xa7614 : word) = Some W_a7614.
Proof. vm_refl. Qed.
Lemma D_a7614 : decode_any W_a7614 = Some (Load SZ8 true 6 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7618 : bv 32 := 0x00337613.
Lemma F_a7618 : fetch_word Ubsan.M.loaded_segments (0xa7618 : word) = Some W_a7618.
Proof. vm_refl. Qed.
Lemma D_a7618 : decode_any W_a7618 = Some (OpImm ALU_AND 12 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a761c : bv 32 := 0x00197e13.
Lemma F_a761c : fetch_word Ubsan.M.loaded_segments (0xa761c : word) = Some W_a761c.
Proof. vm_refl. Qed.
Lemma D_a761c : decode_any W_a761c = Some (OpImm ALU_AND 28 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7620 : bv 32 := 0x00603eb3.
Lemma F_a7620 : fetch_word Ubsan.M.loaded_segments (0xa7620 : word) = Some W_a7620.
Proof. vm_refl. Qed.
Lemma D_a7620 : decode_any W_a7620 = Some (Op ALU_SLTU 29 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7624 : bv 32 := 0xaaaab6b7.
Lemma F_a7624 : fetch_word Ubsan.M.loaded_segments (0xa7624 : word) = Some W_a7624.
Proof. vm_refl. Qed.
Lemma D_a7624 : decode_any W_a7624 = Some (Lui 13 699051, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7628 : bv 32 := 0x00171f13.
Lemma F_a7628 : fetch_word Ubsan.M.loaded_segments (0xa7628 : word) = Some W_a7628.
Proof. vm_refl. Qed.
Lemma D_a7628 : decode_any W_a7628 = Some (ShiftImm ALU_SLL 30 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a762c : bv 32 := 0x03e13423.
Lemma F_a762c : fetch_word Ubsan.M.loaded_segments (0xa762c : word) = Some W_a762c.
Proof. vm_refl. Qed.
Lemma D_a762c : decode_any W_a762c = Some (Store SZ8 2 30 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7630 : bv 32 := 0x00271713.
Lemma F_a7630 : fetch_word Ubsan.M.loaded_segments (0xa7630 : word) = Some W_a7630.
Proof. vm_refl. Qed.
Lemma D_a7630 : decode_any W_a7630 = Some (ShiftImm ALU_SLL 14 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7634 : bv 32 := 0x00200a13.
Lemma F_a7634 : fetch_word Ubsan.M.loaded_segments (0xa7634 : word) = Some W_a7634.
Proof. vm_refl. Qed.
Lemma D_a7634 : decode_any W_a7634 = Some (OpImm ALU_ADD 20 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7638 : bv 32 := 0x400004b7.
Lemma F_a7638 : fetch_word Ubsan.M.loaded_segments (0xa7638 : word) = Some W_a7638.
Proof. vm_refl. Qed.
Lemma D_a7638 : decode_any W_a7638 = Some (Lui 9 262144, 4%Z).
Proof. vm_refl. Qed.

Definition W_a763c : bv 32 := 0x00163613.
Lemma F_a763c : fetch_word Ubsan.M.loaded_segments (0xa763c : word) = Some W_a763c.
Proof. vm_refl. Qed.
Lemma D_a763c : decode_any W_a763c = Some (OpImm ALU_SLTU 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7640 : bv 32 := 0xaaa68b13.
Lemma F_a7640 : fetch_word Ubsan.M.loaded_segments (0xa7640 : word) = Some W_a7640.
Proof. vm_refl. Qed.
Lemma D_a7640 : decode_any W_a7640 = Some (OpImm ALU_ADD 22 13 2730, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7644 : bv 32 := 0x00e13c23.
Lemma F_a7644 : fetch_word Ubsan.M.loaded_segments (0xa7644 : word) = Some W_a7644.
Proof. vm_refl. Qed.
Lemma D_a7644 : decode_any W_a7644 = Some (Store SZ8 2 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7648 : bv 32 := 0x00e30733.
Lemma F_a7648 : fetch_word Ubsan.M.loaded_segments (0xa7648 : word) = Some W_a7648.
Proof. vm_refl. Qed.
Lemma D_a7648 : decode_any W_a7648 = Some (Op ALU_ADD 14 6 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_a764c : bv 32 := 0x00e13823.
Lemma F_a764c : fetch_word Ubsan.M.loaded_segments (0xa764c : word) = Some W_a764c.
Proof. vm_refl. Qed.
Lemma D_a764c : decode_any W_a764c = Some (Store SZ8 2 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7650 : bv 32 := 0x01d67c33.
Lemma F_a7650 : fetch_word Ubsan.M.loaded_segments (0xa7650 : word) = Some W_a7650.
Proof. vm_refl. Qed.
Lemma D_a7650 : decode_any W_a7650 = Some (Op ALU_AND 24 12 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7654 : bv 32 := 0xfff4849b.
Lemma F_a7654 : fetch_word Ubsan.M.loaded_segments (0xa7654 : word) = Some W_a7654.
Proof. vm_refl. Qed.
Lemma D_a7654 : decode_any W_a7654 = Some (OpImm32 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7658 : bv 32 := 0x02913823.
Lemma F_a7658 : fetch_word Ubsan.M.loaded_segments (0xa7658 : word) = Some W_a7658.
Proof. vm_refl. Qed.
Lemma D_a7658 : decode_any W_a7658 = Some (Store SZ8 2 9 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a765c : bv 32 := 0x04813683.
Lemma F_a765c : fetch_word Ubsan.M.loaded_segments (0xa765c : word) = Some W_a765c.
Proof. vm_refl. Qed.
Lemma D_a765c : decode_any W_a765c = Some (Load SZ8 true 13 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7660 : bv 32 := 0x02d28633.
Lemma F_a7660 : fetch_word Ubsan.M.loaded_segments (0xa7660 : word) = Some W_a7660.
Proof. vm_refl. Qed.
Lemma D_a7660 : decode_any W_a7660 = Some (Mul M_MUL 12 5 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7664 : bv 32 := 0x02d286bb.
Lemma F_a7664 : fetch_word Ubsan.M.loaded_segments (0xa7664 : word) = Some W_a7664.
Proof. vm_refl. Qed.
Lemma D_a7664 : decode_any W_a7664 = Some (Mul32 M_MUL 13 5 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7668 : bv 32 := 0x42c69e63.
Lemma F_a7668 : fetch_word Ubsan.M.loaded_segments (0xa7668 : word) = Some W_a7668.
Proof. vm_refl. Qed.
Lemma D_a7668 : decode_any W_a7668 = Some (Branch BC_NE 13 12 1084, 4%Z).
Proof. vm_refl. Qed.

Definition W_a766c : bv 32 := 0x0006061b.
Lemma F_a766c : fetch_word Ubsan.M.loaded_segments (0xa766c : word) = Some W_a766c.
Proof. vm_refl. Qed.
Lemma D_a766c : decode_any W_a766c = Some (OpImm32 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7670 : bv 32 := 0x00261d13.
Lemma F_a7670 : fetch_word Ubsan.M.loaded_segments (0xa7670 : word) = Some W_a7670.
Proof. vm_refl. Qed.
Lemma D_a7670 : decode_any W_a7670 = Some (ShiftImm ALU_SLL 26 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7674 : bv 32 := 0x05013683.
Lemma F_a7674 : fetch_word Ubsan.M.loaded_segments (0xa7674 : word) = Some W_a7674.
Proof. vm_refl. Qed.
Lemma D_a7674 : decode_any W_a7674 = Some (Load SZ8 true 13 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7678 : bv 32 := 0x01a68d33.
Lemma F_a7678 : fetch_word Ubsan.M.loaded_segments (0xa7678 : word) = Some W_a7678.
Proof. vm_refl. Qed.
Lemma D_a7678 : decode_any W_a7678 = Some (Op ALU_ADD 26 13 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_a767c : bv 32 := 0x001d3693.
Lemma F_a767c : fetch_word Ubsan.M.loaded_segments (0xa767c : word) = Some W_a767c.
Proof. vm_refl. Qed.
Lemma D_a767c : decode_any W_a767c = Some (OpImm ALU_SLTU 13 26 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7680 : bv 32 := 0x42de8263.
Lemma F_a7680 : fetch_word Ubsan.M.loaded_segments (0xa7680 : word) = Some W_a7680.
Proof. vm_refl. Qed.
Lemma D_a7680 : decode_any W_a7680 = Some (Branch BC_EQ 29 13 1060, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7684 : bv 32 := 0x05013683.
Lemma F_a7684 : fetch_word Ubsan.M.loaded_segments (0xa7684 : word) = Some W_a7684.
Proof. vm_refl. Qed.
Lemma D_a7684 : decode_any W_a7684 = Some (Load SZ8 true 13 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7688 : bv 32 := 0x00dd36b3.
Lemma F_a7688 : fetch_word Ubsan.M.loaded_segments (0xa7688 : word) = Some W_a7688.
Proof. vm_refl. Qed.
Lemma D_a7688 : decode_any W_a7688 = Some (Op ALU_SLTU 13 26 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a768c : bv 32 := 0x00062613.
Lemma F_a768c : fetch_word Ubsan.M.loaded_segments (0xa768c : word) = Some W_a768c.
Proof. vm_refl. Qed.
Lemma D_a768c : decode_any W_a768c = Some (OpImm ALU_SLT 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7690 : bv 32 := 0x00c6c633.
Lemma F_a7690 : fetch_word Ubsan.M.loaded_segments (0xa7690 : word) = Some W_a7690.
Proof. vm_refl. Qed.
Lemma D_a7690 : decode_any W_a7690 = Some (Op ALU_XOR 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7694 : bv 32 := 0x00164613.
Lemma F_a7694 : fetch_word Ubsan.M.loaded_segments (0xa7694 : word) = Some W_a7694.
Proof. vm_refl. Qed.
Lemma D_a7694 : decode_any W_a7694 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7698 : bv 32 := 0x40060663.
Lemma F_a7698 : fetch_word Ubsan.M.loaded_segments (0xa7698 : word) = Some W_a7698.
Proof. vm_refl. Qed.
Lemma D_a7698 : decode_any W_a7698 = Some (Branch BC_EQ 12 0 1036, 4%Z).
Proof. vm_refl. Qed.

Definition W_a769c : bv 32 := 0x02a88633.
Lemma F_a769c : fetch_word Ubsan.M.loaded_segments (0xa769c : word) = Some W_a769c.
Proof. vm_refl. Qed.
Lemma D_a769c : decode_any W_a769c = Some (Mul M_MUL 12 17 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a76a0 : bv 32 := 0x02a886bb.
Lemma F_a76a0 : fetch_word Ubsan.M.loaded_segments (0xa76a0 : word) = Some W_a76a0.
Proof. vm_refl. Qed.
Lemma D_a76a0 : decode_any W_a76a0 = Some (Mul32 M_MUL 13 17 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a76a4 : bv 32 := 0x40c69063.
Lemma F_a76a4 : fetch_word Ubsan.M.loaded_segments (0xa76a4 : word) = Some W_a76a4.
Proof. vm_refl. Qed.
Lemma D_a76a4 : decode_any W_a76a4 = Some (Branch BC_NE 13 12 1024, 4%Z).
Proof. vm_refl. Qed.

Definition W_a76a8 : bv 32 := 0x01203db3.
Lemma F_a76a8 : fetch_word Ubsan.M.loaded_segments (0xa76a8 : word) = Some W_a76a8.
Proof. vm_refl. Qed.
Lemma D_a76a8 : decode_any W_a76a8 = Some (Op ALU_SLTU 27 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_a76ac : bv 32 := 0x0006061b.
Lemma F_a76ac : fetch_word Ubsan.M.loaded_segments (0xa76ac : word) = Some W_a76ac.
Proof. vm_refl. Qed.
Lemma D_a76ac : decode_any W_a76ac = Some (OpImm32 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a76b0 : bv 32 := 0x00261093.
Lemma F_a76b0 : fetch_word Ubsan.M.loaded_segments (0xa76b0 : word) = Some W_a76b0.
Proof. vm_refl. Qed.
Lemma D_a76b0 : decode_any W_a76b0 = Some (ShiftImm ALU_SLL 1 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a76b4 : bv 32 := 0x001900b3.
Lemma F_a76b4 : fetch_word Ubsan.M.loaded_segments (0xa76b4 : word) = Some W_a76b4.
Proof. vm_refl. Qed.
Lemma D_a76b4 : decode_any W_a76b4 = Some (Op ALU_ADD 1 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a76b8 : bv 32 := 0x0010b693.
Lemma F_a76b8 : fetch_word Ubsan.M.loaded_segments (0xa76b8 : word) = Some W_a76b8.
Proof. vm_refl. Qed.
Lemma D_a76b8 : decode_any W_a76b8 = Some (OpImm ALU_SLTU 13 1 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a76bc : bv 32 := 0x3edd8463.
Lemma F_a76bc : fetch_word Ubsan.M.loaded_segments (0xa76bc : word) = Some W_a76bc.
Proof. vm_refl. Qed.
Lemma D_a76bc : decode_any W_a76bc = Some (Branch BC_EQ 27 13 1000, 4%Z).
Proof. vm_refl. Qed.

Definition W_a76c0 : bv 32 := 0x0120b6b3.
Lemma F_a76c0 : fetch_word Ubsan.M.loaded_segments (0xa76c0 : word) = Some W_a76c0.
Proof. vm_refl. Qed.
Lemma D_a76c0 : decode_any W_a76c0 = Some (Op ALU_SLTU 13 1 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_a76c4 : bv 32 := 0x00062613.
Lemma F_a76c4 : fetch_word Ubsan.M.loaded_segments (0xa76c4 : word) = Some W_a76c4.
Proof. vm_refl. Qed.
Lemma D_a76c4 : decode_any W_a76c4 = Some (OpImm ALU_SLT 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a76c8 : bv 32 := 0x00c6c633.
Lemma F_a76c8 : fetch_word Ubsan.M.loaded_segments (0xa76c8 : word) = Some W_a76c8.
Proof. vm_refl. Qed.
Lemma D_a76c8 : decode_any W_a76c8 = Some (Op ALU_XOR 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a76cc : bv 32 := 0x00164613.
Lemma F_a76cc : fetch_word Ubsan.M.loaded_segments (0xa76cc : word) = Some W_a76cc.
Proof. vm_refl. Qed.
Lemma D_a76cc : decode_any W_a76cc = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a76d0 : bv 32 := 0x3c060a63.
Lemma F_a76d0 : fetch_word Ubsan.M.loaded_segments (0xa76d0 : word) = Some W_a76d0.
Proof. vm_refl. Qed.
Lemma D_a76d0 : decode_any W_a76d0 = Some (Branch BC_EQ 12 0 980, 4%Z).
Proof. vm_refl. Qed.

Definition W_a76d4 : bv 32 := 0x04013603.
Lemma F_a76d4 : fetch_word Ubsan.M.loaded_segments (0xa76d4 : word) = Some W_a76d4.
Proof. vm_refl. Qed.
Lemma D_a76d4 : decode_any W_a76d4 = Some (Load SZ8 true 12 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a76d8 : bv 32 := 0x10c05863.
Lemma F_a76d8 : fetch_word Ubsan.M.loaded_segments (0xa76d8 : word) = Some W_a76d8.
Proof. vm_refl. Qed.
Lemma D_a76d8 : decode_any W_a76d8 = Some (Branch BC_GE 0 12 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_a76dc : bv 32 := 0x00000a93.
Lemma F_a76dc : fetch_word Ubsan.M.loaded_segments (0xa76dc : word) = Some W_a76dc.
Proof. vm_refl. Qed.
Lemma D_a76dc : decode_any W_a76dc = Some (OpImm ALU_ADD 21 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a76e0 : bv 32 := 0x00281b93.
Lemma F_a76e0 : fetch_word Ubsan.M.loaded_segments (0xa76e0 : word) = Some W_a76e0.
Proof. vm_refl. Qed.
Lemma D_a76e0 : decode_any W_a76e0 = Some (ShiftImm ALU_SLL 23 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a76e4 : bv 32 := 0x00279613.
Lemma F_a76e4 : fetch_word Ubsan.M.loaded_segments (0xa76e4 : word) = Some W_a76e4.
Proof. vm_refl. Qed.
Lemma D_a76e4 : decode_any W_a76e4 = Some (ShiftImm ALU_SLL 12 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a76e8 : bv 32 := 0x04813683.
Lemma F_a76e8 : fetch_word Ubsan.M.loaded_segments (0xa76e8 : word) = Some W_a76e8.
Proof. vm_refl. Qed.
Lemma D_a76e8 : decode_any W_a76e8 = Some (Load SZ8 true 13 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a76ec : bv 32 := 0x0006a693.
Lemma F_a76ec : fetch_word Ubsan.M.loaded_segments (0xa76ec : word) = Some W_a76ec.
Proof. vm_refl. Qed.
Lemma D_a76ec : decode_any W_a76ec = Some (OpImm ALU_SLT 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a76f0 : bv 32 := 0x02013303.
Lemma F_a76f0 : fetch_word Ubsan.M.loaded_segments (0xa76f0 : word) = Some W_a76f0.
Proof. vm_refl. Qed.
Lemma D_a76f0 : decode_any W_a76f0 = Some (Load SZ8 true 6 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a76f4 : bv 32 := 0x01a30333.
Lemma F_a76f4 : fetch_word Ubsan.M.loaded_segments (0xa76f4 : word) = Some W_a76f4.
Proof. vm_refl. Qed.
Lemma D_a76f4 : decode_any W_a76f4 = Some (Op ALU_ADD 6 6 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_a76f8 : bv 32 := 0x01813f03.
Lemma F_a76f8 : fetch_word Ubsan.M.loaded_segments (0xa76f8 : word) = Some W_a76f8.
Proof. vm_refl. Qed.
Lemma D_a76f8 : decode_any W_a76f8 = Some (Load SZ8 true 30 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a76fc : bv 32 := 0x01ed0f33.
Lemma F_a76fc : fetch_word Ubsan.M.loaded_segments (0xa76fc : word) = Some W_a76fc.
Proof. vm_refl. Qed.
Lemma D_a76fc : decode_any W_a76fc = Some (Op ALU_ADD 30 26 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7700 : bv 32 := 0x01790bb3.
Lemma F_a7700 : fetch_word Ubsan.M.loaded_segments (0xa7700 : word) = Some W_a7700.
Proof. vm_refl. Qed.
Lemma D_a7700 : decode_any W_a7700 = Some (Op ALU_ADD 23 18 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7704 : bv 32 := 0x05013c83.
Lemma F_a7704 : fetch_word Ubsan.M.loaded_segments (0xa7704 : word) = Some W_a7704.
Proof. vm_refl. Qed.
Lemma D_a7704 : decode_any W_a7704 = Some (Load SZ8 true 25 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7708 : bv 32 := 0x00cc8cb3.
Lemma F_a7708 : fetch_word Ubsan.M.loaded_segments (0xa7708 : word) = Some W_a7708.
Proof. vm_refl. Qed.
Lemma D_a7708 : decode_any W_a7708 = Some (Op ALU_ADD 25 25 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a770c : bv 32 := 0x01013703.
Lemma F_a770c : fetch_word Ubsan.M.loaded_segments (0xa770c : word) = Some W_a770c.
Proof. vm_refl. Qed.
Lemma D_a770c : decode_any W_a770c = Some (Load SZ8 true 14 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7710 : bv 32 := 0x00c70633.
Lemma F_a7710 : fetch_word Ubsan.M.loaded_segments (0xa7710 : word) = Some W_a7710.
Proof. vm_refl. Qed.
Lemma D_a7710 : decode_any W_a7710 = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7714 : bv 32 := 0x00603fb3.
Lemma F_a7714 : fetch_word Ubsan.M.loaded_segments (0xa7714 : word) = Some W_a7714.
Proof. vm_refl. Qed.
Lemma D_a7714 : decode_any W_a7714 = Some (Op ALU_SLTU 31 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7718 : bv 32 := 0x01a33333.
Lemma F_a7718 : fetch_word Ubsan.M.loaded_segments (0xa7718 : word) = Some W_a7718.
Proof. vm_refl. Qed.
Lemma D_a7718 : decode_any W_a7718 = Some (Op ALU_SLTU 6 6 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_a771c : bv 32 := 0x00d346b3.
Lemma F_a771c : fetch_word Ubsan.M.loaded_segments (0xa771c : word) = Some W_a771c.
Proof. vm_refl. Qed.
Lemma D_a771c : decode_any W_a771c = Some (Op ALU_XOR 13 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7720 : bv 32 := 0x0016c693.
Lemma F_a7720 : fetch_word Ubsan.M.loaded_segments (0xa7720 : word) = Some W_a7720.
Proof. vm_refl. Qed.
Lemma D_a7720 : decode_any W_a7720 = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7724 : bv 32 := 0x00dff333.
Lemma F_a7724 : fetch_word Ubsan.M.loaded_segments (0xa7724 : word) = Some W_a7724.
Proof. vm_refl. Qed.
Lemma D_a7724 : decode_any W_a7724 = Some (Op ALU_AND 6 31 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7728 : bv 32 := 0xffff4f93.
Lemma F_a7728 : fetch_word Ubsan.M.loaded_segments (0xa7728 : word) = Some W_a7728.
Proof. vm_refl. Qed.
Lemma D_a7728 : decode_any W_a7728 = Some (OpImm ALU_XOR 31 30 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a772c : bv 32 := 0x04013f03.
Lemma F_a772c : fetch_word Ubsan.M.loaded_segments (0xa772c : word) = Some W_a772c.
Proof. vm_refl. Qed.
Lemma D_a772c : decode_any W_a772c = Some (Load SZ8 true 30 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7730 : bv 32 := 0x000b8993.
Lemma F_a7730 : fetch_word Ubsan.M.loaded_segments (0xa7730 : word) = Some W_a7730.
Proof. vm_refl. Qed.
Lemma D_a7730 : decode_any W_a7730 = Some (OpImm ALU_ADD 19 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7734 : bv 32 := 0x015c8433.
Lemma F_a7734 : fetch_word Ubsan.M.loaded_segments (0xa7734 : word) = Some W_a7734.
Proof. vm_refl. Qed.
Lemma D_a7734 : decode_any W_a7734 = Some (Op ALU_ADD 8 25 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7738 : bv 32 := 0x37a46663.
Lemma F_a7738 : fetch_word Ubsan.M.loaded_segments (0xa7738 : word) = Some W_a7738.
Proof. vm_refl. Qed.
Lemma D_a7738 : decode_any W_a7738 = Some (Branch BC_LTU 8 26 876, 4%Z).
Proof. vm_refl. Qed.

Definition W_a773c : bv 32 := 0x00143693.
Lemma F_a773c : fetch_word Ubsan.M.loaded_segments (0xa773c : word) = Some W_a773c.
Proof. vm_refl. Qed.
Lemma D_a773c : decode_any W_a773c = Some (OpImm ALU_SLTU 13 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7740 : bv 32 := 0x00dec6b3.
Lemma F_a7740 : fetch_word Ubsan.M.loaded_segments (0xa7740 : word) = Some W_a7740.
Proof. vm_refl. Qed.
Lemma D_a7740 : decode_any W_a7740 = Some (Op ALU_XOR 13 29 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7744 : bv 32 := 0x36068063.
Lemma F_a7744 : fetch_word Ubsan.M.loaded_segments (0xa7744 : word) = Some W_a7744.
Proof. vm_refl. Qed.
Lemma D_a7744 : decode_any W_a7744 = Some (Branch BC_EQ 13 0 864, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7748 : bv 32 := 0x340c0e63.
Lemma F_a7748 : fetch_word Ubsan.M.loaded_segments (0xa7748 : word) = Some W_a7748.
Proof. vm_refl. Qed.
Lemma D_a7748 : decode_any W_a7748 = Some (Branch BC_EQ 24 0 860, 4%Z).
Proof. vm_refl. Qed.

Definition W_a774c : bv 32 := 0x34030c63.
Lemma F_a774c : fetch_word Ubsan.M.loaded_segments (0xa774c : word) = Some W_a774c.
Proof. vm_refl. Qed.
Lemma D_a774c : decode_any W_a774c = Some (Branch BC_EQ 6 0 856, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7750 : bv 32 := 0x355fea63.
Lemma F_a7750 : fetch_word Ubsan.M.loaded_segments (0xa7750 : word) = Some W_a7750.
Proof. vm_refl. Qed.
Lemma D_a7750 : decode_any W_a7750 = Some (Branch BC_LTU 31 21 852, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7754 : bv 32 := 0x015606b3.
Lemma F_a7754 : fetch_word Ubsan.M.loaded_segments (0xa7754 : word) = Some W_a7754.
Proof. vm_refl. Qed.
Lemma D_a7754 : decode_any W_a7754 = Some (Op ALU_ADD 13 12 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7758 : bv 32 := 0x00042403.
Lemma F_a7758 : fetch_word Ubsan.M.loaded_segments (0xa7758 : word) = Some W_a7758.
Proof. vm_refl. Qed.
Lemma D_a7758 : decode_any W_a7758 = Some (Load SZ4 true 8 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a775c : bv 32 := 0x0006a683.
Lemma F_a775c : fetch_word Ubsan.M.loaded_segments (0xa775c : word) = Some W_a775c.
Proof. vm_refl. Qed.
Lemma D_a775c : decode_any W_a775c = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7760 : bv 32 := 0x0086f4b3.
Lemma F_a7760 : fetch_word Ubsan.M.loaded_segments (0xa7760 : word) = Some W_a7760.
Proof. vm_refl. Qed.
Lemma D_a7760 : decode_any W_a7760 = Some (Op ALU_AND 9 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7764 : bv 32 := 0x0086e433.
Lemma F_a7764 : fetch_word Ubsan.M.loaded_segments (0xa7764 : word) = Some W_a7764.
Proof. vm_refl. Qed.
Lemma D_a7764 : decode_any W_a7764 = Some (Op ALU_OR 8 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7768 : bv 32 := 0x00149713.
Lemma F_a7768 : fetch_word Ubsan.M.loaded_segments (0xa7768 : word) = Some W_a7768.
Proof. vm_refl. Qed.
Lemma D_a7768 : decode_any W_a7768 = Some (ShiftImm ALU_SLL 14 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a776c : bv 32 := 0x00141693.
Lemma F_a776c : fetch_word Ubsan.M.loaded_segments (0xa776c : word) = Some W_a776c.
Proof. vm_refl. Qed.
Lemma D_a776c : decode_any W_a776c = Some (ShiftImm ALU_SLL 13 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7770 : bv 32 := 0x0086f6b3.
Lemma F_a7770 : fetch_word Ubsan.M.loaded_segments (0xa7770 : word) = Some W_a7770.
Proof. vm_refl. Qed.
Lemma D_a7770 : decode_any W_a7770 = Some (Op ALU_AND 13 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7774 : bv 32 := 0x00976733.
Lemma F_a7774 : fetch_word Ubsan.M.loaded_segments (0xa7774 : word) = Some W_a7774.
Proof. vm_refl. Qed.
Lemma D_a7774 : decode_any W_a7774 = Some (Op ALU_OR 14 14 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7778 : bv 32 := 0x00d766b3.
Lemma F_a7778 : fetch_word Ubsan.M.loaded_segments (0xa7778 : word) = Some W_a7778.
Proof. vm_refl. Qed.
Lemma D_a7778 : decode_any W_a7778 = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a777c : bv 32 := 0x0166f6b3.
Lemma F_a777c : fetch_word Ubsan.M.loaded_segments (0xa777c : word) = Some W_a777c.
Proof. vm_refl. Qed.
Lemma D_a777c : decode_any W_a777c = Some (Op ALU_AND 13 13 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7780 : bv 32 := 0x00769713.
Lemma F_a7780 : fetch_word Ubsan.M.loaded_segments (0xa7780 : word) = Some W_a7780.
Proof. vm_refl. Qed.
Lemma D_a7780 : decode_any W_a7780 = Some (ShiftImm ALU_SLL 14 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7784 : bv 32 := 0x00d706b3.
Lemma F_a7784 : fetch_word Ubsan.M.loaded_segments (0xa7784 : word) = Some W_a7784.
Proof. vm_refl. Qed.
Lemma D_a7784 : decode_any W_a7784 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7788 : bv 32 := 0x0186d41b.
Lemma F_a7788 : fetch_word Ubsan.M.loaded_segments (0xa7788 : word) = Some W_a7788.
Proof. vm_refl. Qed.
Lemma D_a7788 : decode_any W_a7788 = Some (ShiftImm32 ALU_SRL 8 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a778c : bv 32 := 0x3083ec63.
Lemma F_a778c : fetch_word Ubsan.M.loaded_segments (0xa778c : word) = Some W_a778c.
Proof. vm_refl. Qed.
Lemma D_a778c : decode_any W_a778c = Some (Branch BC_LTU 7 8 792, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7790 : bv 32 := 0x03069693.
Lemma F_a7790 : fetch_word Ubsan.M.loaded_segments (0xa7790 : word) = Some W_a7790.
Proof. vm_refl. Qed.
Lemma D_a7790 : decode_any W_a7790 = Some (ShiftImm ALU_SLL 13 13 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7794 : bv 32 := 0x0386d693.
Lemma F_a7794 : fetch_word Ubsan.M.loaded_segments (0xa7794 : word) = Some W_a7794.
Proof. vm_refl. Qed.
Lemma D_a7794 : decode_any W_a7794 = Some (ShiftImm ALU_SRL 13 13 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7798 : bv 32 := 0x30d3e663.
Lemma F_a7798 : fetch_word Ubsan.M.loaded_segments (0xa7798 : word) = Some W_a7798.
Proof. vm_refl. Qed.
Lemma D_a7798 : decode_any W_a7798 = Some (Branch BC_LTU 7 13 780, 4%Z).
Proof. vm_refl. Qed.

Definition W_a779c : bv 32 := 0x3019e463.
Lemma F_a779c : fetch_word Ubsan.M.loaded_segments (0xa779c : word) = Some W_a779c.
Proof. vm_refl. Qed.
Lemma D_a779c : decode_any W_a779c = Some (Branch BC_LTU 19 1 776, 4%Z).
Proof. vm_refl. Qed.

Definition W_a77a0 : bv 32 := 0x0019b713.
Lemma F_a77a0 : fetch_word Ubsan.M.loaded_segments (0xa77a0 : word) = Some W_a77a0.
Proof. vm_refl. Qed.
Lemma D_a77a0 : decode_any W_a77a0 = Some (OpImm ALU_SLTU 14 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a77a4 : bv 32 := 0x00edc733.
Lemma F_a77a4 : fetch_word Ubsan.M.loaded_segments (0xa77a4 : word) = Some W_a77a4.
Proof. vm_refl. Qed.
Lemma D_a77a4 : decode_any W_a77a4 = Some (Op ALU_XOR 14 27 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_a77a8 : bv 32 := 0x2e070e63.
Lemma F_a77a8 : fetch_word Ubsan.M.loaded_segments (0xa77a8 : word) = Some W_a77a8.
Proof. vm_refl. Qed.
Lemma D_a77a8 : decode_any W_a77a8 = Some (Branch BC_EQ 14 0 764, 4%Z).
Proof. vm_refl. Qed.

Definition W_a77ac : bv 32 := 0x2e0e1c63.
Lemma F_a77ac : fetch_word Ubsan.M.loaded_segments (0xa77ac : word) = Some W_a77ac.
Proof. vm_refl. Qed.
Lemma D_a77ac : decode_any W_a77ac = Some (Branch BC_NE 28 0 760, 4%Z).
Proof. vm_refl. Qed.

Definition W_a77b0 : bv 32 := 0x2f4b8a63.
Lemma F_a77b0 : fetch_word Ubsan.M.loaded_segments (0xa77b0 : word) = Some W_a77b0.
Proof. vm_refl. Qed.
Lemma D_a77b0 : decode_any W_a77b0 = Some (Branch BC_EQ 23 20 756, 4%Z).
Proof. vm_refl. Qed.

Definition W_a77b4 : bv 32 := 0x00d586b3.
Lemma F_a77b4 : fetch_word Ubsan.M.loaded_segments (0xa77b4 : word) = Some W_a77b4.
Proof. vm_refl. Qed.
Lemma D_a77b4 : decode_any W_a77b4 = Some (Op ALU_ADD 13 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a77b8 : bv 32 := 0x00858433.
Lemma F_a77b8 : fetch_word Ubsan.M.loaded_segments (0xa77b8 : word) = Some W_a77b8.
Proof. vm_refl. Qed.
Lemma D_a77b8 : decode_any W_a77b8 = Some (Op ALU_ADD 8 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a77bc : bv 32 := 0x00044703.
Lemma F_a77bc : fetch_word Ubsan.M.loaded_segments (0xa77bc : word) = Some W_a77bc.
Proof. vm_refl. Qed.
Lemma D_a77bc : decode_any W_a77bc = Some (Load SZ1 false 14 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a77c0 : bv 32 := 0x0006c683.
Lemma F_a77c0 : fetch_word Ubsan.M.loaded_segments (0xa77c0 : word) = Some W_a77c0.
Proof. vm_refl. Qed.
Lemma D_a77c0 : decode_any W_a77c0 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a77c4 : bv 32 := 0x00871713.
Lemma F_a77c4 : fetch_word Ubsan.M.loaded_segments (0xa77c4 : word) = Some W_a77c4.
Proof. vm_refl. Qed.
Lemma D_a77c4 : decode_any W_a77c4 = Some (ShiftImm ALU_SLL 14 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a77c8 : bv 32 := 0x00d766b3.
Lemma F_a77c8 : fetch_word Ubsan.M.loaded_segments (0xa77c8 : word) = Some W_a77c8.
Proof. vm_refl. Qed.
Lemma D_a77c8 : decode_any W_a77c8 = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a77cc : bv 32 := 0x0029c713.
Lemma F_a77cc : fetch_word Ubsan.M.loaded_segments (0xa77cc : word) = Some W_a77cc.
Proof. vm_refl. Qed.
Lemma D_a77cc : decode_any W_a77cc = Some (OpImm ALU_XOR 14 19 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a77d0 : bv 32 := 0x00298993.
Lemma F_a77d0 : fetch_word Ubsan.M.loaded_segments (0xa77d0 : word) = Some W_a77d0.
Proof. vm_refl. Qed.
Lemma D_a77d0 : decode_any W_a77d0 = Some (OpImm ALU_ADD 19 19 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a77d4 : bv 32 := 0x004a8a93.
Lemma F_a77d4 : fetch_word Ubsan.M.loaded_segments (0xa77d4 : word) = Some W_a77d4.
Proof. vm_refl. Qed.
Lemma D_a77d4 : decode_any W_a77d4 = Some (OpImm ALU_ADD 21 21 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a77d8 : bv 32 := 0xffff0f13.
Lemma F_a77d8 : fetch_word Ubsan.M.loaded_segments (0xa77d8 : word) = Some W_a77d8.
Proof. vm_refl. Qed.
Lemma D_a77d8 : decode_any W_a77d8 = Some (OpImm ALU_ADD 30 30 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a77dc : bv 32 := 0x00d71023.
Lemma F_a77dc : fetch_word Ubsan.M.loaded_segments (0xa77dc : word) = Some W_a77dc.
Proof. vm_refl. Qed.
Lemma D_a77dc : decode_any W_a77dc = Some (Store SZ2 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a77e0 : bv 32 := 0x002b8b93.
Lemma F_a77e0 : fetch_word Ubsan.M.loaded_segments (0xa77e0 : word) = Some W_a77e0.
Proof. vm_refl. Qed.
Lemma D_a77e0 : decode_any W_a77e0 = Some (OpImm ALU_ADD 23 23 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a77e4 : bv 32 := 0xf40f18e3.
Lemma F_a77e4 : fetch_word Ubsan.M.loaded_segments (0xa77e4 : word) = Some W_a77e4.
Proof. vm_refl. Qed.
Lemma D_a77e4 : decode_any W_a77e4 = Some (Branch BC_NE 30 0 8016, 4%Z).
Proof. vm_refl. Qed.

Definition W_a77e8 : bv 32 := 0x03013603.
Lemma F_a77e8 : fetch_word Ubsan.M.loaded_segments (0xa77e8 : word) = Some W_a77e8.
Proof. vm_refl. Qed.
Lemma D_a77e8 : decode_any W_a77e8 = Some (Load SZ8 true 12 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a77ec : bv 32 := 0x2ac88c63.
Lemma F_a77ec : fetch_word Ubsan.M.loaded_segments (0xa77ec : word) = Some W_a77ec.
Proof. vm_refl. Qed.
Lemma D_a77ec : decode_any W_a77ec = Some (Branch BC_EQ 17 12 696, 4%Z).
Proof. vm_refl. Qed.

Definition W_a77f0 : bv 32 := 0x0022829b.
Lemma F_a77f0 : fetch_word Ubsan.M.loaded_segments (0xa77f0 : word) = Some W_a77f0.
Proof. vm_refl. Qed.
Lemma D_a77f0 : decode_any W_a77f0 = Some (OpImm32 5 5 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a77f4 : bv 32 := 0x0018889b.
Lemma F_a77f4 : fetch_word Ubsan.M.loaded_segments (0xa77f4 : word) = Some W_a77f4.
Proof. vm_refl. Qed.
Lemma D_a77f4 : decode_any W_a77f4 = Some (OpImm32 17 17 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a77f8 : bv 32 := 0x00a8083b.
Lemma F_a77f8 : fetch_word Ubsan.M.loaded_segments (0xa77f8 : word) = Some W_a77f8.
Proof. vm_refl. Qed.
Lemma D_a77f8 : decode_any W_a77f8 = Some (Op32 ALU_ADD 16 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a77fc : bv 32 := 0x02813603.
Lemma F_a77fc : fetch_word Ubsan.M.loaded_segments (0xa77fc : word) = Some W_a77fc.
Proof. vm_refl. Qed.
Lemma D_a77fc : decode_any W_a77fc = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7800 : bv 32 := 0x00c787bb.
Lemma F_a7800 : fetch_word Ubsan.M.loaded_segments (0xa7800 : word) = Some W_a7800.
Proof. vm_refl. Qed.
Lemma D_a7800 : decode_any W_a7800 = Some (Op32 ALU_ADD 15 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7804 : bv 32 := 0x03813603.
Lemma F_a7804 : fetch_word Ubsan.M.loaded_segments (0xa7804 : word) = Some W_a7804.
Proof. vm_refl. Qed.
Lemma D_a7804 : decode_any W_a7804 = Some (Load SZ8 true 12 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7808 : bv 32 := 0xe4c2cae3.
Lemma F_a7808 : fetch_word Ubsan.M.loaded_segments (0xa7808 : word) = Some W_a7808.
Proof. vm_refl. Qed.
Lemma D_a7808 : decode_any W_a7808 = Some (Branch BC_LT 5 12 7764, 4%Z).
Proof. vm_refl. Qed.

Definition W_a780c : bv 32 := 0x2100006f.
Lemma F_a780c : fetch_word Ubsan.M.loaded_segments (0xa780c : word) = Some W_a780c.
Proof. vm_refl. Qed.
Lemma D_a780c : decode_any W_a780c = Some (Jal 0 528, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7810 : bv 32 := 0x28061a63.
Lemma F_a7810 : fetch_word Ubsan.M.loaded_segments (0xa7810 : word) = Some W_a7810.
Proof. vm_refl. Qed.
Lemma D_a7810 : decode_any W_a7810 = Some (Branch BC_NE 12 0 660, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7814 : bv 32 := 0x03813603.
Lemma F_a7814 : fetch_word Ubsan.M.loaded_segments (0xa7814 : word) = Some W_a7814.
Proof. vm_refl. Qed.
Lemma D_a7814 : decode_any W_a7814 = Some (Load SZ8 true 12 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7818 : bv 32 := 0x20c05263.
Lemma F_a7818 : fetch_word Ubsan.M.loaded_segments (0xa7818 : word) = Some W_a7818.
Proof. vm_refl. Qed.
Lemma D_a7818 : decode_any W_a7818 = Some (Branch BC_GE 0 12 516, 4%Z).
Proof. vm_refl. Qed.

Definition W_a781c : bv 32 := 0x00000793.
Lemma F_a781c : fetch_word Ubsan.M.loaded_segments (0xa781c : word) = Some W_a781c.
Proof. vm_refl. Qed.
Lemma D_a781c : decode_any W_a781c = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7820 : bv 32 := 0x00000813.
Lemma F_a7820 : fetch_word Ubsan.M.loaded_segments (0xa7820 : word) = Some W_a7820.
Proof. vm_refl. Qed.
Lemma D_a7820 : decode_any W_a7820 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7824 : bv 32 := 0x00000893.
Lemma F_a7824 : fetch_word Ubsan.M.loaded_segments (0xa7824 : word) = Some W_a7824.
Proof. vm_refl. Qed.
Lemma D_a7824 : decode_any W_a7824 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7828 : bv 32 := 0x00000293.
Lemma F_a7828 : fetch_word Ubsan.M.loaded_segments (0xa7828 : word) = Some W_a7828.
Proof. vm_refl. Qed.
Lemma D_a7828 : decode_any W_a7828 = Some (OpImm ALU_ADD 5 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a782c : bv 32 := 0x04813703.
Lemma F_a782c : fetch_word Ubsan.M.loaded_segments (0xa782c : word) = Some W_a782c.
Proof. vm_refl. Qed.
Lemma D_a782c : decode_any W_a782c = Some (Load SZ8 true 14 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7830 : bv 32 := 0x00271613.
Lemma F_a7830 : fetch_word Ubsan.M.loaded_segments (0xa7830 : word) = Some W_a7830.
Proof. vm_refl. Qed.
Lemma D_a7830 : decode_any W_a7830 = Some (ShiftImm ALU_SLL 12 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7834 : bv 32 := 0x02c13423.
Lemma F_a7834 : fetch_word Ubsan.M.loaded_segments (0xa7834 : word) = Some W_a7834.
Proof. vm_refl. Qed.
Lemma D_a7834 : decode_any W_a7834 = Some (Store SZ8 2 12 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7838 : bv 32 := 0xfff5c393.
Lemma F_a7838 : fetch_word Ubsan.M.loaded_segments (0xa7838 : word) = Some W_a7838.
Proof. vm_refl. Qed.
Lemma D_a7838 : decode_any W_a7838 = Some (OpImm ALU_XOR 7 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a783c : bv 32 := 0x05013303.
Lemma F_a783c : fetch_word Ubsan.M.loaded_segments (0xa783c : word) = Some W_a783c.
Proof. vm_refl. Qed.
Lemma D_a783c : decode_any W_a783c = Some (Load SZ8 true 6 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7840 : bv 32 := 0x00337613.
Lemma F_a7840 : fetch_word Ubsan.M.loaded_segments (0xa7840 : word) = Some W_a7840.
Proof. vm_refl. Qed.
Lemma D_a7840 : decode_any W_a7840 = Some (OpImm ALU_AND 12 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7844 : bv 32 := 0x00197e13.
Lemma F_a7844 : fetch_word Ubsan.M.loaded_segments (0xa7844 : word) = Some W_a7844.
Proof. vm_refl. Qed.
Lemma D_a7844 : decode_any W_a7844 = Some (OpImm ALU_AND 28 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7848 : bv 32 := 0x00603eb3.
Lemma F_a7848 : fetch_word Ubsan.M.loaded_segments (0xa7848 : word) = Some W_a7848.
Proof. vm_refl. Qed.
Lemma D_a7848 : decode_any W_a7848 = Some (Op ALU_SLTU 29 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_a784c : bv 32 := 0xaaaab6b7.
Lemma F_a784c : fetch_word Ubsan.M.loaded_segments (0xa784c : word) = Some W_a784c.
Proof. vm_refl. Qed.
Lemma D_a784c : decode_any W_a784c = Some (Lui 13 699051, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7850 : bv 32 := 0x00171f13.
Lemma F_a7850 : fetch_word Ubsan.M.loaded_segments (0xa7850 : word) = Some W_a7850.
Proof. vm_refl. Qed.
Lemma D_a7850 : decode_any W_a7850 = Some (ShiftImm ALU_SLL 30 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7854 : bv 32 := 0x03e13823.
Lemma F_a7854 : fetch_word Ubsan.M.loaded_segments (0xa7854 : word) = Some W_a7854.
Proof. vm_refl. Qed.
Lemma D_a7854 : decode_any W_a7854 = Some (Store SZ8 2 30 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7858 : bv 32 := 0x00271713.
Lemma F_a7858 : fetch_word Ubsan.M.loaded_segments (0xa7858 : word) = Some W_a7858.
Proof. vm_refl. Qed.
Lemma D_a7858 : decode_any W_a7858 = Some (ShiftImm ALU_SLL 14 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a785c : bv 32 := 0x00200a13.
Lemma F_a785c : fetch_word Ubsan.M.loaded_segments (0xa785c : word) = Some W_a785c.
Proof. vm_refl. Qed.
Lemma D_a785c : decode_any W_a785c = Some (OpImm ALU_ADD 20 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7860 : bv 32 := 0x400004b7.
Lemma F_a7860 : fetch_word Ubsan.M.loaded_segments (0xa7860 : word) = Some W_a7860.
Proof. vm_refl. Qed.
Lemma D_a7860 : decode_any W_a7860 = Some (Lui 9 262144, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7864 : bv 32 := 0x00163613.
Lemma F_a7864 : fetch_word Ubsan.M.loaded_segments (0xa7864 : word) = Some W_a7864.
Proof. vm_refl. Qed.
Lemma D_a7864 : decode_any W_a7864 = Some (OpImm ALU_SLTU 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7868 : bv 32 := 0xaaa68b13.
Lemma F_a7868 : fetch_word Ubsan.M.loaded_segments (0xa7868 : word) = Some W_a7868.
Proof. vm_refl. Qed.
Lemma D_a7868 : decode_any W_a7868 = Some (OpImm ALU_ADD 22 13 2730, 4%Z).
Proof. vm_refl. Qed.

Definition W_a786c : bv 32 := 0x02e13023.
Lemma F_a786c : fetch_word Ubsan.M.loaded_segments (0xa786c : word) = Some W_a786c.
Proof. vm_refl. Qed.
Lemma D_a786c : decode_any W_a786c = Some (Store SZ8 2 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7870 : bv 32 := 0x00e30733.
Lemma F_a7870 : fetch_word Ubsan.M.loaded_segments (0xa7870 : word) = Some W_a7870.
Proof. vm_refl. Qed.
Lemma D_a7870 : decode_any W_a7870 = Some (Op ALU_ADD 14 6 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7874 : bv 32 := 0x00e13c23.
Lemma F_a7874 : fetch_word Ubsan.M.loaded_segments (0xa7874 : word) = Some W_a7874.
Proof. vm_refl. Qed.
Lemma D_a7874 : decode_any W_a7874 = Some (Store SZ8 2 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7878 : bv 32 := 0x01d67c33.
Lemma F_a7878 : fetch_word Ubsan.M.loaded_segments (0xa7878 : word) = Some W_a7878.
Proof. vm_refl. Qed.
Lemma D_a7878 : decode_any W_a7878 = Some (Op ALU_AND 24 12 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_a787c : bv 32 := 0xfff4849b.
Lemma F_a787c : fetch_word Ubsan.M.loaded_segments (0xa787c : word) = Some W_a787c.
Proof. vm_refl. Qed.
Lemma D_a787c : decode_any W_a787c = Some (OpImm32 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7880 : bv 32 := 0x04813683.
Lemma F_a7880 : fetch_word Ubsan.M.loaded_segments (0xa7880 : word) = Some W_a7880.
Proof. vm_refl. Qed.
Lemma D_a7880 : decode_any W_a7880 = Some (Load SZ8 true 13 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7884 : bv 32 := 0x02d28633.
Lemma F_a7884 : fetch_word Ubsan.M.loaded_segments (0xa7884 : word) = Some W_a7884.
Proof. vm_refl. Qed.
Lemma D_a7884 : decode_any W_a7884 = Some (Mul M_MUL 12 5 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7888 : bv 32 := 0x02d286bb.
Lemma F_a7888 : fetch_word Ubsan.M.loaded_segments (0xa7888 : word) = Some W_a7888.
Proof. vm_refl. Qed.
Lemma D_a7888 : decode_any W_a7888 = Some (Mul32 M_MUL 13 5 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a788c : bv 32 := 0x20c69c63.
Lemma F_a788c : fetch_word Ubsan.M.loaded_segments (0xa788c : word) = Some W_a788c.
Proof. vm_refl. Qed.
Lemma D_a788c : decode_any W_a788c = Some (Branch BC_NE 13 12 536, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7890 : bv 32 := 0x0006061b.
Lemma F_a7890 : fetch_word Ubsan.M.loaded_segments (0xa7890 : word) = Some W_a7890.
Proof. vm_refl. Qed.
Lemma D_a7890 : decode_any W_a7890 = Some (OpImm32 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7894 : bv 32 := 0x00261d13.
Lemma F_a7894 : fetch_word Ubsan.M.loaded_segments (0xa7894 : word) = Some W_a7894.
Proof. vm_refl. Qed.
Lemma D_a7894 : decode_any W_a7894 = Some (ShiftImm ALU_SLL 26 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7898 : bv 32 := 0x05013683.
Lemma F_a7898 : fetch_word Ubsan.M.loaded_segments (0xa7898 : word) = Some W_a7898.
Proof. vm_refl. Qed.
Lemma D_a7898 : decode_any W_a7898 = Some (Load SZ8 true 13 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a789c : bv 32 := 0x01a68d33.
Lemma F_a789c : fetch_word Ubsan.M.loaded_segments (0xa789c : word) = Some W_a789c.
Proof. vm_refl. Qed.
Lemma D_a789c : decode_any W_a789c = Some (Op ALU_ADD 26 13 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_a78a0 : bv 32 := 0x001d3693.
Lemma F_a78a0 : fetch_word Ubsan.M.loaded_segments (0xa78a0 : word) = Some W_a78a0.
Proof. vm_refl. Qed.
Lemma D_a78a0 : decode_any W_a78a0 = Some (OpImm ALU_SLTU 13 26 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a78a4 : bv 32 := 0x20de8063.
Lemma F_a78a4 : fetch_word Ubsan.M.loaded_segments (0xa78a4 : word) = Some W_a78a4.
Proof. vm_refl. Qed.
Lemma D_a78a4 : decode_any W_a78a4 = Some (Branch BC_EQ 29 13 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_a78a8 : bv 32 := 0x05013683.
Lemma F_a78a8 : fetch_word Ubsan.M.loaded_segments (0xa78a8 : word) = Some W_a78a8.
Proof. vm_refl. Qed.
Lemma D_a78a8 : decode_any W_a78a8 = Some (Load SZ8 true 13 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a78ac : bv 32 := 0x00dd36b3.
Lemma F_a78ac : fetch_word Ubsan.M.loaded_segments (0xa78ac : word) = Some W_a78ac.
Proof. vm_refl. Qed.
Lemma D_a78ac : decode_any W_a78ac = Some (Op ALU_SLTU 13 26 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a78b0 : bv 32 := 0x00062613.
Lemma F_a78b0 : fetch_word Ubsan.M.loaded_segments (0xa78b0 : word) = Some W_a78b0.
Proof. vm_refl. Qed.
Lemma D_a78b0 : decode_any W_a78b0 = Some (OpImm ALU_SLT 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a78b4 : bv 32 := 0x00c6c633.
Lemma F_a78b4 : fetch_word Ubsan.M.loaded_segments (0xa78b4 : word) = Some W_a78b4.
Proof. vm_refl. Qed.
Lemma D_a78b4 : decode_any W_a78b4 = Some (Op ALU_XOR 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a78b8 : bv 32 := 0x00164613.
Lemma F_a78b8 : fetch_word Ubsan.M.loaded_segments (0xa78b8 : word) = Some W_a78b8.
Proof. vm_refl. Qed.
Lemma D_a78b8 : decode_any W_a78b8 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a78bc : bv 32 := 0x1e060463.
Lemma F_a78bc : fetch_word Ubsan.M.loaded_segments (0xa78bc : word) = Some W_a78bc.
Proof. vm_refl. Qed.
Lemma D_a78bc : decode_any W_a78bc = Some (Branch BC_EQ 12 0 488, 4%Z).
Proof. vm_refl. Qed.

Definition W_a78c0 : bv 32 := 0x02a88633.
Lemma F_a78c0 : fetch_word Ubsan.M.loaded_segments (0xa78c0 : word) = Some W_a78c0.
Proof. vm_refl. Qed.
Lemma D_a78c0 : decode_any W_a78c0 = Some (Mul M_MUL 12 17 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a78c4 : bv 32 := 0x02a886bb.
Lemma F_a78c4 : fetch_word Ubsan.M.loaded_segments (0xa78c4 : word) = Some W_a78c4.
Proof. vm_refl. Qed.
Lemma D_a78c4 : decode_any W_a78c4 = Some (Mul32 M_MUL 13 17 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a78c8 : bv 32 := 0x1cc69e63.
Lemma F_a78c8 : fetch_word Ubsan.M.loaded_segments (0xa78c8 : word) = Some W_a78c8.
Proof. vm_refl. Qed.
Lemma D_a78c8 : decode_any W_a78c8 = Some (Branch BC_NE 13 12 476, 4%Z).
Proof. vm_refl. Qed.

Definition W_a78cc : bv 32 := 0x01203db3.
Lemma F_a78cc : fetch_word Ubsan.M.loaded_segments (0xa78cc : word) = Some W_a78cc.
Proof. vm_refl. Qed.
Lemma D_a78cc : decode_any W_a78cc = Some (Op ALU_SLTU 27 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_a78d0 : bv 32 := 0x0006061b.
Lemma F_a78d0 : fetch_word Ubsan.M.loaded_segments (0xa78d0 : word) = Some W_a78d0.
Proof. vm_refl. Qed.
Lemma D_a78d0 : decode_any W_a78d0 = Some (OpImm32 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a78d4 : bv 32 := 0x00261093.
Lemma F_a78d4 : fetch_word Ubsan.M.loaded_segments (0xa78d4 : word) = Some W_a78d4.
Proof. vm_refl. Qed.
Lemma D_a78d4 : decode_any W_a78d4 = Some (ShiftImm ALU_SLL 1 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a78d8 : bv 32 := 0x001900b3.
Lemma F_a78d8 : fetch_word Ubsan.M.loaded_segments (0xa78d8 : word) = Some W_a78d8.
Proof. vm_refl. Qed.
Lemma D_a78d8 : decode_any W_a78d8 = Some (Op ALU_ADD 1 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a78dc : bv 32 := 0x0010b693.
Lemma F_a78dc : fetch_word Ubsan.M.loaded_segments (0xa78dc : word) = Some W_a78dc.
Proof. vm_refl. Qed.
Lemma D_a78dc : decode_any W_a78dc = Some (OpImm ALU_SLTU 13 1 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a78e0 : bv 32 := 0x1cdd8263.
Lemma F_a78e0 : fetch_word Ubsan.M.loaded_segments (0xa78e0 : word) = Some W_a78e0.
Proof. vm_refl. Qed.
Lemma D_a78e0 : decode_any W_a78e0 = Some (Branch BC_EQ 27 13 452, 4%Z).
Proof. vm_refl. Qed.

Definition W_a78e4 : bv 32 := 0x0120b6b3.
Lemma F_a78e4 : fetch_word Ubsan.M.loaded_segments (0xa78e4 : word) = Some W_a78e4.
Proof. vm_refl. Qed.
Lemma D_a78e4 : decode_any W_a78e4 = Some (Op ALU_SLTU 13 1 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_a78e8 : bv 32 := 0x00062613.
Lemma F_a78e8 : fetch_word Ubsan.M.loaded_segments (0xa78e8 : word) = Some W_a78e8.
Proof. vm_refl. Qed.
Lemma D_a78e8 : decode_any W_a78e8 = Some (OpImm ALU_SLT 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a78ec : bv 32 := 0x00c6c633.
Lemma F_a78ec : fetch_word Ubsan.M.loaded_segments (0xa78ec : word) = Some W_a78ec.
Proof. vm_refl. Qed.
Lemma D_a78ec : decode_any W_a78ec = Some (Op ALU_XOR 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a78f0 : bv 32 := 0x00164613.
Lemma F_a78f0 : fetch_word Ubsan.M.loaded_segments (0xa78f0 : word) = Some W_a78f0.
Proof. vm_refl. Qed.
Lemma D_a78f0 : decode_any W_a78f0 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a78f4 : bv 32 := 0x1a060863.
Lemma F_a78f4 : fetch_word Ubsan.M.loaded_segments (0xa78f4 : word) = Some W_a78f4.
Proof. vm_refl. Qed.
Lemma D_a78f4 : decode_any W_a78f4 = Some (Branch BC_EQ 12 0 432, 4%Z).
Proof. vm_refl. Qed.

Definition W_a78f8 : bv 32 := 0x04013603.
Lemma F_a78f8 : fetch_word Ubsan.M.loaded_segments (0xa78f8 : word) = Some W_a78f8.
Proof. vm_refl. Qed.
Lemma D_a78f8 : decode_any W_a78f8 = Some (Load SZ8 true 12 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a78fc : bv 32 := 0x10c05063.
Lemma F_a78fc : fetch_word Ubsan.M.loaded_segments (0xa78fc : word) = Some W_a78fc.
Proof. vm_refl. Qed.
Lemma D_a78fc : decode_any W_a78fc = Some (Branch BC_GE 0 12 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7900 : bv 32 := 0x00000a93.
Lemma F_a7900 : fetch_word Ubsan.M.loaded_segments (0xa7900 : word) = Some W_a7900.
Proof. vm_refl. Qed.
Lemma D_a7900 : decode_any W_a7900 = Some (OpImm ALU_ADD 21 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7904 : bv 32 := 0x00281993.
Lemma F_a7904 : fetch_word Ubsan.M.loaded_segments (0xa7904 : word) = Some W_a7904.
Proof. vm_refl. Qed.
Lemma D_a7904 : decode_any W_a7904 = Some (ShiftImm ALU_SLL 19 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7908 : bv 32 := 0x00279613.
Lemma F_a7908 : fetch_word Ubsan.M.loaded_segments (0xa7908 : word) = Some W_a7908.
Proof. vm_refl. Qed.
Lemma D_a7908 : decode_any W_a7908 = Some (ShiftImm ALU_SLL 12 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a790c : bv 32 := 0x04813683.
Lemma F_a790c : fetch_word Ubsan.M.loaded_segments (0xa790c : word) = Some W_a790c.
Proof. vm_refl. Qed.
Lemma D_a790c : decode_any W_a790c = Some (Load SZ8 true 13 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7910 : bv 32 := 0x0006a693.
Lemma F_a7910 : fetch_word Ubsan.M.loaded_segments (0xa7910 : word) = Some W_a7910.
Proof. vm_refl. Qed.
Lemma D_a7910 : decode_any W_a7910 = Some (OpImm ALU_SLT 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7914 : bv 32 := 0x02813703.
Lemma F_a7914 : fetch_word Ubsan.M.loaded_segments (0xa7914 : word) = Some W_a7914.
Proof. vm_refl. Qed.
Lemma D_a7914 : decode_any W_a7914 = Some (Load SZ8 true 14 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7918 : bv 32 := 0x01a70733.
Lemma F_a7918 : fetch_word Ubsan.M.loaded_segments (0xa7918 : word) = Some W_a7918.
Proof. vm_refl. Qed.
Lemma D_a7918 : decode_any W_a7918 = Some (Op ALU_ADD 14 14 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_a791c : bv 32 := 0x02013303.
Lemma F_a791c : fetch_word Ubsan.M.loaded_segments (0xa791c : word) = Some W_a791c.
Proof. vm_refl. Qed.
Lemma D_a791c : decode_any W_a791c = Some (Load SZ8 true 6 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7920 : bv 32 := 0x006d0333.
Lemma F_a7920 : fetch_word Ubsan.M.loaded_segments (0xa7920 : word) = Some W_a7920.
Proof. vm_refl. Qed.
Lemma D_a7920 : decode_any W_a7920 = Some (Op ALU_ADD 6 26 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7924 : bv 32 := 0x013909b3.
Lemma F_a7924 : fetch_word Ubsan.M.loaded_segments (0xa7924 : word) = Some W_a7924.
Proof. vm_refl. Qed.
Lemma D_a7924 : decode_any W_a7924 = Some (Op ALU_ADD 19 18 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7928 : bv 32 := 0x05013c83.
Lemma F_a7928 : fetch_word Ubsan.M.loaded_segments (0xa7928 : word) = Some W_a7928.
Proof. vm_refl. Qed.
Lemma D_a7928 : decode_any W_a7928 = Some (Load SZ8 true 25 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a792c : bv 32 := 0x00cc8cb3.
Lemma F_a792c : fetch_word Ubsan.M.loaded_segments (0xa792c : word) = Some W_a792c.
Proof. vm_refl. Qed.
Lemma D_a792c : decode_any W_a792c = Some (Op ALU_ADD 25 25 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7930 : bv 32 := 0x01813f03.
Lemma F_a7930 : fetch_word Ubsan.M.loaded_segments (0xa7930 : word) = Some W_a7930.
Proof. vm_refl. Qed.
Lemma D_a7930 : decode_any W_a7930 = Some (Load SZ8 true 30 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7934 : bv 32 := 0x00cf0633.
Lemma F_a7934 : fetch_word Ubsan.M.loaded_segments (0xa7934 : word) = Some W_a7934.
Proof. vm_refl. Qed.
Lemma D_a7934 : decode_any W_a7934 = Some (Op ALU_ADD 12 30 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7938 : bv 32 := 0x00e03f33.
Lemma F_a7938 : fetch_word Ubsan.M.loaded_segments (0xa7938 : word) = Some W_a7938.
Proof. vm_refl. Qed.
Lemma D_a7938 : decode_any W_a7938 = Some (Op ALU_SLTU 30 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_a793c : bv 32 := 0x01a73733.
Lemma F_a793c : fetch_word Ubsan.M.loaded_segments (0xa793c : word) = Some W_a793c.
Proof. vm_refl. Qed.
Lemma D_a793c : decode_any W_a793c = Some (Op ALU_SLTU 14 14 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7940 : bv 32 := 0x00d746b3.
Lemma F_a7940 : fetch_word Ubsan.M.loaded_segments (0xa7940 : word) = Some W_a7940.
Proof. vm_refl. Qed.
Lemma D_a7940 : decode_any W_a7940 = Some (Op ALU_XOR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7944 : bv 32 := 0x0016c693.
Lemma F_a7944 : fetch_word Ubsan.M.loaded_segments (0xa7944 : word) = Some W_a7944.
Proof. vm_refl. Qed.
Lemma D_a7944 : decode_any W_a7944 = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7948 : bv 32 := 0x00df7f33.
Lemma F_a7948 : fetch_word Ubsan.M.loaded_segments (0xa7948 : word) = Some W_a7948.
Proof. vm_refl. Qed.
Lemma D_a7948 : decode_any W_a7948 = Some (Op ALU_AND 30 30 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a794c : bv 32 := 0xfff34313.
Lemma F_a794c : fetch_word Ubsan.M.loaded_segments (0xa794c : word) = Some W_a794c.
Proof. vm_refl. Qed.
Lemma D_a794c : decode_any W_a794c = Some (OpImm ALU_XOR 6 6 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7950 : bv 32 := 0x04013b83.
Lemma F_a7950 : fetch_word Ubsan.M.loaded_segments (0xa7950 : word) = Some W_a7950.
Proof. vm_refl. Qed.
Lemma D_a7950 : decode_any W_a7950 = Some (Load SZ8 true 23 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7954 : bv 32 := 0x00098413.
Lemma F_a7954 : fetch_word Ubsan.M.loaded_segments (0xa7954 : word) = Some W_a7954.
Proof. vm_refl. Qed.
Lemma D_a7954 : decode_any W_a7954 = Some (OpImm ALU_ADD 8 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7958 : bv 32 := 0x015c8fb3.
Lemma F_a7958 : fetch_word Ubsan.M.loaded_segments (0xa7958 : word) = Some W_a7958.
Proof. vm_refl. Qed.
Lemma D_a7958 : decode_any W_a7958 = Some (Op ALU_ADD 31 25 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_a795c : bv 32 := 0x15afe463.
Lemma F_a795c : fetch_word Ubsan.M.loaded_segments (0xa795c : word) = Some W_a795c.
Proof. vm_refl. Qed.
Lemma D_a795c : decode_any W_a795c = Some (Branch BC_LTU 31 26 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7960 : bv 32 := 0x001fb693.
Lemma F_a7960 : fetch_word Ubsan.M.loaded_segments (0xa7960 : word) = Some W_a7960.
Proof. vm_refl. Qed.
Lemma D_a7960 : decode_any W_a7960 = Some (OpImm ALU_SLTU 13 31 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7964 : bv 32 := 0x00dec6b3.
Lemma F_a7964 : fetch_word Ubsan.M.loaded_segments (0xa7964 : word) = Some W_a7964.
Proof. vm_refl. Qed.
Lemma D_a7964 : decode_any W_a7964 = Some (Op ALU_XOR 13 29 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7968 : bv 32 := 0x12068e63.
Lemma F_a7968 : fetch_word Ubsan.M.loaded_segments (0xa7968 : word) = Some W_a7968.
Proof. vm_refl. Qed.
Lemma D_a7968 : decode_any W_a7968 = Some (Branch BC_EQ 13 0 316, 4%Z).
Proof. vm_refl. Qed.

Definition W_a796c : bv 32 := 0x120c0c63.
Lemma F_a796c : fetch_word Ubsan.M.loaded_segments (0xa796c : word) = Some W_a796c.
Proof. vm_refl. Qed.
Lemma D_a796c : decode_any W_a796c = Some (Branch BC_EQ 24 0 312, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7970 : bv 32 := 0x120f0a63.
Lemma F_a7970 : fetch_word Ubsan.M.loaded_segments (0xa7970 : word) = Some W_a7970.
Proof. vm_refl. Qed.
Lemma D_a7970 : decode_any W_a7970 = Some (Branch BC_EQ 30 0 308, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7974 : bv 32 := 0x13536863.
Lemma F_a7974 : fetch_word Ubsan.M.loaded_segments (0xa7974 : word) = Some W_a7974.
Proof. vm_refl. Qed.
Lemma D_a7974 : decode_any W_a7974 = Some (Branch BC_LTU 6 21 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7978 : bv 32 := 0x015606b3.
Lemma F_a7978 : fetch_word Ubsan.M.loaded_segments (0xa7978 : word) = Some W_a7978.
Proof. vm_refl. Qed.
Lemma D_a7978 : decode_any W_a7978 = Some (Op ALU_ADD 13 12 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_a797c : bv 32 := 0x000fa703.
Lemma F_a797c : fetch_word Ubsan.M.loaded_segments (0xa797c : word) = Some W_a797c.
Proof. vm_refl. Qed.
Lemma D_a797c : decode_any W_a797c = Some (Load SZ4 true 14 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7980 : bv 32 := 0x0006a683.
Lemma F_a7980 : fetch_word Ubsan.M.loaded_segments (0xa7980 : word) = Some W_a7980.
Proof. vm_refl. Qed.
Lemma D_a7980 : decode_any W_a7980 = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7984 : bv 32 := 0x00e6f6b3.
Lemma F_a7984 : fetch_word Ubsan.M.loaded_segments (0xa7984 : word) = Some W_a7984.
Proof. vm_refl. Qed.
Lemma D_a7984 : decode_any W_a7984 = Some (Op ALU_AND 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7988 : bv 32 := 0x00169713.
Lemma F_a7988 : fetch_word Ubsan.M.loaded_segments (0xa7988 : word) = Some W_a7988.
Proof. vm_refl. Qed.
Lemma D_a7988 : decode_any W_a7988 = Some (ShiftImm ALU_SLL 14 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a798c : bv 32 := 0x0166f6b3.
Lemma F_a798c : fetch_word Ubsan.M.loaded_segments (0xa798c : word) = Some W_a798c.
Proof. vm_refl. Qed.
Lemma D_a798c : decode_any W_a798c = Some (Op ALU_AND 13 13 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7990 : bv 32 := 0x00e6f6b3.
Lemma F_a7990 : fetch_word Ubsan.M.loaded_segments (0xa7990 : word) = Some W_a7990.
Proof. vm_refl. Qed.
Lemma D_a7990 : decode_any W_a7990 = Some (Op ALU_AND 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7994 : bv 32 := 0x00769713.
Lemma F_a7994 : fetch_word Ubsan.M.loaded_segments (0xa7994 : word) = Some W_a7994.
Proof. vm_refl. Qed.
Lemma D_a7994 : decode_any W_a7994 = Some (ShiftImm ALU_SLL 14 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7998 : bv 32 := 0x00d706b3.
Lemma F_a7998 : fetch_word Ubsan.M.loaded_segments (0xa7998 : word) = Some W_a7998.
Proof. vm_refl. Qed.
Lemma D_a7998 : decode_any W_a7998 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a799c : bv 32 := 0x0186df9b.
Lemma F_a799c : fetch_word Ubsan.M.loaded_segments (0xa799c : word) = Some W_a799c.
Proof. vm_refl. Qed.
Lemma D_a799c : decode_any W_a799c = Some (ShiftImm32 ALU_SRL 31 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a79a0 : bv 32 := 0x11f3e263.
Lemma F_a79a0 : fetch_word Ubsan.M.loaded_segments (0xa79a0 : word) = Some W_a79a0.
Proof. vm_refl. Qed.
Lemma D_a79a0 : decode_any W_a79a0 = Some (Branch BC_LTU 7 31 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_a79a4 : bv 32 := 0x03069693.
Lemma F_a79a4 : fetch_word Ubsan.M.loaded_segments (0xa79a4 : word) = Some W_a79a4.
Proof. vm_refl. Qed.
Lemma D_a79a4 : decode_any W_a79a4 = Some (ShiftImm ALU_SLL 13 13 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a79a8 : bv 32 := 0x0386d693.
Lemma F_a79a8 : fetch_word Ubsan.M.loaded_segments (0xa79a8 : word) = Some W_a79a8.
Proof. vm_refl. Qed.
Lemma D_a79a8 : decode_any W_a79a8 = Some (ShiftImm ALU_SRL 13 13 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a79ac : bv 32 := 0x0ed3ec63.
Lemma F_a79ac : fetch_word Ubsan.M.loaded_segments (0xa79ac : word) = Some W_a79ac.
Proof. vm_refl. Qed.
Lemma D_a79ac : decode_any W_a79ac = Some (Branch BC_LTU 7 13 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_a79b0 : bv 32 := 0x0e146a63.
Lemma F_a79b0 : fetch_word Ubsan.M.loaded_segments (0xa79b0 : word) = Some W_a79b0.
Proof. vm_refl. Qed.
Lemma D_a79b0 : decode_any W_a79b0 = Some (Branch BC_LTU 8 1 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_a79b4 : bv 32 := 0x00143713.
Lemma F_a79b4 : fetch_word Ubsan.M.loaded_segments (0xa79b4 : word) = Some W_a79b4.
Proof. vm_refl. Qed.
Lemma D_a79b4 : decode_any W_a79b4 = Some (OpImm ALU_SLTU 14 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a79b8 : bv 32 := 0x00edc733.
Lemma F_a79b8 : fetch_word Ubsan.M.loaded_segments (0xa79b8 : word) = Some W_a79b8.
Proof. vm_refl. Qed.
Lemma D_a79b8 : decode_any W_a79b8 = Some (Op ALU_XOR 14 27 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_a79bc : bv 32 := 0x0e070463.
Lemma F_a79bc : fetch_word Ubsan.M.loaded_segments (0xa79bc : word) = Some W_a79bc.
Proof. vm_refl. Qed.
Lemma D_a79bc : decode_any W_a79bc = Some (Branch BC_EQ 14 0 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_a79c0 : bv 32 := 0x0e0e1263.
Lemma F_a79c0 : fetch_word Ubsan.M.loaded_segments (0xa79c0 : word) = Some W_a79c0.
Proof. vm_refl. Qed.
Lemma D_a79c0 : decode_any W_a79c0 = Some (Branch BC_NE 28 0 228, 4%Z).
Proof. vm_refl. Qed.

Definition W_a79c4 : bv 32 := 0x0f498063.
Lemma F_a79c4 : fetch_word Ubsan.M.loaded_segments (0xa79c4 : word) = Some W_a79c4.
Proof. vm_refl. Qed.
Lemma D_a79c4 : decode_any W_a79c4 = Some (Branch BC_EQ 19 20 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_a79c8 : bv 32 := 0x00d586b3.
Lemma F_a79c8 : fetch_word Ubsan.M.loaded_segments (0xa79c8 : word) = Some W_a79c8.
Proof. vm_refl. Qed.
Lemma D_a79c8 : decode_any W_a79c8 = Some (Op ALU_ADD 13 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a79cc : bv 32 := 0x01f58fb3.
Lemma F_a79cc : fetch_word Ubsan.M.loaded_segments (0xa79cc : word) = Some W_a79cc.
Proof. vm_refl. Qed.
Lemma D_a79cc : decode_any W_a79cc = Some (Op ALU_ADD 31 11 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_a79d0 : bv 32 := 0x000fc703.
Lemma F_a79d0 : fetch_word Ubsan.M.loaded_segments (0xa79d0 : word) = Some W_a79d0.
Proof. vm_refl. Qed.
Lemma D_a79d0 : decode_any W_a79d0 = Some (Load SZ1 false 14 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a79d4 : bv 32 := 0x0006c683.
Lemma F_a79d4 : fetch_word Ubsan.M.loaded_segments (0xa79d4 : word) = Some W_a79d4.
Proof. vm_refl. Qed.
Lemma D_a79d4 : decode_any W_a79d4 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a79d8 : bv 32 := 0x00871713.
Lemma F_a79d8 : fetch_word Ubsan.M.loaded_segments (0xa79d8 : word) = Some W_a79d8.
Proof. vm_refl. Qed.
Lemma D_a79d8 : decode_any W_a79d8 = Some (ShiftImm ALU_SLL 14 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a79dc : bv 32 := 0x00d766b3.
Lemma F_a79dc : fetch_word Ubsan.M.loaded_segments (0xa79dc : word) = Some W_a79dc.
Proof. vm_refl. Qed.
Lemma D_a79dc : decode_any W_a79dc = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a79e0 : bv 32 := 0x00244713.
Lemma F_a79e0 : fetch_word Ubsan.M.loaded_segments (0xa79e0 : word) = Some W_a79e0.
Proof. vm_refl. Qed.
Lemma D_a79e0 : decode_any W_a79e0 = Some (OpImm ALU_XOR 14 8 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a79e4 : bv 32 := 0x00240413.
Lemma F_a79e4 : fetch_word Ubsan.M.loaded_segments (0xa79e4 : word) = Some W_a79e4.
Proof. vm_refl. Qed.
Lemma D_a79e4 : decode_any W_a79e4 = Some (OpImm ALU_ADD 8 8 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a79e8 : bv 32 := 0x004a8a93.
Lemma F_a79e8 : fetch_word Ubsan.M.loaded_segments (0xa79e8 : word) = Some W_a79e8.
Proof. vm_refl. Qed.
Lemma D_a79e8 : decode_any W_a79e8 = Some (OpImm ALU_ADD 21 21 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a79ec : bv 32 := 0xfffb8b93.
Lemma F_a79ec : fetch_word Ubsan.M.loaded_segments (0xa79ec : word) = Some W_a79ec.
Proof. vm_refl. Qed.
Lemma D_a79ec : decode_any W_a79ec = Some (OpImm ALU_ADD 23 23 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a79f0 : bv 32 := 0x00d71023.
Lemma F_a79f0 : fetch_word Ubsan.M.loaded_segments (0xa79f0 : word) = Some W_a79f0.
Proof. vm_refl. Qed.
Lemma D_a79f0 : decode_any W_a79f0 = Some (Store SZ2 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a79f4 : bv 32 := 0x00298993.
Lemma F_a79f4 : fetch_word Ubsan.M.loaded_segments (0xa79f4 : word) = Some W_a79f4.
Proof. vm_refl. Qed.
Lemma D_a79f4 : decode_any W_a79f4 = Some (OpImm ALU_ADD 19 19 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a79f8 : bv 32 := 0xf60b90e3.
Lemma F_a79f8 : fetch_word Ubsan.M.loaded_segments (0xa79f8 : word) = Some W_a79f8.
Proof. vm_refl. Qed.
Lemma D_a79f8 : decode_any W_a79f8 = Some (Branch BC_NE 23 0 8032, 4%Z).
Proof. vm_refl. Qed.

Definition W_a79fc : bv 32 := 0x0a988463.
Lemma F_a79fc : fetch_word Ubsan.M.loaded_segments (0xa79fc : word) = Some W_a79fc.
Proof. vm_refl. Qed.
Lemma D_a79fc : decode_any W_a79fc = Some (Branch BC_EQ 17 9 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a00 : bv 32 := 0x0022829b.
Lemma F_a7a00 : fetch_word Ubsan.M.loaded_segments (0xa7a00 : word) = Some W_a7a00.
Proof. vm_refl. Qed.
Lemma D_a7a00 : decode_any W_a7a00 = Some (OpImm32 5 5 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a04 : bv 32 := 0x0018889b.
Lemma F_a7a04 : fetch_word Ubsan.M.loaded_segments (0xa7a04 : word) = Some W_a7a04.
Proof. vm_refl. Qed.
Lemma D_a7a04 : decode_any W_a7a04 = Some (OpImm32 17 17 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a08 : bv 32 := 0x00a8083b.
Lemma F_a7a08 : fetch_word Ubsan.M.loaded_segments (0xa7a08 : word) = Some W_a7a08.
Proof. vm_refl. Qed.
Lemma D_a7a08 : decode_any W_a7a08 = Some (Op32 ALU_ADD 16 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a0c : bv 32 := 0x03013603.
Lemma F_a7a0c : fetch_word Ubsan.M.loaded_segments (0xa7a0c : word) = Some W_a7a0c.
Proof. vm_refl. Qed.
Lemma D_a7a0c : decode_any W_a7a0c = Some (Load SZ8 true 12 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a10 : bv 32 := 0x00c787bb.
Lemma F_a7a10 : fetch_word Ubsan.M.loaded_segments (0xa7a10 : word) = Some W_a7a10.
Proof. vm_refl. Qed.
Lemma D_a7a10 : decode_any W_a7a10 = Some (Op32 ALU_ADD 15 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a14 : bv 32 := 0x03813603.
Lemma F_a7a14 : fetch_word Ubsan.M.loaded_segments (0xa7a14 : word) = Some W_a7a14.
Proof. vm_refl. Qed.
Lemma D_a7a14 : decode_any W_a7a14 = Some (Load SZ8 true 12 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a18 : bv 32 := 0xe6c2c4e3.
Lemma F_a7a18 : fetch_word Ubsan.M.loaded_segments (0xa7a18 : word) = Some W_a7a18.
Proof. vm_refl. Qed.
Lemma D_a7a18 : decode_any W_a7a18 = Some (Branch BC_LT 5 12 7784, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a1c : bv 32 := 0x00013503.
Lemma F_a7a1c : fetch_word Ubsan.M.loaded_segments (0xa7a1c : word) = Some W_a7a1c.
Proof. vm_refl. Qed.
Lemma D_a7a1c : decode_any W_a7a1c = Some (Load SZ8 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a20 : bv 32 := 0x00051663.
Lemma F_a7a20 : fetch_word Ubsan.M.loaded_segments (0xa7a20 : word) = Some W_a7a20.
Proof. vm_refl. Qed.
Lemma D_a7a20 : decode_any W_a7a20 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a24 : bv 32 := 0x00058513.
Lemma F_a7a24 : fetch_word Ubsan.M.loaded_segments (0xa7a24 : word) = Some W_a7a24.
Proof. vm_refl. Qed.
Lemma D_a7a24 : decode_any W_a7a24 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a28 : bv 32 := 0x5f1660ef.
Lemma F_a7a28 : fetch_word Ubsan.M.loaded_segments (0xa7a28 : word) = Some W_a7a28.
Proof. vm_refl. Qed.
Lemma D_a7a28 : decode_any W_a7a28 = Some (Jal 1 421360, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a2c : bv 32 := 0x00813503.
Lemma F_a7a2c : fetch_word Ubsan.M.loaded_segments (0xa7a2c : word) = Some W_a7a2c.
Proof. vm_refl. Qed.
Lemma D_a7a2c : decode_any W_a7a2c = Some (Load SZ8 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a30 : bv 32 := 0x0380006f.
Lemma F_a7a30 : fetch_word Ubsan.M.loaded_segments (0xa7a30 : word) = Some W_a7a30.
Proof. vm_refl. Qed.
Lemma D_a7a30 : decode_any W_a7a30 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a34 : bv 32 := 0x05810513.
Lemma F_a7a34 : fetch_word Ubsan.M.loaded_segments (0xa7a34 : word) = Some W_a7a34.
Proof. vm_refl. Qed.
Lemma D_a7a34 : decode_any W_a7a34 = Some (OpImm ALU_ADD 10 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a38 : bv 32 := 0xd60c60ef.
Lemma F_a7a38 : fetch_word Ubsan.M.loaded_segments (0xa7a38 : word) = Some W_a7a38.
Proof. vm_refl. Qed.
Lemma D_a7a38 : decode_any W_a7a38 = Some (Jal 1 1860960, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a3c : bv 32 := 0x0007f517.
Lemma F_a7a3c : fetch_word Ubsan.M.loaded_segments (0xa7a3c : word) = Some W_a7a3c.
Proof. vm_refl. Qed.
Lemma D_a7a3c : decode_any W_a7a3c = Some (Auipc 10 127, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a40 : bv 32 := 0x03453503.
Lemma F_a7a40 : fetch_word Ubsan.M.loaded_segments (0xa7a40 : word) = Some W_a7a40.
Proof. vm_refl. Qed.
Lemma D_a7a40 : decode_any W_a7a40 = Some (Load SZ8 true 10 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a44 : bv 32 := 0x00052503.
Lemma F_a7a44 : fetch_word Ubsan.M.loaded_segments (0xa7a44 : word) = Some W_a7a44.
Proof. vm_refl. Qed.
Lemma D_a7a44 : decode_any W_a7a44 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a48 : bv 32 := 0x00500593.
Lemma F_a7a48 : fetch_word Ubsan.M.loaded_segments (0xa7a48 : word) = Some W_a7a48.
Proof. vm_refl. Qed.
Lemma D_a7a48 : decode_any W_a7a48 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a4c : bv 32 := 0x00a5cc63.
Lemma F_a7a4c : fetch_word Ubsan.M.loaded_segments (0xa7a4c : word) = Some W_a7a4c.
Proof. vm_refl. Qed.
Lemma D_a7a4c : decode_any W_a7a4c = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a50 : bv 32 := 0xfff6a517.
Lemma F_a7a50 : fetch_word Ubsan.M.loaded_segments (0xa7a50 : word) = Some W_a7a50.
Proof. vm_refl. Qed.
Lemma D_a7a50 : decode_any W_a7a50 = Some (Auipc 10 1048426, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a54 : bv 32 := 0xfff6f597.
Lemma F_a7a54 : fetch_word Ubsan.M.loaded_segments (0xa7a54 : word) = Some W_a7a54.
Proof. vm_refl. Qed.
Lemma D_a7a54 : decode_any W_a7a54 = Some (Auipc 11 1048431, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a58 : bv 32 := 0xfb150513.
Lemma F_a7a58 : fetch_word Ubsan.M.loaded_segments (0xa7a58 : word) = Some W_a7a58.
Proof. vm_refl. Qed.
Lemma D_a7a58 : decode_any W_a7a58 = Some (OpImm ALU_ADD 10 10 4017, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a5c : bv 32 := 0x93258593.
Lemma F_a7a5c : fetch_word Ubsan.M.loaded_segments (0xa7a5c : word) = Some W_a7a5c.
Proof. vm_refl. Qed.
Lemma D_a7a5c : decode_any W_a7a5c = Some (OpImm ALU_ADD 11 11 2354, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a60 : bv 32 := 0x94dff06f.
Lemma F_a7a60 : fetch_word Ubsan.M.loaded_segments (0xa7a60 : word) = Some W_a7a60.
Proof. vm_refl. Qed.
Lemma D_a7a60 : decode_any W_a7a60 = Some (Jal 0 2095436, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a64 : bv 32 := 0x00000513.
Lemma F_a7a64 : fetch_word Ubsan.M.loaded_segments (0xa7a64 : word) = Some W_a7a64.
Proof. vm_refl. Qed.
Lemma D_a7a64 : decode_any W_a7a64 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a68 : bv 32 := 0x0c813083.
Lemma F_a7a68 : fetch_word Ubsan.M.loaded_segments (0xa7a68 : word) = Some W_a7a68.
Proof. vm_refl. Qed.
Lemma D_a7a68 : decode_any W_a7a68 = Some (Load SZ8 true 1 2 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a6c : bv 32 := 0x0c013403.
Lemma F_a7a6c : fetch_word Ubsan.M.loaded_segments (0xa7a6c : word) = Some W_a7a6c.
Proof. vm_refl. Qed.
Lemma D_a7a6c : decode_any W_a7a6c = Some (Load SZ8 true 8 2 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a70 : bv 32 := 0x0b813483.
Lemma F_a7a70 : fetch_word Ubsan.M.loaded_segments (0xa7a70 : word) = Some W_a7a70.
Proof. vm_refl. Qed.
Lemma D_a7a70 : decode_any W_a7a70 = Some (Load SZ8 true 9 2 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a74 : bv 32 := 0x0b013903.
Lemma F_a7a74 : fetch_word Ubsan.M.loaded_segments (0xa7a74 : word) = Some W_a7a74.
Proof. vm_refl. Qed.
Lemma D_a7a74 : decode_any W_a7a74 = Some (Load SZ8 true 18 2 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a78 : bv 32 := 0x0a813983.
Lemma F_a7a78 : fetch_word Ubsan.M.loaded_segments (0xa7a78 : word) = Some W_a7a78.
Proof. vm_refl. Qed.
Lemma D_a7a78 : decode_any W_a7a78 = Some (Load SZ8 true 19 2 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a7c : bv 32 := 0x0a013a03.
Lemma F_a7a7c : fetch_word Ubsan.M.loaded_segments (0xa7a7c : word) = Some W_a7a7c.
Proof. vm_refl. Qed.
Lemma D_a7a7c : decode_any W_a7a7c = Some (Load SZ8 true 20 2 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a80 : bv 32 := 0x09813a83.
Lemma F_a7a80 : fetch_word Ubsan.M.loaded_segments (0xa7a80 : word) = Some W_a7a80.
Proof. vm_refl. Qed.
Lemma D_a7a80 : decode_any W_a7a80 = Some (Load SZ8 true 21 2 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a84 : bv 32 := 0x09013b03.
Lemma F_a7a84 : fetch_word Ubsan.M.loaded_segments (0xa7a84 : word) = Some W_a7a84.
Proof. vm_refl. Qed.
Lemma D_a7a84 : decode_any W_a7a84 = Some (Load SZ8 true 22 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a88 : bv 32 := 0x08813b83.
Lemma F_a7a88 : fetch_word Ubsan.M.loaded_segments (0xa7a88 : word) = Some W_a7a88.
Proof. vm_refl. Qed.
Lemma D_a7a88 : decode_any W_a7a88 = Some (Load SZ8 true 23 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a8c : bv 32 := 0x08013c03.
Lemma F_a7a8c : fetch_word Ubsan.M.loaded_segments (0xa7a8c : word) = Some W_a7a8c.
Proof. vm_refl. Qed.
Lemma D_a7a8c : decode_any W_a7a8c = Some (Load SZ8 true 24 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a90 : bv 32 := 0x07813c83.
Lemma F_a7a90 : fetch_word Ubsan.M.loaded_segments (0xa7a90 : word) = Some W_a7a90.
Proof. vm_refl. Qed.
Lemma D_a7a90 : decode_any W_a7a90 = Some (Load SZ8 true 25 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a94 : bv 32 := 0x07013d03.
Lemma F_a7a94 : fetch_word Ubsan.M.loaded_segments (0xa7a94 : word) = Some W_a7a94.
Proof. vm_refl. Qed.
Lemma D_a7a94 : decode_any W_a7a94 = Some (Load SZ8 true 26 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a98 : bv 32 := 0x06813d83.
Lemma F_a7a98 : fetch_word Ubsan.M.loaded_segments (0xa7a98 : word) = Some W_a7a98.
Proof. vm_refl. Qed.
Lemma D_a7a98 : decode_any W_a7a98 = Some (Load SZ8 true 27 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7a9c : bv 32 := 0x0d010113.
Lemma F_a7a9c : fetch_word Ubsan.M.loaded_segments (0xa7a9c : word) = Some W_a7a9c.
Proof. vm_refl. Qed.
Lemma D_a7a9c : decode_any W_a7a9c = Some (OpImm ALU_ADD 2 2 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7aa0 : bv 32 := 0x00008067.
Lemma F_a7aa0 : fetch_word Ubsan.M.loaded_segments (0xa7aa0 : word) = Some W_a7aa0.
Proof. vm_refl. Qed.
Lemma D_a7aa0 : decode_any W_a7aa0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
