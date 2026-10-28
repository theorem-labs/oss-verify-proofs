(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_18258 : bv 32 := 0xfe010113.
Lemma F_18258 : fetch_word Ubsan.M.loaded_segments (0x18258 : word) = Some W_18258.
Proof. vm_refl. Qed.
Lemma D_18258 : decode_any W_18258 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_1825c : bv 32 := 0x00113c23.
Lemma F_1825c : fetch_word Ubsan.M.loaded_segments (0x1825c : word) = Some W_1825c.
Proof. vm_refl. Qed.
Lemma D_1825c : decode_any W_1825c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18260 : bv 32 := 0x00813823.
Lemma F_18260 : fetch_word Ubsan.M.loaded_segments (0x18260 : word) = Some W_18260.
Proof. vm_refl. Qed.
Lemma D_18260 : decode_any W_18260 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18264 : bv 32 := 0x00913423.
Lemma F_18264 : fetch_word Ubsan.M.loaded_segments (0x18264 : word) = Some W_18264.
Proof. vm_refl. Qed.
Lemma D_18264 : decode_any W_18264 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18268 : bv 32 := 0x00050493.
Lemma F_18268 : fetch_word Ubsan.M.loaded_segments (0x18268 : word) = Some W_18268.
Proof. vm_refl. Qed.
Lemma D_18268 : decode_any W_18268 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1826c : bv 32 := 0x00100513.
Lemma F_1826c : fetch_word Ubsan.M.loaded_segments (0x1826c : word) = Some W_1826c.
Proof. vm_refl. Qed.
Lemma D_1826c : decode_any W_1826c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_18270 : bv 32 := 0x02000593.
Lemma F_18270 : fetch_word Ubsan.M.loaded_segments (0x18270 : word) = Some W_18270.
Proof. vm_refl. Qed.
Lemma D_18270 : decode_any W_18270 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18274 : bv 32 := 0x685230ef.
Lemma F_18274 : fetch_word Ubsan.M.loaded_segments (0x18274 : word) = Some W_18274.
Proof. vm_refl. Qed.
Lemma D_18274 : decode_any W_18274 = Some (Jal 1 147076, 4%Z).
Proof. vm_refl. Qed.

Definition W_18278 : bv 32 := 0x00a13023.
Lemma F_18278 : fetch_word Ubsan.M.loaded_segments (0x18278 : word) = Some W_18278.
Proof. vm_refl. Qed.
Lemma D_18278 : decode_any W_18278 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1827c : bv 32 := 0x0c050063.
Lemma F_1827c : fetch_word Ubsan.M.loaded_segments (0x1827c : word) = Some W_1827c.
Proof. vm_refl. Qed.
Lemma D_1827c : decode_any W_1827c = Some (Branch BC_EQ 10 0 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_18280 : bv 32 := 0x00050413.
Lemma F_18280 : fetch_word Ubsan.M.loaded_segments (0x18280 : word) = Some W_18280.
Proof. vm_refl. Qed.
Lemma D_18280 : decode_any W_18280 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18284 : bv 32 := 0x00757513.
Lemma F_18284 : fetch_word Ubsan.M.loaded_segments (0x18284 : word) = Some W_18284.
Proof. vm_refl. Qed.
Lemma D_18284 : decode_any W_18284 = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_18288 : bv 32 := 0x0a051a63.
Lemma F_18288 : fetch_word Ubsan.M.loaded_segments (0x18288 : word) = Some W_18288.
Proof. vm_refl. Qed.
Lemma D_18288 : decode_any W_18288 = Some (Branch BC_NE 10 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_1828c : bv 32 := 0xfffe8537.
Lemma F_1828c : fetch_word Ubsan.M.loaded_segments (0x1828c : word) = Some W_1828c.
Proof. vm_refl. Qed.
Lemma D_1828c : decode_any W_1828c = Some (Lui 10 1048552, 4%Z).
Proof. vm_refl. Qed.

Definition W_18290 : bv 32 := 0x95f50593.
Lemma F_18290 : fetch_word Ubsan.M.loaded_segments (0x18290 : word) = Some W_18290.
Proof. vm_refl. Qed.
Lemma D_18290 : decode_any W_18290 = Some (OpImm ALU_ADD 11 10 2399, 4%Z).
Proof. vm_refl. Qed.

Definition W_18294 : bv 32 := 0x00b485bb.
Lemma F_18294 : fetch_word Ubsan.M.loaded_segments (0x18294 : word) = Some W_18294.
Proof. vm_refl. Qed.
Lemma D_18294 : decode_any W_18294 = Some (Op32 ALU_ADD 11 9 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_18298 : bv 32 := 0x9605051b.
Lemma F_18298 : fetch_word Ubsan.M.loaded_segments (0x18298 : word) = Some W_18298.
Proof. vm_refl. Qed.
Lemma D_18298 : decode_any W_18298 = Some (OpImm32 10 10 2400, 4%Z).
Proof. vm_refl. Qed.

Definition W_1829c : bv 32 := 0x00a5f463.
Lemma F_1829c : fetch_word Ubsan.M.loaded_segments (0x1829c : word) = Some W_1829c.
Proof. vm_refl. Qed.
Lemma D_1829c : decode_any W_1829c = Some (Branch BC_GEU 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_182a0 : bv 32 := 0x01400493.
Lemma F_182a0 : fetch_word Ubsan.M.loaded_segments (0x182a0 : word) = Some W_182a0.
Proof. vm_refl. Qed.
Lemma D_182a0 : decode_any W_182a0 = Some (OpImm ALU_ADD 9 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_182a4 : bv 32 := 0x00042023.
Lemma F_182a4 : fetch_word Ubsan.M.loaded_segments (0x182a4 : word) = Some W_182a4.
Proof. vm_refl. Qed.
Lemma D_182a4 : decode_any W_182a4 = Some (Store SZ4 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_182a8 : bv 32 := 0x00942223.
Lemma F_182a8 : fetch_word Ubsan.M.loaded_segments (0x182a8 : word) = Some W_182a8.
Proof. vm_refl. Qed.
Lemma D_182a8 : decode_any W_182a8 = Some (Store SZ4 8 9 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_182ac : bv 32 := 0x0310000f.
Lemma F_182ac : fetch_word Ubsan.M.loaded_segments (0x182ac : word) = Some W_182ac.
Proof. vm_refl. Qed.
Lemma D_182ac : decode_any W_182ac = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_182b0 : bv 32 := 0x00100513.
Lemma F_182b0 : fetch_word Ubsan.M.loaded_segments (0x182b0 : word) = Some W_182b0.
Proof. vm_refl. Qed.
Lemma D_182b0 : decode_any W_182b0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_182b4 : bv 32 := 0x00a42423.
Lemma F_182b4 : fetch_word Ubsan.M.loaded_segments (0x182b4 : word) = Some W_182b4.
Proof. vm_refl. Qed.
Lemma D_182b4 : decode_any W_182b4 = Some (Store SZ4 8 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_182b8 : bv 32 := 0x0330000f.
Lemma F_182b8 : fetch_word Ubsan.M.loaded_segments (0x182b8 : word) = Some W_182b8.
Proof. vm_refl. Qed.
Lemma D_182b8 : decode_any W_182b8 = Some (Fence 0 3 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_182bc : bv 32 := 0x00800593.
Lemma F_182bc : fetch_word Ubsan.M.loaded_segments (0x182bc : word) = Some W_182bc.
Proof. vm_refl. Qed.
Lemma D_182bc : decode_any W_182bc = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_182c0 : bv 32 := 0x00048513.
Lemma F_182c0 : fetch_word Ubsan.M.loaded_segments (0x182c0 : word) = Some W_182c0.
Proof. vm_refl. Qed.
Lemma D_182c0 : decode_any W_182c0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_182c4 : bv 32 := 0x635230ef.
Lemma F_182c4 : fetch_word Ubsan.M.loaded_segments (0x182c4 : word) = Some W_182c4.
Proof. vm_refl. Qed.
Lemma D_182c4 : decode_any W_182c4 = Some (Jal 1 146996, 4%Z).
Proof. vm_refl. Qed.

Definition W_182c8 : bv 32 := 0x00a43823.
Lemma F_182c8 : fetch_word Ubsan.M.loaded_segments (0x182c8 : word) = Some W_182c8.
Proof. vm_refl. Qed.
Lemma D_182c8 : decode_any W_182c8 = Some (Store SZ8 8 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_182cc : bv 32 := 0x00048513.
Lemma F_182cc : fetch_word Ubsan.M.loaded_segments (0x182cc : word) = Some W_182cc.
Proof. vm_refl. Qed.
Lemma D_182cc : decode_any W_182cc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_182d0 : bv 32 := 0x3fd000ef.
Lemma F_182d0 : fetch_word Ubsan.M.loaded_segments (0x182d0 : word) = Some W_182d0.
Proof. vm_refl. Qed.
Lemma D_182d0 : decode_any W_182d0 = Some (Jal 1 3068, 4%Z).
Proof. vm_refl. Qed.

Definition W_182d4 : bv 32 := 0x01043583.
Lemma F_182d4 : fetch_word Ubsan.M.loaded_segments (0x182d4 : word) = Some W_182d4.
Proof. vm_refl. Qed.
Lemma D_182d4 : decode_any W_182d4 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_182d8 : bv 32 := 0x00a43c23.
Lemma F_182d8 : fetch_word Ubsan.M.loaded_segments (0x182d8 : word) = Some W_182d8.
Proof. vm_refl. Qed.
Lemma D_182d8 : decode_any W_182d8 = Some (Store SZ8 8 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_182dc : bv 32 := 0x00058463.
Lemma F_182dc : fetch_word Ubsan.M.loaded_segments (0x182dc : word) = Some W_182dc.
Proof. vm_refl. Qed.
Lemma D_182dc : decode_any W_182dc = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_182e0 : bv 32 := 0x04051263.
Lemma F_182e0 : fetch_word Ubsan.M.loaded_segments (0x182e0 : word) = Some W_182e0.
Proof. vm_refl. Qed.
Lemma D_182e0 : decode_any W_182e0 = Some (Branch BC_NE 10 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_182e4 : bv 32 := 0x00010513.
Lemma F_182e4 : fetch_word Ubsan.M.loaded_segments (0x182e4 : word) = Some W_182e4.
Proof. vm_refl. Qed.
Lemma D_182e4 : decode_any W_182e4 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_182e8 : bv 32 := 0x058000ef.
Lemma F_182e8 : fetch_word Ubsan.M.loaded_segments (0x182e8 : word) = Some W_182e8.
Proof. vm_refl. Qed.
Lemma D_182e8 : decode_any W_182e8 = Some (Jal 1 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_182ec : bv 32 := 0x0002d517.
Lemma F_182ec : fetch_word Ubsan.M.loaded_segments (0x182ec : word) = Some W_182ec.
Proof. vm_refl. Qed.
Lemma D_182ec : decode_any W_182ec = Some (Auipc 10 45, 4%Z).
Proof. vm_refl. Qed.

Definition W_182f0 : bv 32 := 0xbac53503.
Lemma F_182f0 : fetch_word Ubsan.M.loaded_segments (0x182f0 : word) = Some W_182f0.
Proof. vm_refl. Qed.
Lemma D_182f0 : decode_any W_182f0 = Some (Load SZ8 true 10 10 2988, 4%Z).
Proof. vm_refl. Qed.

Definition W_182f4 : bv 32 := 0x00052503.
Lemma F_182f4 : fetch_word Ubsan.M.loaded_segments (0x182f4 : word) = Some W_182f4.
Proof. vm_refl. Qed.
Lemma D_182f4 : decode_any W_182f4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_182f8 : bv 32 := 0x00500593.
Lemma F_182f8 : fetch_word Ubsan.M.loaded_segments (0x182f8 : word) = Some W_182f8.
Proof. vm_refl. Qed.
Lemma D_182f8 : decode_any W_182f8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_182fc : bv 32 := 0x02a5c263.
Lemma F_182fc : fetch_word Ubsan.M.loaded_segments (0x182fc : word) = Some W_182fc.
Proof. vm_refl. Qed.
Lemma D_182fc : decode_any W_182fc = Some (Branch BC_LT 11 10 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_18300 : bv 32 := 0xffff9517.
Lemma F_18300 : fetch_word Ubsan.M.loaded_segments (0x18300 : word) = Some W_18300.
Proof. vm_refl. Qed.
Lemma D_18300 : decode_any W_18300 = Some (Auipc 10 1048569, 4%Z).
Proof. vm_refl. Qed.

Definition W_18304 : bv 32 := 0xffff8597.
Lemma F_18304 : fetch_word Ubsan.M.loaded_segments (0x18304 : word) = Some W_18304.
Proof. vm_refl. Qed.
Lemma D_18304 : decode_any W_18304 = Some (Auipc 11 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_18308 : bv 32 := 0x61b50513.
Lemma F_18308 : fetch_word Ubsan.M.loaded_segments (0x18308 : word) = Some W_18308.
Proof. vm_refl. Qed.
Lemma D_18308 : decode_any W_18308 = Some (OpImm ALU_ADD 10 10 1563, 4%Z).
Proof. vm_refl. Qed.

Definition W_1830c : bv 32 := 0x08058593.
Lemma F_1830c : fetch_word Ubsan.M.loaded_segments (0x1830c : word) = Some W_1830c.
Proof. vm_refl. Qed.
Lemma D_1830c : decode_any W_1830c = Some (OpImm ALU_ADD 11 11 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_18310 : bv 32 := 0x00000613.
Lemma F_18310 : fetch_word Ubsan.M.loaded_segments (0x18310 : word) = Some W_18310.
Proof. vm_refl. Qed.
Lemma D_18310 : decode_any W_18310 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18314 : bv 32 := 0xbb1ff0ef.
Lemma F_18314 : fetch_word Ubsan.M.loaded_segments (0x18314 : word) = Some W_18314.
Proof. vm_refl. Qed.
Lemma D_18314 : decode_any W_18314 = Some (Jal 1 2096048, 4%Z).
Proof. vm_refl. Qed.

Definition W_18318 : bv 32 := 0x00050413.
Lemma F_18318 : fetch_word Ubsan.M.loaded_segments (0x18318 : word) = Some W_18318.
Proof. vm_refl. Qed.
Lemma D_18318 : decode_any W_18318 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1831c : bv 32 := 0x0080006f.
Lemma F_1831c : fetch_word Ubsan.M.loaded_segments (0x1831c : word) = Some W_1831c.
Proof. vm_refl. Qed.
Lemma D_1831c : decode_any W_1831c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18320 : bv 32 := 0x00000413.
Lemma F_18320 : fetch_word Ubsan.M.loaded_segments (0x18320 : word) = Some W_18320.
Proof. vm_refl. Qed.
Lemma D_18320 : decode_any W_18320 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18324 : bv 32 := 0x00040513.
Lemma F_18324 : fetch_word Ubsan.M.loaded_segments (0x18324 : word) = Some W_18324.
Proof. vm_refl. Qed.
Lemma D_18324 : decode_any W_18324 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18328 : bv 32 := 0x01813083.
Lemma F_18328 : fetch_word Ubsan.M.loaded_segments (0x18328 : word) = Some W_18328.
Proof. vm_refl. Qed.
Lemma D_18328 : decode_any W_18328 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1832c : bv 32 := 0x01013403.
Lemma F_1832c : fetch_word Ubsan.M.loaded_segments (0x1832c : word) = Some W_1832c.
Proof. vm_refl. Qed.
Lemma D_1832c : decode_any W_1832c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18330 : bv 32 := 0x00813483.
Lemma F_18330 : fetch_word Ubsan.M.loaded_segments (0x18330 : word) = Some W_18330.
Proof. vm_refl. Qed.
Lemma D_18330 : decode_any W_18330 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18334 : bv 32 := 0x02010113.
Lemma F_18334 : fetch_word Ubsan.M.loaded_segments (0x18334 : word) = Some W_18334.
Proof. vm_refl. Qed.
Lemma D_18334 : decode_any W_18334 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18338 : bv 32 := 0x00008067.
Lemma F_18338 : fetch_word Ubsan.M.loaded_segments (0x18338 : word) = Some W_18338.
Proof. vm_refl. Qed.
Lemma D_18338 : decode_any W_18338 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
