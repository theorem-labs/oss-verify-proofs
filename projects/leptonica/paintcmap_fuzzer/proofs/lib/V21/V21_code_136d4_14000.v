(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.H Require GcFlushU21.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.paintcmap_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_13c44 : bv 32 := 0xfd010113.
Lemma F_13c44 : fetch_word Ubsan.M.loaded_segments (0x13d48 : word) = Some W_13c44.
Proof. vm_refl. Qed.
Lemma D_13c44 : decode_any W_13c44 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c48 : bv 32 := 0x02113423.
Lemma F_13c48 : fetch_word Ubsan.M.loaded_segments (0x13d4c : word) = Some W_13c48.
Proof. vm_refl. Qed.
Lemma D_13c48 : decode_any W_13c48 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c4c : bv 32 := 0x02813023.
Lemma F_13c4c : fetch_word Ubsan.M.loaded_segments (0x13d50 : word) = Some W_13c4c.
Proof. vm_refl. Qed.
Lemma D_13c4c : decode_any W_13c4c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c50 : bv 32 := 0x00913c23.
Lemma F_13c50 : fetch_word Ubsan.M.loaded_segments (0x13d54 : word) = Some W_13c50.
Proof. vm_refl. Qed.
Lemma D_13c50 : decode_any W_13c50 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c54 : bv 32 := 0x00058413.
Lemma F_13c54 : fetch_word Ubsan.M.loaded_segments (0x13d58 : word) = Some W_13c54.
Proof. vm_refl. Qed.
Lemma D_13c54 : decode_any W_13c54 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c58 : bv 32 := 0x00300593.
Lemma F_13c58 : fetch_word Ubsan.M.loaded_segments (0x13d5c : word) = Some W_13c58.
Proof. vm_refl. Qed.
Lemma D_13c58 : decode_any W_13c58 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c5c : bv 32 := 0x0cb46063.
Lemma F_13c5c : fetch_word Ubsan.M.loaded_segments (0x13d60 : word) = Some W_13c5c.
Proof. vm_refl. Qed.
Lemma D_13c5c : decode_any W_13c5c = Some (Branch BC_LTU 8 11 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c60 : bv 32 := 0x00050493.
Lemma F_13c60 : fetch_word Ubsan.M.loaded_segments (0x13d64 : word) = Some W_13c60.
Proof. vm_refl. Qed.
Lemma D_13c60 : decode_any W_13c60 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c64 : bv 32 := 0x00000517.
Lemma F_13c64 : fetch_word Ubsan.M.loaded_segments (0x13d68 : word) = Some W_13c64.
Proof. vm_refl. Qed.
Lemma D_13c64 : decode_any W_13c64 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c68 : bv 32 := 0x0d050513.
Lemma F_13c68 : fetch_word Ubsan.M.loaded_segments (0x13d6c : word) = Some W_13c68.
Proof. vm_refl. Qed.
Lemma D_13c68 : decode_any W_13c68 = Some (OpImm ALU_ADD 10 10 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c6c : bv 32 := 0x1e8000ef.
Lemma F_13c6c : fetch_word Ubsan.M.loaded_segments (0x13d70 : word) = Some W_13c6c.
Proof. vm_refl. Qed.
Lemma D_13c6c : decode_any W_13c6c = Some (Jal 1 488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c70 : bv 32 := 0x00048513.
Lemma F_13c70 : fetch_word Ubsan.M.loaded_segments (0x13d74 : word) = Some W_13c70.
Proof. vm_refl. Qed.
Lemma D_13c70 : decode_any W_13c70 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c74 : bv 32 := 0x00040593.
Lemma F_13c74 : fetch_word Ubsan.M.loaded_segments (0x13d78 : word) = Some W_13c74.
Proof. vm_refl. Qed.
Lemma D_13c74 : decode_any W_13c74 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c78 : bv 32 := 0x54c030ef.
Lemma F_13c78 : fetch_word Ubsan.M.loaded_segments (0x13d7c : word) = Some W_13c78.
Proof. vm_refl. Qed.
Lemma D_13c78 : decode_any W_13c78 = Some (Jal 1 13644, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c7c : bv 32 := 0x00a13823.
Lemma F_13c7c : fetch_word Ubsan.M.loaded_segments (0x13d80 : word) = Some W_13c7c.
Proof. vm_refl. Qed.
Lemma D_13c7c : decode_any W_13c7c = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c80 : bv 32 := 0x08050e63.
Lemma F_13c80 : fetch_word Ubsan.M.loaded_segments (0x13d84 : word) = Some W_13c80.
Proof. vm_refl. Qed.
Lemma D_13c80 : decode_any W_13c80 = Some (Branch BC_EQ 10 0 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c84 : bv 32 := 0x00050413.
Lemma F_13c84 : fetch_word Ubsan.M.loaded_segments (0x13d88 : word) = Some W_13c84.
Proof. vm_refl. Qed.
Lemma D_13c84 : decode_any W_13c84 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c88 : bv 32 := 0x11600513.
Lemma F_13c88 : fetch_word Ubsan.M.loaded_segments (0x13d8c : word) = Some W_13c88.
Proof. vm_refl. Qed.
Lemma D_13c88 : decode_any W_13c88 = Some (OpImm ALU_ADD 10 0 278, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c8c : bv 32 := 0x02300593.
Lemma F_13c8c : fetch_word Ubsan.M.loaded_segments (0x13d90 : word) = Some W_13c8c.
Proof. vm_refl. Qed.
Lemma D_13c8c : decode_any W_13c8c = Some (OpImm ALU_ADD 11 0 35, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c90 : bv 32 := 0x07a00613.
Lemma F_13c90 : fetch_word Ubsan.M.loaded_segments (0x13d94 : word) = Some W_13c90.
Proof. vm_refl. Qed.
Lemma D_13c90 : decode_any W_13c90 = Some (OpImm ALU_ADD 12 0 122, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c94 : bv 32 := 0x03200693.
Lemma F_13c94 : fetch_word Ubsan.M.loaded_segments (0x13d98 : word) = Some W_13c94.
Proof. vm_refl. Qed.
Lemma D_13c94 : decode_any W_13c94 = Some (OpImm ALU_ADD 13 0 50, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c98 : bv 32 := 0x3bc000ef.
Lemma F_13c98 : fetch_word Ubsan.M.loaded_segments (0x13d9c : word) = Some W_13c98.
Proof. vm_refl. Qed.
Lemma D_13c98 : decode_any W_13c98 = Some (Jal 1 956, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c9c : bv 32 := 0x00050493.
Lemma F_13c9c : fetch_word Ubsan.M.loaded_segments (0x13da0 : word) = Some W_13c9c.
Proof. vm_refl. Qed.
Lemma D_13c9c : decode_any W_13c9c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ca0 : bv 32 := 0x00a13423.
Lemma F_13ca0 : fetch_word Ubsan.M.loaded_segments (0x13da4 : word) = Some W_13ca0.
Proof. vm_refl. Qed.
Lemma D_13ca0 : decode_any W_13ca0 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ca4 : bv 32 := 0x00000513.
Lemma F_13ca4 : fetch_word Ubsan.M.loaded_segments (0x13da8 : word) = Some W_13ca4.
Proof. vm_refl. Qed.
Lemma D_13ca4 : decode_any W_13ca4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ca8 : bv 32 := 0x00040593.
Lemma F_13ca8 : fetch_word Ubsan.M.loaded_segments (0x13dac : word) = Some W_13ca8.
Proof. vm_refl. Qed.
Lemma D_13ca8 : decode_any W_13ca8 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cac : bv 32 := 0x374010ef.
Lemma F_13cac : fetch_word Ubsan.M.loaded_segments (0x13db0 : word) = Some W_13cac.
Proof. vm_refl. Qed.
Lemma D_13cac : decode_any W_13cac = Some (Jal 1 4980, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cb0 : bv 32 := 0x00a13023.
Lemma F_13cb0 : fetch_word Ubsan.M.loaded_segments (0x13db4 : word) = Some W_13cb0.
Proof. vm_refl. Qed.
Lemma D_13cb0 : decode_any W_13cb0 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cb4 : bv 32 := 0x00200613.
Lemma F_13cb4 : fetch_word Ubsan.M.loaded_segments (0x13db8 : word) = Some W_13cb4.
Proof. vm_refl. Qed.
Lemma D_13cb4 : decode_any W_13cb4 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cb8 : bv 32 := 0x0ff00693.
Lemma F_13cb8 : fetch_word Ubsan.M.loaded_segments (0x13dbc : word) = Some W_13cb8.
Proof. vm_refl. Qed.
Lemma D_13cb8 : decode_any W_13cb8 = Some (OpImm ALU_ADD 13 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cbc : bv 32 := 0x0ff00713.
Lemma F_13cbc : fetch_word Ubsan.M.loaded_segments (0x13dc0 : word) = Some W_13cbc.
Proof. vm_refl. Qed.
Lemma D_13cbc : decode_any W_13cbc = Some (OpImm ALU_ADD 14 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cc0 : bv 32 := 0x06400793.
Lemma F_13cc0 : fetch_word Ubsan.M.loaded_segments (0x13dc4 : word) = Some W_13cc0.
Proof. vm_refl. Qed.
Lemma D_13cc0 : decode_any W_13cc0 = Some (OpImm ALU_ADD 15 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cc4 : bv 32 := 0x00048593.
Lemma F_13cc4 : fetch_word Ubsan.M.loaded_segments (0x13dc8 : word) = Some W_13cc4.
Proof. vm_refl. Qed.
Lemma D_13cc4 : decode_any W_13cc4 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cc8 : bv 32 := 0x2e1020ef.
Lemma F_13cc8 : fetch_word Ubsan.M.loaded_segments (0x13dcc : word) = Some W_13cc8.
Proof. vm_refl. Qed.
Lemma D_13cc8 : decode_any W_13cc8 = Some (Jal 1 10976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ccc : bv 32 := 0x00810513.
Lemma F_13ccc : fetch_word Ubsan.M.loaded_segments (0x13dd0 : word) = Some W_13ccc.
Proof. vm_refl. Qed.
Lemma D_13ccc : decode_any W_13ccc = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cd0 : bv 32 := 0x500000ef.
Lemma F_13cd0 : fetch_word Ubsan.M.loaded_segments (0x13dd4 : word) = Some W_13cd0.
Proof. vm_refl. Qed.
Lemma D_13cd0 : decode_any W_13cd0 = Some (Jal 1 1280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cd4 : bv 32 := 0x00010513.
Lemma F_13cd4 : fetch_word Ubsan.M.loaded_segments (0x13dd8 : word) = Some W_13cd4.
Proof. vm_refl. Qed.
Lemma D_13cd4 : decode_any W_13cd4 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cd8 : bv 32 := 0x3d1000ef.
Lemma F_13cd8 : fetch_word Ubsan.M.loaded_segments (0x13ddc : word) = Some W_13cd8.
Proof. vm_refl. Qed.
Lemma D_13cd8 : decode_any W_13cd8 = Some (Jal 1 3024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cdc : bv 32 := 0x00000513.
Lemma F_13cdc : fetch_word Ubsan.M.loaded_segments (0x13de0 : word) = Some W_13cdc.
Proof. vm_refl. Qed.
Lemma D_13cdc : decode_any W_13cdc = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ce0 : bv 32 := 0x00040593.
Lemma F_13ce0 : fetch_word Ubsan.M.loaded_segments (0x13de4 : word) = Some W_13ce0.
Proof. vm_refl. Qed.
Lemma D_13ce0 : decode_any W_13ce0 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ce4 : bv 32 := 0x33c010ef.
Lemma F_13ce4 : fetch_word Ubsan.M.loaded_segments (0x13de8 : word) = Some W_13ce4.
Proof. vm_refl. Qed.
Lemma D_13ce4 : decode_any W_13ce4 = Some (Jal 1 4924, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ce8 : bv 32 := 0x00a13023.
Lemma F_13ce8 : fetch_word Ubsan.M.loaded_segments (0x13dec : word) = Some W_13ce8.
Proof. vm_refl. Qed.
Lemma D_13ce8 : decode_any W_13ce8 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cec : bv 32 := 0x00100613.
Lemma F_13cec : fetch_word Ubsan.M.loaded_segments (0x13df0 : word) = Some W_13cec.
Proof. vm_refl. Qed.
Lemma D_13cec : decode_any W_13cec = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cf0 : bv 32 := 0x03200693.
Lemma F_13cf0 : fetch_word Ubsan.M.loaded_segments (0x13df4 : word) = Some W_13cf0.
Proof. vm_refl. Qed.
Lemma D_13cf0 : decode_any W_13cf0 = Some (OpImm ALU_ADD 13 0 50, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cf4 : bv 32 := 0x0fa00793.
Lemma F_13cf4 : fetch_word Ubsan.M.loaded_segments (0x13df8 : word) = Some W_13cf4.
Proof. vm_refl. Qed.
Lemma D_13cf4 : decode_any W_13cf4 = Some (OpImm ALU_ADD 15 0 250, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cf8 : bv 32 := 0x0f900813.
Lemma F_13cf8 : fetch_word Ubsan.M.loaded_segments (0x13dfc : word) = Some W_13cf8.
Proof. vm_refl. Qed.
Lemma D_13cf8 : decode_any W_13cf8 = Some (OpImm ALU_ADD 16 0 249, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cfc : bv 32 := 0x0f800893.
Lemma F_13cfc : fetch_word Ubsan.M.loaded_segments (0x13e00 : word) = Some W_13cfc.
Proof. vm_refl. Qed.
Lemma D_13cfc : decode_any W_13cfc = Some (OpImm ALU_ADD 17 0 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d00 : bv 32 := 0x00000593.
Lemma F_13d00 : fetch_word Ubsan.M.loaded_segments (0x13e04 : word) = Some W_13d00.
Proof. vm_refl. Qed.
Lemma D_13d00 : decode_any W_13d00 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d04 : bv 32 := 0x00000713.
Lemma F_13d04 : fetch_word Ubsan.M.loaded_segments (0x13e08 : word) = Some W_13d04.
Proof. vm_refl. Qed.
Lemma D_13d04 : decode_any W_13d04 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d08 : bv 32 := 0x795020ef.
Lemma F_13d08 : fetch_word Ubsan.M.loaded_segments (0x13e0c : word) = Some W_13d08.
Proof. vm_refl. Qed.
Lemma D_13d08 : decode_any W_13d08 = Some (Jal 1 12180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d0c : bv 32 := 0x00010513.
Lemma F_13d0c : fetch_word Ubsan.M.loaded_segments (0x13e10 : word) = Some W_13d0c.
Proof. vm_refl. Qed.
Lemma D_13d0c : decode_any W_13d0c = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d10 : bv 32 := 0x399000ef.
Lemma F_13d10 : fetch_word Ubsan.M.loaded_segments (0x13e14 : word) = Some W_13d10.
Proof. vm_refl. Qed.
Lemma D_13d10 : decode_any W_13d10 = Some (Jal 1 2968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d14 : bv 32 := 0x01010513.
Lemma F_13d14 : fetch_word Ubsan.M.loaded_segments (0x13e18 : word) = Some W_13d14.
Proof. vm_refl. Qed.
Lemma D_13d14 : decode_any W_13d14 = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d18 : bv 32 := 0x391000ef.
Lemma F_13d18 : fetch_word Ubsan.M.loaded_segments (0x13e1c : word) = Some W_13d18.
Proof. vm_refl. Qed.
Lemma D_13d18 : decode_any W_13d18 = Some (Jal 1 2960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d1c : bv 32 := 0x00000513.
Lemma F_13d1c : fetch_word Ubsan.M.loaded_segments (0x13e20 : word) = Some W_13d1c.
Proof. vm_refl. Qed.
Lemma D_13d1c : decode_any W_13d1c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d20 : bv 32 := 0x02813083.
Lemma F_13d20 : fetch_word Ubsan.M.loaded_segments (0x13e24 : word) = Some W_13d20.
Proof. vm_refl. Qed.
Lemma D_13d20 : decode_any W_13d20 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d24 : bv 32 := 0x02013403.
Lemma F_13d24 : fetch_word Ubsan.M.loaded_segments (0x13e28 : word) = Some W_13d24.
Proof. vm_refl. Qed.
Lemma D_13d24 : decode_any W_13d24 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d28 : bv 32 := 0x01813483.
Lemma F_13d28 : fetch_word Ubsan.M.loaded_segments (0x13e2c : word) = Some W_13d28.
Proof. vm_refl. Qed.
Lemma D_13d28 : decode_any W_13d28 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d2c : bv 32 := 0x03010113.
Lemma F_13d2c : fetch_word Ubsan.M.loaded_segments (0x13e30 : word) = Some W_13d2c.
Proof. vm_refl. Qed.
Lemma D_13d2c : decode_any W_13d2c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d30 : bv 32 := 0x00008067.
Lemma F_13d30 : fetch_word Ubsan.M.loaded_segments (0x13e34 : word) = Some W_13d30.
Proof. vm_refl. Qed.
Lemma D_13d30 : decode_any W_13d30 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d38 : bv 32 := 0xff010113.
Lemma F_13d38 : fetch_word Ubsan.M.loaded_segments (0x13e3c : word) = Some W_13d38.
Proof. vm_refl. Qed.
Lemma D_13d38 : decode_any W_13d38 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d3c : bv 32 := 0x00113423.
Lemma F_13d3c : fetch_word Ubsan.M.loaded_segments (0x13e40 : word) = Some W_13d3c.
Proof. vm_refl. Qed.
Lemma D_13d3c : decode_any W_13d3c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d40 : bv 32 := 0x00813023.
Lemma F_13d40 : fetch_word Ubsan.M.loaded_segments (0x13e44 : word) = Some W_13d40.
Proof. vm_refl. Qed.
Lemma D_13d40 : decode_any W_13d40 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d44 : bv 32 := 0x00060413.
Lemma F_13d44 : fetch_word Ubsan.M.loaded_segments (0x13e48 : word) = Some W_13d44.
Proof. vm_refl. Qed.
Lemma D_13d44 : decode_any W_13d44 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d48 : bv 32 := 0x00050613.
Lemma F_13d48 : fetch_word Ubsan.M.loaded_segments (0x13e4c : word) = Some W_13d48.
Proof. vm_refl. Qed.
Lemma D_13d48 : decode_any W_13d48 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d4c : bv 32 := 0xffffd517.
Lemma F_13d4c : fetch_word Ubsan.M.loaded_segments (0x13e50 : word) = Some W_13d4c.
Proof. vm_refl. Qed.
Lemma D_13d4c : decode_any W_13d4c = Some (Auipc 10 1048573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d50 : bv 32 := 0xe9550513.
Lemma F_13d50 : fetch_word Ubsan.M.loaded_segments (0x13e54 : word) = Some W_13d50.
Proof. vm_refl. Qed.
Lemma D_13d50 : decode_any W_13d50 = Some (OpImm ALU_ADD 10 10 3733, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d54 : bv 32 := 0x018000ef.
Lemma F_13d54 : fetch_word Ubsan.M.loaded_segments (0x13e58 : word) = Some W_13d54.
Proof. vm_refl. Qed.
Lemma D_13d54 : decode_any W_13d54 = Some (Jal 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d58 : bv 32 := 0x00040513.
Lemma F_13d58 : fetch_word Ubsan.M.loaded_segments (0x13e5c : word) = Some W_13d58.
Proof. vm_refl. Qed.
Lemma D_13d58 : decode_any W_13d58 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d5c : bv 32 := 0x00813083.
Lemma F_13d5c : fetch_word Ubsan.M.loaded_segments (0x13e60 : word) = Some W_13d5c.
Proof. vm_refl. Qed.
Lemma D_13d5c : decode_any W_13d5c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d60 : bv 32 := 0x00013403.
Lemma F_13d60 : fetch_word Ubsan.M.loaded_segments (0x13e64 : word) = Some W_13d60.
Proof. vm_refl. Qed.
Lemma D_13d60 : decode_any W_13d60 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d64 : bv 32 := 0x01010113.
Lemma F_13d64 : fetch_word Ubsan.M.loaded_segments (0x13e68 : word) = Some W_13d64.
Proof. vm_refl. Qed.
Lemma D_13d64 : decode_any W_13d64 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d68 : bv 32 := 0x00008067.
Lemma F_13d68 : fetch_word Ubsan.M.loaded_segments (0x13e6c : word) = Some W_13d68.
Proof. vm_refl. Qed.
Lemma D_13d68 : decode_any W_13d68 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e08 : bv 32 := 0xff010113.
Lemma F_13e08 : fetch_word Ubsan.M.loaded_segments (0x13f0c : word) = Some W_13e08.
Proof. vm_refl. Qed.
Lemma D_13e08 : decode_any W_13e08 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e0c : bv 32 := 0x00113423.
Lemma F_13e0c : fetch_word Ubsan.M.loaded_segments (0x13f10 : word) = Some W_13e0c.
Proof. vm_refl. Qed.
Lemma D_13e0c : decode_any W_13e0c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e10 : bv 32 := 0x00813023.
Lemma F_13e10 : fetch_word Ubsan.M.loaded_segments (0x13f14 : word) = Some W_13e10.
Proof. vm_refl. Qed.
Lemma D_13e10 : decode_any W_13e10 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e14 : bv 32 := 0x00060413.
Lemma F_13e14 : fetch_word Ubsan.M.loaded_segments (0x13f18 : word) = Some W_13e14.
Proof. vm_refl. Qed.
Lemma D_13e14 : decode_any W_13e14 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e18 : bv 32 := 0x00050613.
Lemma F_13e18 : fetch_word Ubsan.M.loaded_segments (0x13f1c : word) = Some W_13e18.
Proof. vm_refl. Qed.
Lemma D_13e18 : decode_any W_13e18 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e1c : bv 32 := 0xffffd517.
Lemma F_13e1c : fetch_word Ubsan.M.loaded_segments (0x13f20 : word) = Some W_13e1c.
Proof. vm_refl. Qed.
Lemma D_13e1c : decode_any W_13e1c = Some (Auipc 10 1048573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e20 : bv 32 := 0xdc550513.
Lemma F_13e20 : fetch_word Ubsan.M.loaded_segments (0x13f24 : word) = Some W_13e20.
Proof. vm_refl. Qed.
Lemma D_13e20 : decode_any W_13e20 = Some (OpImm ALU_ADD 10 10 3525, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e24 : bv 32 := 0xf49ff0ef.
Lemma F_13e24 : fetch_word Ubsan.M.loaded_segments (0x13f28 : word) = Some W_13e24.
Proof. vm_refl. Qed.
Lemma D_13e24 : decode_any W_13e24 = Some (Jal 1 2096968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e28 : bv 32 := 0x00040513.
Lemma F_13e28 : fetch_word Ubsan.M.loaded_segments (0x13f2c : word) = Some W_13e28.
Proof. vm_refl. Qed.
Lemma D_13e28 : decode_any W_13e28 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e2c : bv 32 := 0x00813083.
Lemma F_13e2c : fetch_word Ubsan.M.loaded_segments (0x13f30 : word) = Some W_13e2c.
Proof. vm_refl. Qed.
Lemma D_13e2c : decode_any W_13e2c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e30 : bv 32 := 0x00013403.
Lemma F_13e30 : fetch_word Ubsan.M.loaded_segments (0x13f34 : word) = Some W_13e30.
Proof. vm_refl. Qed.
Lemma D_13e30 : decode_any W_13e30 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e34 : bv 32 := 0x01010113.
Lemma F_13e34 : fetch_word Ubsan.M.loaded_segments (0x13f38 : word) = Some W_13e34.
Proof. vm_refl. Qed.
Lemma D_13e34 : decode_any W_13e34 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e38 : bv 32 := 0x00008067.
Lemma F_13e38 : fetch_word Ubsan.M.loaded_segments (0x13f3c : word) = Some W_13e38.
Proof. vm_refl. Qed.
Lemma D_13e38 : decode_any W_13e38 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e54 : bv 32 := 0x00051663.
Lemma F_13e54 : fetch_word Ubsan.M.loaded_segments (0x13f58 : word) = Some W_13e54.
Proof. vm_refl. Qed.
Lemma D_13e54 : decode_any W_13e54 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e60 : bv 32 := 0x0000e597.
Lemma F_13e60 : fetch_word Ubsan.M.loaded_segments (0x13f64 : word) = Some W_13e60.
Proof. vm_refl. Qed.
Lemma D_13e60 : decode_any W_13e60 = Some (Auipc 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e64 : bv 32 := 0xf6a5b623.
Lemma F_13e64 : fetch_word Ubsan.M.loaded_segments (0x13f68 : word) = Some W_13e64.
Proof. vm_refl. Qed.
Lemma D_13e64 : decode_any W_13e64 = Some (Store SZ8 11 10 3948, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e68 : bv 32 := 0x00008067.
Lemma F_13e68 : fetch_word Ubsan.M.loaded_segments (0x13f6c : word) = Some W_13e68.
Proof. vm_refl. Qed.
Lemma D_13e68 : decode_any W_13e68 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fa8 : bv 32 := 0xfe010113.
Lemma F_13fa8 : fetch_word Ubsan.M.loaded_segments (0x140ac : word) = Some W_13fa8.
Proof. vm_refl. Qed.
Lemma D_13fa8 : decode_any W_13fa8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fac : bv 32 := 0x00113c23.
Lemma F_13fac : fetch_word Ubsan.M.loaded_segments (0x140b0 : word) = Some W_13fac.
Proof. vm_refl. Qed.
Lemma D_13fac : decode_any W_13fac = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fb0 : bv 32 := 0x00813823.
Lemma F_13fb0 : fetch_word Ubsan.M.loaded_segments (0x140b4 : word) = Some W_13fb0.
Proof. vm_refl. Qed.
Lemma D_13fb0 : decode_any W_13fb0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fb4 : bv 32 := 0x00913423.
Lemma F_13fb4 : fetch_word Ubsan.M.loaded_segments (0x140b8 : word) = Some W_13fb4.
Proof. vm_refl. Qed.
Lemma D_13fb4 : decode_any W_13fb4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fb8 : bv 32 := 0x02050a63.
Lemma F_13fb8 : fetch_word Ubsan.M.loaded_segments (0x140bc : word) = Some W_13fb8.
Proof. vm_refl. Qed.
Lemma D_13fb8 : decode_any W_13fb8 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fbc : bv 32 := 0x00050413.
Lemma F_13fbc : fetch_word Ubsan.M.loaded_segments (0x140c0 : word) = Some W_13fbc.
Proof. vm_refl. Qed.
Lemma D_13fbc : decode_any W_13fbc = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fc0 : bv 32 := 0x00757513.
Lemma F_13fc0 : fetch_word Ubsan.M.loaded_segments (0x140c4 : word) = Some W_13fc0.
Proof. vm_refl. Qed.
Lemma D_13fc0 : decode_any W_13fc0 = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fc4 : bv 32 := 0x08051663.
Lemma F_13fc4 : fetch_word Ubsan.M.loaded_segments (0x140c8 : word) = Some W_13fc4.
Proof. vm_refl. Qed.
Lemma D_13fc4 : decode_any W_13fc4 = Some (Branch BC_NE 10 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fc8 : bv 32 := 0x00058493.
Lemma F_13fc8 : fetch_word Ubsan.M.loaded_segments (0x140cc : word) = Some W_13fc8.
Proof. vm_refl. Qed.
Lemma D_13fc8 : decode_any W_13fc8 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fcc : bv 32 := 0x00043503.
Lemma F_13fcc : fetch_word Ubsan.M.loaded_segments (0x140d0 : word) = Some W_13fcc.
Proof. vm_refl. Qed.
Lemma D_13fcc : decode_any W_13fcc = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fd0 : bv 32 := 0x00050463.
Lemma F_13fd0 : fetch_word Ubsan.M.loaded_segments (0x140d4 : word) = Some W_13fd0.
Proof. vm_refl. Qed.
Lemma D_13fd0 : decode_any W_13fd0 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fd8 : bv 32 := 0x04048863.
Lemma F_13fd8 : fetch_word Ubsan.M.loaded_segments (0x140dc : word) = Some W_13fd8.
Proof. vm_refl. Qed.
Lemma D_13fd8 : decode_any W_13fd8 = Some (Branch BC_EQ 9 0 80, 4%Z).
Proof. vm_refl. Qed.
