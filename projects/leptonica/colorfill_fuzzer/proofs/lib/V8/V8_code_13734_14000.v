(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.H Require GcFlushU8.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.colorfill_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_13ca4 : bv 32 := 0xfd010113.
Lemma F_13ca4 : fetch_word Ubsan.M.loaded_segments (0x13da8 : word) = Some W_13ca4.
Proof. vm_refl. Qed.
Lemma D_13ca4 : decode_any W_13ca4 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ca8 : bv 32 := 0x02113423.
Lemma F_13ca8 : fetch_word Ubsan.M.loaded_segments (0x13dac : word) = Some W_13ca8.
Proof. vm_refl. Qed.
Lemma D_13ca8 : decode_any W_13ca8 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cac : bv 32 := 0x02813023.
Lemma F_13cac : fetch_word Ubsan.M.loaded_segments (0x13db0 : word) = Some W_13cac.
Proof. vm_refl. Qed.
Lemma D_13cac : decode_any W_13cac = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cb0 : bv 32 := 0x00913c23.
Lemma F_13cb0 : fetch_word Ubsan.M.loaded_segments (0x13db4 : word) = Some W_13cb0.
Proof. vm_refl. Qed.
Lemma D_13cb0 : decode_any W_13cb0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cb4 : bv 32 := 0x00058413.
Lemma F_13cb4 : fetch_word Ubsan.M.loaded_segments (0x13db8 : word) = Some W_13cb4.
Proof. vm_refl. Qed.
Lemma D_13cb4 : decode_any W_13cb4 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cb8 : bv 32 := 0x00300593.
Lemma F_13cb8 : fetch_word Ubsan.M.loaded_segments (0x13dbc : word) = Some W_13cb8.
Proof. vm_refl. Qed.
Lemma D_13cb8 : decode_any W_13cb8 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cbc : bv 32 := 0x04b46463.
Lemma F_13cbc : fetch_word Ubsan.M.loaded_segments (0x13dc0 : word) = Some W_13cbc.
Proof. vm_refl. Qed.
Lemma D_13cbc : decode_any W_13cbc = Some (Branch BC_LTU 8 11 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cc0 : bv 32 := 0x00050493.
Lemma F_13cc0 : fetch_word Ubsan.M.loaded_segments (0x13dc4 : word) = Some W_13cc0.
Proof. vm_refl. Qed.
Lemma D_13cc0 : decode_any W_13cc0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cc4 : bv 32 := 0x00000517.
Lemma F_13cc4 : fetch_word Ubsan.M.loaded_segments (0x13dc8 : word) = Some W_13cc4.
Proof. vm_refl. Qed.
Lemma D_13cc4 : decode_any W_13cc4 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cc8 : bv 32 := 0x05850513.
Lemma F_13cc8 : fetch_word Ubsan.M.loaded_segments (0x13dcc : word) = Some W_13cc8.
Proof. vm_refl. Qed.
Lemma D_13cc8 : decode_any W_13cc8 = Some (OpImm ALU_ADD 10 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ccc : bv 32 := 0x170000ef.
Lemma F_13ccc : fetch_word Ubsan.M.loaded_segments (0x13dd0 : word) = Some W_13ccc.
Proof. vm_refl. Qed.
Lemma D_13ccc : decode_any W_13ccc = Some (Jal 1 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cd0 : bv 32 := 0x00048513.
Lemma F_13cd0 : fetch_word Ubsan.M.loaded_segments (0x13dd4 : word) = Some W_13cd0.
Proof. vm_refl. Qed.
Lemma D_13cd0 : decode_any W_13cd0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cd4 : bv 32 := 0x00040593.
Lemma F_13cd4 : fetch_word Ubsan.M.loaded_segments (0x13dd8 : word) = Some W_13cd4.
Proof. vm_refl. Qed.
Lemma D_13cd4 : decode_any W_13cd4 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cd8 : bv 32 := 0x2b9020ef.
Lemma F_13cd8 : fetch_word Ubsan.M.loaded_segments (0x13ddc : word) = Some W_13cd8.
Proof. vm_refl. Qed.
Lemma D_13cd8 : decode_any W_13cd8 = Some (Jal 1 10936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cdc : bv 32 := 0x00a13823.
Lemma F_13cdc : fetch_word Ubsan.M.loaded_segments (0x13de0 : word) = Some W_13cdc.
Proof. vm_refl. Qed.
Lemma D_13cdc : decode_any W_13cdc = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ce0 : bv 32 := 0x02050263.
Lemma F_13ce0 : fetch_word Ubsan.M.loaded_segments (0x13de4 : word) = Some W_13ce0.
Proof. vm_refl. Qed.
Lemma D_13ce0 : decode_any W_13ce0 = Some (Branch BC_EQ 10 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ce4 : bv 32 := 0x00100593.
Lemma F_13ce4 : fetch_word Ubsan.M.loaded_segments (0x13de8 : word) = Some W_13ce4.
Proof. vm_refl. Qed.
Lemma D_13ce4 : decode_any W_13ce4 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ce8 : bv 32 := 0x00100613.
Lemma F_13ce8 : fetch_word Ubsan.M.loaded_segments (0x13dec : word) = Some W_13ce8.
Proof. vm_refl. Qed.
Lemma D_13ce8 : decode_any W_13ce8 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cec : bv 32 := 0x795020ef.
Lemma F_13cec : fetch_word Ubsan.M.loaded_segments (0x13df0 : word) = Some W_13cec.
Proof. vm_refl. Qed.
Lemma D_13cec : decode_any W_13cec = Some (Jal 1 12180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cf0 : bv 32 := 0x00a13423.
Lemma F_13cf0 : fetch_word Ubsan.M.loaded_segments (0x13df4 : word) = Some W_13cf0.
Proof. vm_refl. Qed.
Lemma D_13cf0 : decode_any W_13cf0 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cf4 : bv 32 := 0x00810513.
Lemma F_13cf4 : fetch_word Ubsan.M.loaded_segments (0x13df8 : word) = Some W_13cf4.
Proof. vm_refl. Qed.
Lemma D_13cf4 : decode_any W_13cf4 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cf8 : bv 32 := 0x234030ef.
Lemma F_13cf8 : fetch_word Ubsan.M.loaded_segments (0x13dfc : word) = Some W_13cf8.
Proof. vm_refl. Qed.
Lemma D_13cf8 : decode_any W_13cf8 = Some (Jal 1 12852, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cfc : bv 32 := 0x01010513.
Lemma F_13cfc : fetch_word Ubsan.M.loaded_segments (0x13e00 : word) = Some W_13cfc.
Proof. vm_refl. Qed.
Lemma D_13cfc : decode_any W_13cfc = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d00 : bv 32 := 0x6f8010ef.
Lemma F_13d00 : fetch_word Ubsan.M.loaded_segments (0x13e04 : word) = Some W_13d00.
Proof. vm_refl. Qed.
Lemma D_13d00 : decode_any W_13d00 = Some (Jal 1 5880, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d04 : bv 32 := 0x00000513.
Lemma F_13d04 : fetch_word Ubsan.M.loaded_segments (0x13e08 : word) = Some W_13d04.
Proof. vm_refl. Qed.
Lemma D_13d04 : decode_any W_13d04 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d08 : bv 32 := 0x02813083.
Lemma F_13d08 : fetch_word Ubsan.M.loaded_segments (0x13e0c : word) = Some W_13d08.
Proof. vm_refl. Qed.
Lemma D_13d08 : decode_any W_13d08 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d0c : bv 32 := 0x02013403.
Lemma F_13d0c : fetch_word Ubsan.M.loaded_segments (0x13e10 : word) = Some W_13d0c.
Proof. vm_refl. Qed.
Lemma D_13d0c : decode_any W_13d0c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d10 : bv 32 := 0x01813483.
Lemma F_13d10 : fetch_word Ubsan.M.loaded_segments (0x13e14 : word) = Some W_13d10.
Proof. vm_refl. Qed.
Lemma D_13d10 : decode_any W_13d10 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d14 : bv 32 := 0x03010113.
Lemma F_13d14 : fetch_word Ubsan.M.loaded_segments (0x13e18 : word) = Some W_13d14.
Proof. vm_refl. Qed.
Lemma D_13d14 : decode_any W_13d14 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d18 : bv 32 := 0x00008067.
Lemma F_13d18 : fetch_word Ubsan.M.loaded_segments (0x13e1c : word) = Some W_13d18.
Proof. vm_refl. Qed.
Lemma D_13d18 : decode_any W_13d18 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d20 : bv 32 := 0xff010113.
Lemma F_13d20 : fetch_word Ubsan.M.loaded_segments (0x13e24 : word) = Some W_13d20.
Proof. vm_refl. Qed.
Lemma D_13d20 : decode_any W_13d20 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d24 : bv 32 := 0x00113423.
Lemma F_13d24 : fetch_word Ubsan.M.loaded_segments (0x13e28 : word) = Some W_13d24.
Proof. vm_refl. Qed.
Lemma D_13d24 : decode_any W_13d24 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d28 : bv 32 := 0x00813023.
Lemma F_13d28 : fetch_word Ubsan.M.loaded_segments (0x13e2c : word) = Some W_13d28.
Proof. vm_refl. Qed.
Lemma D_13d28 : decode_any W_13d28 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d2c : bv 32 := 0x00060413.
Lemma F_13d2c : fetch_word Ubsan.M.loaded_segments (0x13e30 : word) = Some W_13d2c.
Proof. vm_refl. Qed.
Lemma D_13d2c : decode_any W_13d2c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d30 : bv 32 := 0x00050613.
Lemma F_13d30 : fetch_word Ubsan.M.loaded_segments (0x13e34 : word) = Some W_13d30.
Proof. vm_refl. Qed.
Lemma D_13d30 : decode_any W_13d30 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d34 : bv 32 := 0xffffd517.
Lemma F_13d34 : fetch_word Ubsan.M.loaded_segments (0x13e38 : word) = Some W_13d34.
Proof. vm_refl. Qed.
Lemma D_13d34 : decode_any W_13d34 = Some (Auipc 10 1048573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d38 : bv 32 := 0xe8550513.
Lemma F_13d38 : fetch_word Ubsan.M.loaded_segments (0x13e3c : word) = Some W_13d38.
Proof. vm_refl. Qed.
Lemma D_13d38 : decode_any W_13d38 = Some (OpImm ALU_ADD 10 10 3717, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d3c : bv 32 := 0x018000ef.
Lemma F_13d3c : fetch_word Ubsan.M.loaded_segments (0x13e40 : word) = Some W_13d3c.
Proof. vm_refl. Qed.
Lemma D_13d3c : decode_any W_13d3c = Some (Jal 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d40 : bv 32 := 0x00040513.
Lemma F_13d40 : fetch_word Ubsan.M.loaded_segments (0x13e44 : word) = Some W_13d40.
Proof. vm_refl. Qed.
Lemma D_13d40 : decode_any W_13d40 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d44 : bv 32 := 0x00813083.
Lemma F_13d44 : fetch_word Ubsan.M.loaded_segments (0x13e48 : word) = Some W_13d44.
Proof. vm_refl. Qed.
Lemma D_13d44 : decode_any W_13d44 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d48 : bv 32 := 0x00013403.
Lemma F_13d48 : fetch_word Ubsan.M.loaded_segments (0x13e4c : word) = Some W_13d48.
Proof. vm_refl. Qed.
Lemma D_13d48 : decode_any W_13d48 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d4c : bv 32 := 0x01010113.
Lemma F_13d4c : fetch_word Ubsan.M.loaded_segments (0x13e50 : word) = Some W_13d4c.
Proof. vm_refl. Qed.
Lemma D_13d4c : decode_any W_13d4c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d50 : bv 32 := 0x00008067.
Lemma F_13d50 : fetch_word Ubsan.M.loaded_segments (0x13e54 : word) = Some W_13d50.
Proof. vm_refl. Qed.
Lemma D_13d50 : decode_any W_13d50 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13df0 : bv 32 := 0xff010113.
Lemma F_13df0 : fetch_word Ubsan.M.loaded_segments (0x13ef4 : word) = Some W_13df0.
Proof. vm_refl. Qed.
Lemma D_13df0 : decode_any W_13df0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13df4 : bv 32 := 0x00113423.
Lemma F_13df4 : fetch_word Ubsan.M.loaded_segments (0x13ef8 : word) = Some W_13df4.
Proof. vm_refl. Qed.
Lemma D_13df4 : decode_any W_13df4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13df8 : bv 32 := 0x00813023.
Lemma F_13df8 : fetch_word Ubsan.M.loaded_segments (0x13efc : word) = Some W_13df8.
Proof. vm_refl. Qed.
Lemma D_13df8 : decode_any W_13df8 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13dfc : bv 32 := 0x00060413.
Lemma F_13dfc : fetch_word Ubsan.M.loaded_segments (0x13f00 : word) = Some W_13dfc.
Proof. vm_refl. Qed.
Lemma D_13dfc : decode_any W_13dfc = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e00 : bv 32 := 0x00050613.
Lemma F_13e00 : fetch_word Ubsan.M.loaded_segments (0x13f04 : word) = Some W_13e00.
Proof. vm_refl. Qed.
Lemma D_13e00 : decode_any W_13e00 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e04 : bv 32 := 0xffffd517.
Lemma F_13e04 : fetch_word Ubsan.M.loaded_segments (0x13f08 : word) = Some W_13e04.
Proof. vm_refl. Qed.
Lemma D_13e04 : decode_any W_13e04 = Some (Auipc 10 1048573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e08 : bv 32 := 0xdb550513.
Lemma F_13e08 : fetch_word Ubsan.M.loaded_segments (0x13f0c : word) = Some W_13e08.
Proof. vm_refl. Qed.
Lemma D_13e08 : decode_any W_13e08 = Some (OpImm ALU_ADD 10 10 3509, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e0c : bv 32 := 0xf49ff0ef.
Lemma F_13e0c : fetch_word Ubsan.M.loaded_segments (0x13f10 : word) = Some W_13e0c.
Proof. vm_refl. Qed.
Lemma D_13e0c : decode_any W_13e0c = Some (Jal 1 2096968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e10 : bv 32 := 0x00040513.
Lemma F_13e10 : fetch_word Ubsan.M.loaded_segments (0x13f14 : word) = Some W_13e10.
Proof. vm_refl. Qed.
Lemma D_13e10 : decode_any W_13e10 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e14 : bv 32 := 0x00813083.
Lemma F_13e14 : fetch_word Ubsan.M.loaded_segments (0x13f18 : word) = Some W_13e14.
Proof. vm_refl. Qed.
Lemma D_13e14 : decode_any W_13e14 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e18 : bv 32 := 0x00013403.
Lemma F_13e18 : fetch_word Ubsan.M.loaded_segments (0x13f1c : word) = Some W_13e18.
Proof. vm_refl. Qed.
Lemma D_13e18 : decode_any W_13e18 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e1c : bv 32 := 0x01010113.
Lemma F_13e1c : fetch_word Ubsan.M.loaded_segments (0x13f20 : word) = Some W_13e1c.
Proof. vm_refl. Qed.
Lemma D_13e1c : decode_any W_13e1c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e20 : bv 32 := 0x00008067.
Lemma F_13e20 : fetch_word Ubsan.M.loaded_segments (0x13f24 : word) = Some W_13e20.
Proof. vm_refl. Qed.
Lemma D_13e20 : decode_any W_13e20 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e3c : bv 32 := 0x00051663.
Lemma F_13e3c : fetch_word Ubsan.M.loaded_segments (0x13f40 : word) = Some W_13e3c.
Proof. vm_refl. Qed.
Lemma D_13e3c : decode_any W_13e3c = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e48 : bv 32 := 0x0000e597.
Lemma F_13e48 : fetch_word Ubsan.M.loaded_segments (0x13f4c : word) = Some W_13e48.
Proof. vm_refl. Qed.
Lemma D_13e48 : decode_any W_13e48 = Some (Auipc 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e4c : bv 32 := 0x8ca5b623.
Lemma F_13e4c : fetch_word Ubsan.M.loaded_segments (0x13f50 : word) = Some W_13e4c.
Proof. vm_refl. Qed.
Lemma D_13e4c : decode_any W_13e4c = Some (Store SZ8 11 10 2252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13e50 : bv 32 := 0x00008067.
Lemma F_13e50 : fetch_word Ubsan.M.loaded_segments (0x13f54 : word) = Some W_13e50.
Proof. vm_refl. Qed.
Lemma D_13e50 : decode_any W_13e50 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f9c : bv 32 := 0xfe010113.
Lemma F_13f9c : fetch_word Ubsan.M.loaded_segments (0x140a0 : word) = Some W_13f9c.
Proof. vm_refl. Qed.
Lemma D_13f9c : decode_any W_13f9c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fa0 : bv 32 := 0x00113c23.
Lemma F_13fa0 : fetch_word Ubsan.M.loaded_segments (0x140a4 : word) = Some W_13fa0.
Proof. vm_refl. Qed.
Lemma D_13fa0 : decode_any W_13fa0 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fa4 : bv 32 := 0x00813823.
Lemma F_13fa4 : fetch_word Ubsan.M.loaded_segments (0x140a8 : word) = Some W_13fa4.
Proof. vm_refl. Qed.
Lemma D_13fa4 : decode_any W_13fa4 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fa8 : bv 32 := 0x00913423.
Lemma F_13fa8 : fetch_word Ubsan.M.loaded_segments (0x140ac : word) = Some W_13fa8.
Proof. vm_refl. Qed.
Lemma D_13fa8 : decode_any W_13fa8 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fac : bv 32 := 0x00050413.
Lemma F_13fac : fetch_word Ubsan.M.loaded_segments (0x140b0 : word) = Some W_13fac.
Proof. vm_refl. Qed.
Lemma D_13fac : decode_any W_13fac = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fb0 : bv 32 := 0xfff0c537.
Lemma F_13fb0 : fetch_word Ubsan.M.loaded_segments (0x140b4 : word) = Some W_13fb0.
Proof. vm_refl. Qed.
Lemma D_13fb0 : decode_any W_13fb0 = Some (Lui 10 1048332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fb4 : bv 32 := 0xdbf50593.
Lemma F_13fb4 : fetch_word Ubsan.M.loaded_segments (0x140b8 : word) = Some W_13fb4.
Proof. vm_refl. Qed.
Lemma D_13fb4 : decode_any W_13fb4 = Some (OpImm ALU_ADD 11 10 3519, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fb8 : bv 32 := 0x00b405bb.
Lemma F_13fb8 : fetch_word Ubsan.M.loaded_segments (0x140bc : word) = Some W_13fb8.
Proof. vm_refl. Qed.
Lemma D_13fb8 : decode_any W_13fb8 = Some (Op32 ALU_ADD 11 8 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fbc : bv 32 := 0xdc05051b.
Lemma F_13fbc : fetch_word Ubsan.M.loaded_segments (0x140c0 : word) = Some W_13fbc.
Proof. vm_refl. Qed.
Lemma D_13fbc : decode_any W_13fbc = Some (OpImm32 10 10 3520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fc0 : bv 32 := 0x00a5f463.
Lemma F_13fc0 : fetch_word Ubsan.M.loaded_segments (0x140c4 : word) = Some W_13fc0.
Proof. vm_refl. Qed.
Lemma D_13fc0 : decode_any W_13fc0 = Some (Branch BC_GEU 11 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fc8 : bv 32 := 0x00100513.
Lemma F_13fc8 : fetch_word Ubsan.M.loaded_segments (0x140cc : word) = Some W_13fc8.
Proof. vm_refl. Qed.
Lemma D_13fc8 : decode_any W_13fc8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fcc : bv 32 := 0x01000593.
Lemma F_13fcc : fetch_word Ubsan.M.loaded_segments (0x140d0 : word) = Some W_13fcc.
Proof. vm_refl. Qed.
Lemma D_13fcc : decode_any W_13fcc = Some (OpImm ALU_ADD 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fd0 : bv 32 := 0x249030ef.
Lemma F_13fd0 : fetch_word Ubsan.M.loaded_segments (0x140d4 : word) = Some W_13fd0.
Proof. vm_refl. Qed.
Lemma D_13fd0 : decode_any W_13fd0 = Some (Jal 1 14920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fd4 : bv 32 := 0x00050493.
Lemma F_13fd4 : fetch_word Ubsan.M.loaded_segments (0x140d8 : word) = Some W_13fd4.
Proof. vm_refl. Qed.
Lemma D_13fd4 : decode_any W_13fd4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fd8 : bv 32 := 0x00a13023.
Lemma F_13fd8 : fetch_word Ubsan.M.loaded_segments (0x140dc : word) = Some W_13fd8.
Proof. vm_refl. Qed.
Lemma D_13fd8 : decode_any W_13fd8 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fdc : bv 32 := 0x00800593.
Lemma F_13fdc : fetch_word Ubsan.M.loaded_segments (0x140e0 : word) = Some W_13fdc.
Proof. vm_refl. Qed.
Lemma D_13fdc : decode_any W_13fdc = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fe0 : bv 32 := 0x00040513.
Lemma F_13fe0 : fetch_word Ubsan.M.loaded_segments (0x140e4 : word) = Some W_13fe0.
Proof. vm_refl. Qed.
Lemma D_13fe0 : decode_any W_13fe0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fe4 : bv 32 := 0x235030ef.
Lemma F_13fe4 : fetch_word Ubsan.M.loaded_segments (0x140e8 : word) = Some W_13fe4.
Proof. vm_refl. Qed.
Lemma D_13fe4 : decode_any W_13fe4 = Some (Jal 1 14900, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fe8 : bv 32 := 0x06048c63.
Lemma F_13fe8 : fetch_word Ubsan.M.loaded_segments (0x140ec : word) = Some W_13fe8.
Proof. vm_refl. Qed.
Lemma D_13fe8 : decode_any W_13fe8 = Some (Branch BC_EQ 9 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13fec : bv 32 := 0x00050593.
Lemma F_13fec : fetch_word Ubsan.M.loaded_segments (0x140f0 : word) = Some W_13fec.
Proof. vm_refl. Qed.
Lemma D_13fec : decode_any W_13fec = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ff0 : bv 32 := 0x00048513.
Lemma F_13ff0 : fetch_word Ubsan.M.loaded_segments (0x140f4 : word) = Some W_13ff0.
Proof. vm_refl. Qed.
Lemma D_13ff0 : decode_any W_13ff0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ff4 : bv 32 := 0x0074f613.
Lemma F_13ff4 : fetch_word Ubsan.M.loaded_segments (0x140f8 : word) = Some W_13ff4.
Proof. vm_refl. Qed.
Lemma D_13ff4 : decode_any W_13ff4 = Some (OpImm ALU_AND 12 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ff8 : bv 32 := 0x06061463.
Lemma F_13ff8 : fetch_word Ubsan.M.loaded_segments (0x140fc : word) = Some W_13ff8.
Proof. vm_refl. Qed.
Lemma D_13ff8 : decode_any W_13ff8 = Some (Branch BC_NE 12 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ffc : bv 32 := 0x00b53423.
Lemma F_13ffc : fetch_word Ubsan.M.loaded_segments (0x14100 : word) = Some W_13ffc.
Proof. vm_refl. Qed.
Lemma D_13ffc : decode_any W_13ffc = Some (Store SZ8 10 11 8, 4%Z).
Proof. vm_refl. Qed.
