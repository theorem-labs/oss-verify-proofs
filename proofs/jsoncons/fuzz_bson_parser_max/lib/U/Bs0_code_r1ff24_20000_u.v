(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_33db0 : bv 32 := 0xfffdc197.
Lemma F_33db0 : fetch_word Ubsan.M.loaded_segments (0x34130 : word) = Some W_33db0.
Proof. vm_refl. Qed.
Lemma D_33db0 : decode_any W_33db0 = Some (Auipc 3 1048540, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33db4 : bv 32 := 0x6d018193.
Lemma F_33db4 : fetch_word Ubsan.M.loaded_segments (0x34134 : word) = Some W_33db4.
Proof. vm_refl. Qed.
Lemma D_33db4 : decode_any W_33db4 = Some (OpImm ALU_ADD 3 3 1744, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33db8 : bv 32 := 0x00010513.
Lemma F_33db8 : fetch_word Ubsan.M.loaded_segments (0x34138 : word) = Some W_33db8.
Proof. vm_refl. Qed.
Lemma D_33db8 : decode_any W_33db8 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33dbc : bv 32 := 0xfffcc597.
Lemma F_33dbc : fetch_word Ubsan.M.loaded_segments (0x3413c : word) = Some W_33dbc.
Proof. vm_refl. Qed.
Lemma D_33dbc : decode_any W_33dbc = Some (Auipc 11 1048524, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33dc0 : bv 32 := 0xec458593.
Lemma F_33dc0 : fetch_word Ubsan.M.loaded_segments (0x34140 : word) = Some W_33dc0.
Proof. vm_refl. Qed.
Lemma D_33dc0 : decode_any W_33dc0 = Some (OpImm ALU_ADD 11 11 3780, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33dc4 : bv 32 := 0xff017113.
Lemma F_33dc4 : fetch_word Ubsan.M.loaded_segments (0x34144 : word) = Some W_33dc4.
Proof. vm_refl. Qed.
Lemma D_33dc4 : decode_any W_33dc4 = Some (OpImm ALU_AND 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33dc8 : bv 32 := 0x0040006f.
Lemma F_33dc8 : fetch_word Ubsan.M.loaded_segments (0x34148 : word) = Some W_33dc8.
Proof. vm_refl. Qed.
Lemma D_33dc8 : decode_any W_33dc8 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33dcc : bv 32 := 0x00052583.
Lemma F_33dcc : fetch_word Ubsan.M.loaded_segments (0x3414c : word) = Some W_33dcc.
Proof. vm_refl. Qed.
Lemma D_33dcc : decode_any W_33dcc = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33dd0 : bv 32 := 0x00083617.
Lemma F_33dd0 : fetch_word Ubsan.M.loaded_segments (0x34150 : word) = Some W_33dd0.
Proof. vm_refl. Qed.
Lemma D_33dd0 : decode_any W_33dd0 = Some (Auipc 12 131, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33dd4 : bv 32 := 0x00083697.
Lemma F_33dd4 : fetch_word Ubsan.M.loaded_segments (0x34154 : word) = Some W_33dd4.
Proof. vm_refl. Qed.
Lemma D_33dd4 : decode_any W_33dd4 = Some (Auipc 13 131, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33dd8 : bv 32 := 0x00083717.
Lemma F_33dd8 : fetch_word Ubsan.M.loaded_segments (0x34158 : word) = Some W_33dd8.
Proof. vm_refl. Qed.
Lemma D_33dd8 : decode_any W_33dd8 = Some (Auipc 14 131, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ddc : bv 32 := 0xf1063783.
Lemma F_33ddc : fetch_word Ubsan.M.loaded_segments (0x3415c : word) = Some W_33ddc.
Proof. vm_refl. Qed.
Lemma D_33ddc : decode_any W_33ddc = Some (Load SZ8 true 15 12 3856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33de0 : bv 32 := 0xf146b683.
Lemma F_33de0 : fetch_word Ubsan.M.loaded_segments (0x34160 : word) = Some W_33de0.
Proof. vm_refl. Qed.
Lemma D_33de0 : decode_any W_33de0 = Some (Load SZ8 true 13 13 3860, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33de4 : bv 32 := 0xf1873703.
Lemma F_33de4 : fetch_word Ubsan.M.loaded_segments (0x34164 : word) = Some W_33de4.
Proof. vm_refl. Qed.
Lemma D_33de4 : decode_any W_33de4 = Some (Load SZ8 true 14 14 3864, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33de8 : bv 32 := 0x00850613.
Lemma F_33de8 : fetch_word Ubsan.M.loaded_segments (0x34168 : word) = Some W_33de8.
Proof. vm_refl. Qed.
Lemma D_33de8 : decode_any W_33de8 = Some (OpImm ALU_ADD 12 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33dec : bv 32 := 0x00078513.
Lemma F_33dec : fetch_word Ubsan.M.loaded_segments (0x3416c : word) = Some W_33dec.
Proof. vm_refl. Qed.
Lemma D_33dec : decode_any W_33dec = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33df0 : bv 32 := 0x00000793.
Lemma F_33df0 : fetch_word Ubsan.M.loaded_segments (0x34170 : word) = Some W_33df0.
Proof. vm_refl. Qed.
Lemma D_33df0 : decode_any W_33df0 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33df4 : bv 32 := 0x58c6606f.
Lemma F_33df4 : fetch_word Ubsan.M.loaded_segments (0x34174 : word) = Some W_33df4.
Proof. vm_refl. Qed.
Lemma D_33df4 : decode_any W_33df4 = Some (Jal 0 419212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33df8 : bv 32 := 0xff010113.
Lemma F_33df8 : fetch_word Ubsan.M.loaded_segments (0x34178 : word) = Some W_33df8.
Proof. vm_refl. Qed.
Lemma D_33df8 : decode_any W_33df8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33dfc : bv 32 := 0x00113423.
Lemma F_33dfc : fetch_word Ubsan.M.loaded_segments (0x3417c : word) = Some W_33dfc.
Proof. vm_refl. Qed.
Lemma D_33dfc : decode_any W_33dfc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e00 : bv 32 := 0x00813023.
Lemma F_33e00 : fetch_word Ubsan.M.loaded_segments (0x34180 : word) = Some W_33e00.
Proof. vm_refl. Qed.
Lemma D_33e00 : decode_any W_33e00 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e04 : bv 32 := 0x01010413.
Lemma F_33e04 : fetch_word Ubsan.M.loaded_segments (0x34184 : word) = Some W_33e04.
Proof. vm_refl. Qed.
Lemma D_33e04 : decode_any W_33e04 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e08 : bv 32 := 0x00084517.
Lemma F_33e08 : fetch_word Ubsan.M.loaded_segments (0x34188 : word) = Some W_33e08.
Proof. vm_refl. Qed.
Lemma D_33e08 : decode_any W_33e08 = Some (Auipc 10 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e0c : bv 32 := 0x37850513.
Lemma F_33e0c : fetch_word Ubsan.M.loaded_segments (0x3418c : word) = Some W_33e0c.
Proof. vm_refl. Qed.
Lemma D_33e0c : decode_any W_33e0c = Some (OpImm ALU_ADD 10 10 888, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e10 : bv 32 := 0x00054503.
Lemma F_33e10 : fetch_word Ubsan.M.loaded_segments (0x34190 : word) = Some W_33e10.
Proof. vm_refl. Qed.
Lemma D_33e10 : decode_any W_33e10 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e14 : bv 32 := 0x00157513.
Lemma F_33e14 : fetch_word Ubsan.M.loaded_segments (0x34194 : word) = Some W_33e14.
Proof. vm_refl. Qed.
Lemma D_33e14 : decode_any W_33e14 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e18 : bv 32 := 0x00050663.
Lemma F_33e18 : fetch_word Ubsan.M.loaded_segments (0x34198 : word) = Some W_33e18.
Proof. vm_refl. Qed.
Lemma D_33e18 : decode_any W_33e18 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e24 : bv 32 := 0x00084517.
Lemma F_33e24 : fetch_word Ubsan.M.loaded_segments (0x341a4 : word) = Some W_33e24.
Proof. vm_refl. Qed.
Lemma D_33e24 : decode_any W_33e24 = Some (Auipc 10 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e28 : bv 32 := 0x35c50593.
Lemma F_33e28 : fetch_word Ubsan.M.loaded_segments (0x341a8 : word) = Some W_33e28.
Proof. vm_refl. Qed.
Lemma D_33e28 : decode_any W_33e28 = Some (OpImm ALU_ADD 11 10 860, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e2c : bv 32 := 0x00100513.
Lemma F_33e2c : fetch_word Ubsan.M.loaded_segments (0x341ac : word) = Some W_33e2c.
Proof. vm_refl. Qed.
Lemma D_33e2c : decode_any W_33e2c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e30 : bv 32 := 0x00a58023.
Lemma F_33e30 : fetch_word Ubsan.M.loaded_segments (0x341b0 : word) = Some W_33e30.
Proof. vm_refl. Qed.
Lemma D_33e30 : decode_any W_33e30 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e34 : bv 32 := 0x00083517.
Lemma F_33e34 : fetch_word Ubsan.M.loaded_segments (0x341b4 : word) = Some W_33e34.
Proof. vm_refl. Qed.
Lemma D_33e34 : decode_any W_33e34 = Some (Auipc 10 131, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e38 : bv 32 := 0xec453503.
Lemma F_33e38 : fetch_word Ubsan.M.loaded_segments (0x341b8 : word) = Some W_33e38.
Proof. vm_refl. Qed.
Lemma D_33e38 : decode_any W_33e38 = Some (Load SZ8 true 10 10 3780, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e3c : bv 32 := 0x02050063.
Lemma F_33e3c : fetch_word Ubsan.M.loaded_segments (0x341bc : word) = Some W_33e3c.
Proof. vm_refl. Qed.
Lemma D_33e3c : decode_any W_33e3c = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e5c : bv 32 := 0x00813083.
Lemma F_33e5c : fetch_word Ubsan.M.loaded_segments (0x341dc : word) = Some W_33e5c.
Proof. vm_refl. Qed.
Lemma D_33e5c : decode_any W_33e5c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e60 : bv 32 := 0x00013403.
Lemma F_33e60 : fetch_word Ubsan.M.loaded_segments (0x341e0 : word) = Some W_33e60.
Proof. vm_refl. Qed.
Lemma D_33e60 : decode_any W_33e60 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e64 : bv 32 := 0x01010113.
Lemma F_33e64 : fetch_word Ubsan.M.loaded_segments (0x341e4 : word) = Some W_33e64.
Proof. vm_refl. Qed.
Lemma D_33e64 : decode_any W_33e64 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e68 : bv 32 := 0x00008067.
Lemma F_33e68 : fetch_word Ubsan.M.loaded_segments (0x341e8 : word) = Some W_33e68.
Proof. vm_refl. Qed.
Lemma D_33e68 : decode_any W_33e68 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e6c : bv 32 := 0xff010113.
Lemma F_33e6c : fetch_word Ubsan.M.loaded_segments (0x341ec : word) = Some W_33e6c.
Proof. vm_refl. Qed.
Lemma D_33e6c : decode_any W_33e6c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e70 : bv 32 := 0x00113423.
Lemma F_33e70 : fetch_word Ubsan.M.loaded_segments (0x341f0 : word) = Some W_33e70.
Proof. vm_refl. Qed.
Lemma D_33e70 : decode_any W_33e70 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e74 : bv 32 := 0x00813023.
Lemma F_33e74 : fetch_word Ubsan.M.loaded_segments (0x341f4 : word) = Some W_33e74.
Proof. vm_refl. Qed.
Lemma D_33e74 : decode_any W_33e74 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e78 : bv 32 := 0x01010413.
Lemma F_33e78 : fetch_word Ubsan.M.loaded_segments (0x341f8 : word) = Some W_33e78.
Proof. vm_refl. Qed.
Lemma D_33e78 : decode_any W_33e78 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e7c : bv 32 := 0x00084517.
Lemma F_33e7c : fetch_word Ubsan.M.loaded_segments (0x341fc : word) = Some W_33e7c.
Proof. vm_refl. Qed.
Lemma D_33e7c : decode_any W_33e7c = Some (Auipc 10 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e80 : bv 32 := 0x34c50513.
Lemma F_33e80 : fetch_word Ubsan.M.loaded_segments (0x34200 : word) = Some W_33e80.
Proof. vm_refl. Qed.
Lemma D_33e80 : decode_any W_33e80 = Some (OpImm ALU_ADD 10 10 844, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e84 : bv 32 := 0x00054503.
Lemma F_33e84 : fetch_word Ubsan.M.loaded_segments (0x34204 : word) = Some W_33e84.
Proof. vm_refl. Qed.
Lemma D_33e84 : decode_any W_33e84 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e88 : bv 32 := 0x00157513.
Lemma F_33e88 : fetch_word Ubsan.M.loaded_segments (0x34208 : word) = Some W_33e88.
Proof. vm_refl. Qed.
Lemma D_33e88 : decode_any W_33e88 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.
