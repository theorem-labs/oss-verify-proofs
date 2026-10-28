(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_bb084 : bv 32 := 0x00757593.
Lemma F_bb084 : fetch_word Ubsan.M.loaded_segments (0xbeaac : word) = Some W_bb084.
Proof. vm_refl. Qed.
Lemma D_bb084 : decode_any W_bb084 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb088 : bv 32 := 0x00050613.
Lemma F_bb088 : fetch_word Ubsan.M.loaded_segments (0xbeab0 : word) = Some W_bb088.
Proof. vm_refl. Qed.
Lemma D_bb088 : decode_any W_bb088 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb08c : bv 32 := 0x02058a63.
Lemma F_bb08c : fetch_word Ubsan.M.loaded_segments (0xbeab4 : word) = Some W_bb08c.
Proof. vm_refl. Qed.
Lemma D_bb08c : decode_any W_bb08c = Some (Branch BC_EQ 11 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb090 : bv 32 := 0x00054583.
Lemma F_bb090 : fetch_word Ubsan.M.loaded_segments (0xbeab8 : word) = Some W_bb090.
Proof. vm_refl. Qed.
Lemma D_bb090 : decode_any W_bb090 = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb094 : bv 32 := 0x06058c63.
Lemma F_bb094 : fetch_word Ubsan.M.loaded_segments (0xbeabc : word) = Some W_bb094.
Proof. vm_refl. Qed.
Lemma D_bb094 : decode_any W_bb094 = Some (Branch BC_EQ 11 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb098 : bv 32 := 0x00150613.
Lemma F_bb098 : fetch_word Ubsan.M.loaded_segments (0xbeac0 : word) = Some W_bb098.
Proof. vm_refl. Qed.
Lemma D_bb098 : decode_any W_bb098 = Some (OpImm ALU_ADD 12 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb09c : bv 32 := 0x00050593.
Lemma F_bb09c : fetch_word Ubsan.M.loaded_segments (0xbeac4 : word) = Some W_bb09c.
Proof. vm_refl. Qed.
Lemma D_bb09c : decode_any W_bb09c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb0a0 : bv 32 := 0x00158693.
Lemma F_bb0a0 : fetch_word Ubsan.M.loaded_segments (0xbeac8 : word) = Some W_bb0a0.
Proof. vm_refl. Qed.
Lemma D_bb0a0 : decode_any W_bb0a0 = Some (OpImm ALU_ADD 13 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb0a4 : bv 32 := 0x0076f693.
Lemma F_bb0a4 : fetch_word Ubsan.M.loaded_segments (0xbeacc : word) = Some W_bb0a4.
Proof. vm_refl. Qed.
Lemma D_bb0a4 : decode_any W_bb0a4 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb0a8 : bv 32 := 0x00068c63.
Lemma F_bb0a8 : fetch_word Ubsan.M.loaded_segments (0xbead0 : word) = Some W_bb0a8.
Proof. vm_refl. Qed.
Lemma D_bb0a8 : decode_any W_bb0a8 = Some (Branch BC_EQ 13 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb0ac : bv 32 := 0x00064683.
Lemma F_bb0ac : fetch_word Ubsan.M.loaded_segments (0xbead4 : word) = Some W_bb0ac.
Proof. vm_refl. Qed.
Lemma D_bb0ac : decode_any W_bb0ac = Some (Load SZ1 false 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb0b0 : bv 32 := 0x00160613.
Lemma F_bb0b0 : fetch_word Ubsan.M.loaded_segments (0xbead8 : word) = Some W_bb0b0.
Proof. vm_refl. Qed.
Lemma D_bb0b0 : decode_any W_bb0b0 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb0b4 : bv 32 := 0x00158593.
Lemma F_bb0b4 : fetch_word Ubsan.M.loaded_segments (0xbeadc : word) = Some W_bb0b4.
Proof. vm_refl. Qed.
Lemma D_bb0b4 : decode_any W_bb0b4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb0b8 : bv 32 := 0xfe0694e3.
Lemma F_bb0b8 : fetch_word Ubsan.M.loaded_segments (0xbeae0 : word) = Some W_bb0b8.
Proof. vm_refl. Qed.
Lemma D_bb0b8 : decode_any W_bb0b8 = Some (Branch BC_NE 13 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb0bc : bv 32 := 0x0480006f.
Lemma F_bb0bc : fetch_word Ubsan.M.loaded_segments (0xbeae4 : word) = Some W_bb0bc.
Proof. vm_refl. Qed.
Lemma D_bb0bc : decode_any W_bb0bc = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb0c0 : bv 32 := 0xfff55597.
Lemma F_bb0c0 : fetch_word Ubsan.M.loaded_segments (0xbeae8 : word) = Some W_bb0c0.
Proof. vm_refl. Qed.
Lemma D_bb0c0 : decode_any W_bb0c0 = Some (Auipc 11 1048405, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb0c4 : bv 32 := 0xfff55717.
Lemma F_bb0c4 : fetch_word Ubsan.M.loaded_segments (0xbeaec : word) = Some W_bb0c4.
Proof. vm_refl. Qed.
Lemma D_bb0c4 : decode_any W_bb0c4 = Some (Auipc 14 1048405, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb0c8 : bv 32 := 0x0185b683.
Lemma F_bb0c8 : fetch_word Ubsan.M.loaded_segments (0xbeaf0 : word) = Some W_bb0c8.
Proof. vm_refl. Qed.
Lemma D_bb0c8 : decode_any W_bb0c8 = Some (Load SZ8 true 13 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb0cc : bv 32 := 0x00473703.
Lemma F_bb0cc : fetch_word Ubsan.M.loaded_segments (0xbeaf4 : word) = Some W_bb0cc.
Proof. vm_refl. Qed.
Lemma D_bb0cc : decode_any W_bb0cc = Some (Load SZ8 true 14 14 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb0d0 : bv 32 := 0xff760593.
Lemma F_bb0d0 : fetch_word Ubsan.M.loaded_segments (0xbeaf8 : word) = Some W_bb0d0.
Proof. vm_refl. Qed.
Lemma D_bb0d0 : decode_any W_bb0d0 = Some (OpImm ALU_ADD 11 12 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb0d4 : bv 32 := 0xff860613.
Lemma F_bb0d4 : fetch_word Ubsan.M.loaded_segments (0xbeafc : word) = Some W_bb0d4.
Proof. vm_refl. Qed.
Lemma D_bb0d4 : decode_any W_bb0d4 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb0d8 : bv 32 := 0x00863783.
Lemma F_bb0d8 : fetch_word Ubsan.M.loaded_segments (0xbeb00 : word) = Some W_bb0d8.
Proof. vm_refl. Qed.
Lemma D_bb0d8 : decode_any W_bb0d8 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb0dc : bv 32 := 0x00860613.
Lemma F_bb0dc : fetch_word Ubsan.M.loaded_segments (0xbeb04 : word) = Some W_bb0dc.
Proof. vm_refl. Qed.
Lemma D_bb0dc : decode_any W_bb0dc = Some (OpImm ALU_ADD 12 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb0e0 : bv 32 := 0x40f68833.
Lemma F_bb0e0 : fetch_word Ubsan.M.loaded_segments (0xbeb08 : word) = Some W_bb0e0.
Proof. vm_refl. Qed.
Lemma D_bb0e0 : decode_any W_bb0e0 = Some (Op ALU_SUB 16 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb0e4 : bv 32 := 0x00f867b3.
Lemma F_bb0e4 : fetch_word Ubsan.M.loaded_segments (0xbeb0c : word) = Some W_bb0e4.
Proof. vm_refl. Qed.
Lemma D_bb0e4 : decode_any W_bb0e4 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb0e8 : bv 32 := 0x00e7f7b3.
Lemma F_bb0e8 : fetch_word Ubsan.M.loaded_segments (0xbeb10 : word) = Some W_bb0e8.
Proof. vm_refl. Qed.
Lemma D_bb0e8 : decode_any W_bb0e8 = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb0ec : bv 32 := 0x00858593.
Lemma F_bb0ec : fetch_word Ubsan.M.loaded_segments (0xbeb14 : word) = Some W_bb0ec.
Proof. vm_refl. Qed.
Lemma D_bb0ec : decode_any W_bb0ec = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb0f0 : bv 32 := 0xfee784e3.
Lemma F_bb0f0 : fetch_word Ubsan.M.loaded_segments (0xbeb18 : word) = Some W_bb0f0.
Proof. vm_refl. Qed.
Lemma D_bb0f0 : decode_any W_bb0f0 = Some (Branch BC_EQ 15 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb0f4 : bv 32 := 0x00064683.
Lemma F_bb0f4 : fetch_word Ubsan.M.loaded_segments (0xbeb1c : word) = Some W_bb0f4.
Proof. vm_refl. Qed.
Lemma D_bb0f4 : decode_any W_bb0f4 = Some (Load SZ1 false 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb0f8 : bv 32 := 0x00160613.
Lemma F_bb0f8 : fetch_word Ubsan.M.loaded_segments (0xbeb20 : word) = Some W_bb0f8.
Proof. vm_refl. Qed.
Lemma D_bb0f8 : decode_any W_bb0f8 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb0fc : bv 32 := 0x00158593.
Lemma F_bb0fc : fetch_word Ubsan.M.loaded_segments (0xbeb24 : word) = Some W_bb0fc.
Proof. vm_refl. Qed.
Lemma D_bb0fc : decode_any W_bb0fc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb100 : bv 32 := 0xfe069ae3.
Lemma F_bb100 : fetch_word Ubsan.M.loaded_segments (0xbeb28 : word) = Some W_bb100.
Proof. vm_refl. Qed.
Lemma D_bb100 : decode_any W_bb100 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb104 : bv 32 := 0x40a58533.
Lemma F_bb104 : fetch_word Ubsan.M.loaded_segments (0xbeb2c : word) = Some W_bb104.
Proof. vm_refl. Qed.
Lemma D_bb104 : decode_any W_bb104 = Some (Op ALU_SUB 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb108 : bv 32 := 0x00008067.
Lemma F_bb108 : fetch_word Ubsan.M.loaded_segments (0xbeb30 : word) = Some W_bb108.
Proof. vm_refl. Qed.
Lemma D_bb108 : decode_any W_bb108 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb10c : bv 32 := 0x40a50533.
Lemma F_bb10c : fetch_word Ubsan.M.loaded_segments (0xbeb34 : word) = Some W_bb10c.
Proof. vm_refl. Qed.
Lemma D_bb10c : decode_any W_bb10c = Some (Op ALU_SUB 10 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb110 : bv 32 := 0x00008067.
Lemma F_bb110 : fetch_word Ubsan.M.loaded_segments (0xbeb38 : word) = Some W_bb110.
Proof. vm_refl. Qed.
Lemma D_bb110 : decode_any W_bb110 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb114 : bv 32 := 0xfe010113.
Lemma F_bb114 : fetch_word Ubsan.M.loaded_segments (0xbeb3c : word) = Some W_bb114.
Proof. vm_refl. Qed.
Lemma D_bb114 : decode_any W_bb114 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb118 : bv 32 := 0x00113c23.
Lemma F_bb118 : fetch_word Ubsan.M.loaded_segments (0xbeb40 : word) = Some W_bb118.
Proof. vm_refl. Qed.
Lemma D_bb118 : decode_any W_bb118 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb11c : bv 32 := 0x00813823.
Lemma F_bb11c : fetch_word Ubsan.M.loaded_segments (0xbeb44 : word) = Some W_bb11c.
Proof. vm_refl. Qed.
Lemma D_bb11c : decode_any W_bb11c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb120 : bv 32 := 0x00913423.
Lemma F_bb120 : fetch_word Ubsan.M.loaded_segments (0xbeb48 : word) = Some W_bb120.
Proof. vm_refl. Qed.
Lemma D_bb120 : decode_any W_bb120 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb124 : bv 32 := 0x00058413.
Lemma F_bb124 : fetch_word Ubsan.M.loaded_segments (0xbeb4c : word) = Some W_bb124.
Proof. vm_refl. Qed.
Lemma D_bb124 : decode_any W_bb124 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb128 : bv 32 := 0x00050493.
Lemma F_bb128 : fetch_word Ubsan.M.loaded_segments (0xbeb50 : word) = Some W_bb128.
Proof. vm_refl. Qed.
Lemma D_bb128 : decode_any W_bb128 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb12c : bv 32 := 0x00000593.
Lemma F_bb12c : fetch_word Ubsan.M.loaded_segments (0xbeb54 : word) = Some W_bb12c.
Proof. vm_refl. Qed.
Lemma D_bb12c : decode_any W_bb12c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb130 : bv 32 := 0x00040613.
Lemma F_bb130 : fetch_word Ubsan.M.loaded_segments (0xbeb58 : word) = Some W_bb130.
Proof. vm_refl. Qed.
Lemma D_bb130 : decode_any W_bb130 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb134 : bv 32 := 0xbf0ff0ef.
Lemma F_bb134 : fetch_word Ubsan.M.loaded_segments (0xbeb5c : word) = Some W_bb134.
Proof. vm_refl. Qed.
Lemma D_bb134 : decode_any W_bb134 = Some (Jal 1 2094064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb138 : bv 32 := 0x00050463.
Lemma F_bb138 : fetch_word Ubsan.M.loaded_segments (0xbeb60 : word) = Some W_bb138.
Proof. vm_refl. Qed.
Lemma D_bb138 : decode_any W_bb138 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb13c : bv 32 := 0x40950433.
Lemma F_bb13c : fetch_word Ubsan.M.loaded_segments (0xbeb64 : word) = Some W_bb13c.
Proof. vm_refl. Qed.
Lemma D_bb13c : decode_any W_bb13c = Some (Op ALU_SUB 8 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb140 : bv 32 := 0x00040513.
Lemma F_bb140 : fetch_word Ubsan.M.loaded_segments (0xbeb68 : word) = Some W_bb140.
Proof. vm_refl. Qed.
Lemma D_bb140 : decode_any W_bb140 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb144 : bv 32 := 0x01813083.
Lemma F_bb144 : fetch_word Ubsan.M.loaded_segments (0xbeb6c : word) = Some W_bb144.
Proof. vm_refl. Qed.
Lemma D_bb144 : decode_any W_bb144 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb148 : bv 32 := 0x01013403.
Lemma F_bb148 : fetch_word Ubsan.M.loaded_segments (0xbeb70 : word) = Some W_bb148.
Proof. vm_refl. Qed.
Lemma D_bb148 : decode_any W_bb148 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb14c : bv 32 := 0x00813483.
Lemma F_bb14c : fetch_word Ubsan.M.loaded_segments (0xbeb74 : word) = Some W_bb14c.
Proof. vm_refl. Qed.
Lemma D_bb14c : decode_any W_bb14c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb150 : bv 32 := 0x02010113.
Lemma F_bb150 : fetch_word Ubsan.M.loaded_segments (0xbeb78 : word) = Some W_bb150.
Proof. vm_refl. Qed.
Lemma D_bb150 : decode_any W_bb150 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb154 : bv 32 := 0x00008067.
Lemma F_bb154 : fetch_word Ubsan.M.loaded_segments (0xbeb7c : word) = Some W_bb154.
Proof. vm_refl. Qed.
Lemma D_bb154 : decode_any W_bb154 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb2b0 : bv 32 := 0x0003e597.
Lemma F_bb2b0 : fetch_word Ubsan.M.loaded_segments (0xbecd8 : word) = Some W_bb2b0.
Proof. vm_refl. Qed.
Lemma D_bb2b0 : decode_any W_bb2b0 = Some (Auipc 11 62, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb2b4 : bv 32 := 0x5cb58683.
Lemma F_bb2b4 : fetch_word Ubsan.M.loaded_segments (0xbecdc : word) = Some W_bb2b4.
Proof. vm_refl. Qed.
Lemma D_bb2b4 : decode_any W_bb2b4 = Some (Load SZ1 true 13 11 1483, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb2b8 : bv 32 := 0x1e068863.
Lemma F_bb2b8 : fetch_word Ubsan.M.loaded_segments (0xbece0 : word) = Some W_bb2b8.
Proof. vm_refl. Qed.
Lemma D_bb2b8 : decode_any W_bb2b8 = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb4a8 : bv 32 := 0x00008067.
Lemma F_bb4a8 : fetch_word Ubsan.M.loaded_segments (0xbeed0 : word) = Some W_bb4a8.
Proof. vm_refl. Qed.
Lemma D_bb4a8 : decode_any W_bb4a8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb538 : bv 32 := 0x00052583.
Lemma F_bb538 : fetch_word Ubsan.M.loaded_segments (0xbef60 : word) = Some W_bb538.
Proof. vm_refl. Qed.
Lemma D_bb538 : decode_any W_bb538 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb53c : bv 32 := 0x0005c463.
Lemma F_bb53c : fetch_word Ubsan.M.loaded_segments (0xbef64 : word) = Some W_bb53c.
Proof. vm_refl. Qed.
Lemma D_bb53c : decode_any W_bb53c = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bb540 : bv 32 := 0x00008067.
Lemma F_bb540 : fetch_word Ubsan.M.loaded_segments (0xbef68 : word) = Some W_bb540.
Proof. vm_refl. Qed.
Lemma D_bb540 : decode_any W_bb540 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

