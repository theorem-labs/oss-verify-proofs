(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.H Require GcFlushU9.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_63114 : bv 32 := 0xff010113.
Lemma F_63114 : fetch_word Ubsan.M.loaded_segments (0x6316c : word) = Some W_63114.
Proof. vm_refl. Qed.
Lemma D_63114 : decode_any W_63114 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63118 : bv 32 := 0x00113423.
Lemma F_63118 : fetch_word Ubsan.M.loaded_segments (0x63170 : word) = Some W_63118.
Proof. vm_refl. Qed.
Lemma D_63118 : decode_any W_63118 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6311c : bv 32 := 0x00813023.
Lemma F_6311c : fetch_word Ubsan.M.loaded_segments (0x63174 : word) = Some W_6311c.
Proof. vm_refl. Qed.
Lemma D_6311c : decode_any W_6311c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63120 : bv 32 := 0x098000ef.
Lemma F_63120 : fetch_word Ubsan.M.loaded_segments (0x63178 : word) = Some W_63120.
Proof. vm_refl. Qed.
Lemma D_63120 : decode_any W_63120 = Some (Jal 1 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63124 : bv 32 := 0x04050263.
Lemma F_63124 : fetch_word Ubsan.M.loaded_segments (0x6317c : word) = Some W_63124.
Proof. vm_refl. Qed.
Lemma D_63124 : decode_any W_63124 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63128 : bv 32 := 0x00757593.
Lemma F_63128 : fetch_word Ubsan.M.loaded_segments (0x63180 : word) = Some W_63128.
Proof. vm_refl. Qed.
Lemma D_63128 : decode_any W_63128 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6312c : bv 32 := 0x08059463.
Lemma F_6312c : fetch_word Ubsan.M.loaded_segments (0x63184 : word) = Some W_6312c.
Proof. vm_refl. Qed.
Lemma D_6312c : decode_any W_6312c = Some (Branch BC_NE 11 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63130 : bv 32 := 0x01056583.
Lemma F_63130 : fetch_word Ubsan.M.loaded_segments (0x63188 : word) = Some W_63130.
Proof. vm_refl. Qed.
Lemma D_63130 : decode_any W_63130 = Some (Load SZ4 false 11 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63134 : bv 32 := 0x00456603.
Lemma F_63134 : fetch_word Ubsan.M.loaded_segments (0x6318c : word) = Some W_63134.
Proof. vm_refl. Qed.
Lemma D_63134 : decode_any W_63134 = Some (Load SZ4 false 12 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63138 : bv 32 := 0x00259593.
Lemma F_63138 : fetch_word Ubsan.M.loaded_segments (0x63190 : word) = Some W_63138.
Proof. vm_refl. Qed.
Lemma D_63138 : decode_any W_63138 = Some (ShiftImm ALU_SLL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6313c : bv 32 := 0x02c596b3.
Lemma F_6313c : fetch_word Ubsan.M.loaded_segments (0x63194 : word) = Some W_6313c.
Proof. vm_refl. Qed.
Lemma D_6313c : decode_any W_6313c = Some (Mul M_MULH 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63140 : bv 32 := 0x02c58633.
Lemma F_63140 : fetch_word Ubsan.M.loaded_segments (0x63198 : word) = Some W_63140.
Proof. vm_refl. Qed.
Lemma D_63140 : decode_any W_63140 = Some (Mul M_MUL 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63144 : bv 32 := 0x43f65593.
Lemma F_63144 : fetch_word Ubsan.M.loaded_segments (0x6319c : word) = Some W_63144.
Proof. vm_refl. Qed.
Lemma D_63144 : decode_any W_63144 = Some (ShiftImm ALU_SRA 11 12 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63148 : bv 32 := 0x06b69663.
Lemma F_63148 : fetch_word Ubsan.M.loaded_segments (0x631a0 : word) = Some W_63148.
Proof. vm_refl. Qed.
Lemma D_63148 : decode_any W_63148 = Some (Branch BC_NE 13 11 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6314c : bv 32 := 0x03853583.
Lemma F_6314c : fetch_word Ubsan.M.loaded_segments (0x631a4 : word) = Some W_6314c.
Proof. vm_refl. Qed.
Lemma D_6314c : decode_any W_6314c = Some (Load SZ8 true 11 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63150 : bv 32 := 0x00050413.
Lemma F_63150 : fetch_word Ubsan.M.loaded_segments (0x631a8 : word) = Some W_63150.
Proof. vm_refl. Qed.
Lemma D_63150 : decode_any W_63150 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63154 : bv 32 := 0x00058513.
Lemma F_63154 : fetch_word Ubsan.M.loaded_segments (0x631ac : word) = Some W_63154.
Proof. vm_refl. Qed.
Lemma D_63154 : decode_any W_63154 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63158 : bv 32 := 0x00000593.
Lemma F_63158 : fetch_word Ubsan.M.loaded_segments (0x631b0 : word) = Some W_63158.
Proof. vm_refl. Qed.
Lemma D_63158 : decode_any W_63158 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6315c : bv 32 := 0x6558d0ef.
Lemma F_6315c : fetch_word Ubsan.M.loaded_segments (0x631b4 : word) = Some W_6315c.
Proof. vm_refl. Qed.
Lemma D_6315c : decode_any W_6315c = Some (Jal 1 581204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63160 : bv 32 := 0x00040513.
Lemma F_63160 : fetch_word Ubsan.M.loaded_segments (0x631b8 : word) = Some W_63160.
Proof. vm_refl. Qed.
Lemma D_63160 : decode_any W_63160 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63164 : bv 32 := 0x0400006f.
Lemma F_63164 : fetch_word Ubsan.M.loaded_segments (0x631bc : word) = Some W_63164.
Proof. vm_refl. Qed.
Lemma D_63164 : decode_any W_63164 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63168 : bv 32 := 0x00096517.
Lemma F_63168 : fetch_word Ubsan.M.loaded_segments (0x631c0 : word) = Some W_63168.
Proof. vm_refl. Qed.
Lemma D_63168 : decode_any W_63168 = Some (Auipc 10 150, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6316c : bv 32 := 0xf6053503.
Lemma F_6316c : fetch_word Ubsan.M.loaded_segments (0x631c4 : word) = Some W_6316c.
Proof. vm_refl. Qed.
Lemma D_6316c : decode_any W_6316c = Some (Load SZ8 true 10 10 3936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63170 : bv 32 := 0x00052503.
Lemma F_63170 : fetch_word Ubsan.M.loaded_segments (0x631c8 : word) = Some W_63170.
Proof. vm_refl. Qed.
Lemma D_63170 : decode_any W_63170 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63174 : bv 32 := 0x00500593.
Lemma F_63174 : fetch_word Ubsan.M.loaded_segments (0x631cc : word) = Some W_63174.
Proof. vm_refl. Qed.
Lemma D_63174 : decode_any W_63174 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63178 : bv 32 := 0x02a5c463.
Lemma F_63178 : fetch_word Ubsan.M.loaded_segments (0x631d0 : word) = Some W_63178.
Proof. vm_refl. Qed.
Lemma D_63178 : decode_any W_63178 = Some (Branch BC_LT 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6317c : bv 32 := 0xfffaf517.
Lemma F_6317c : fetch_word Ubsan.M.loaded_segments (0x631d4 : word) = Some W_6317c.
Proof. vm_refl. Qed.
Lemma D_6317c : decode_any W_6317c = Some (Auipc 10 1048495, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63180 : bv 32 := 0xfffb1597.
Lemma F_63180 : fetch_word Ubsan.M.loaded_segments (0x631d8 : word) = Some W_63180.
Proof. vm_refl. Qed.
Lemma D_63180 : decode_any W_63180 = Some (Auipc 11 1048497, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63184 : bv 32 := 0xe8e50513.
Lemma F_63184 : fetch_word Ubsan.M.loaded_segments (0x631dc : word) = Some W_63184.
Proof. vm_refl. Qed.
Lemma D_63184 : decode_any W_63184 = Some (OpImm ALU_ADD 10 10 3726, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63188 : bv 32 := 0x37158593.
Lemma F_63188 : fetch_word Ubsan.M.loaded_segments (0x631e0 : word) = Some W_63188.
Proof. vm_refl. Qed.
Lemma D_63188 : decode_any W_63188 = Some (OpImm ALU_ADD 11 11 881, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6318c : bv 32 := 0x00000613.
Lemma F_6318c : fetch_word Ubsan.M.loaded_segments (0x631e4 : word) = Some W_6318c.
Proof. vm_refl. Qed.
Lemma D_6318c : decode_any W_6318c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63190 : bv 32 := 0x00813083.
Lemma F_63190 : fetch_word Ubsan.M.loaded_segments (0x631e8 : word) = Some W_63190.
Proof. vm_refl. Qed.
Lemma D_63190 : decode_any W_63190 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63194 : bv 32 := 0x00013403.
Lemma F_63194 : fetch_word Ubsan.M.loaded_segments (0x631ec : word) = Some W_63194.
Proof. vm_refl. Qed.
Lemma D_63194 : decode_any W_63194 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63198 : bv 32 := 0x01010113.
Lemma F_63198 : fetch_word Ubsan.M.loaded_segments (0x631f0 : word) = Some W_63198.
Proof. vm_refl. Qed.
Lemma D_63198 : decode_any W_63198 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6319c : bv 32 := 0x8a0fa06f.
Lemma F_6319c : fetch_word Ubsan.M.loaded_segments (0x631f4 : word) = Some W_6319c.
Proof. vm_refl. Qed.
Lemma D_6319c : decode_any W_6319c = Some (Jal 0 2072736, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631a4 : bv 32 := 0x00813083.
Lemma F_631a4 : fetch_word Ubsan.M.loaded_segments (0x631fc : word) = Some W_631a4.
Proof. vm_refl. Qed.
Lemma D_631a4 : decode_any W_631a4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631a8 : bv 32 := 0x00013403.
Lemma F_631a8 : fetch_word Ubsan.M.loaded_segments (0x63200 : word) = Some W_631a8.
Proof. vm_refl. Qed.
Lemma D_631a8 : decode_any W_631a8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631ac : bv 32 := 0x01010113.
Lemma F_631ac : fetch_word Ubsan.M.loaded_segments (0x63204 : word) = Some W_631ac.
Proof. vm_refl. Qed.
Lemma D_631ac : decode_any W_631ac = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631b0 : bv 32 := 0x00008067.
Lemma F_631b0 : fetch_word Ubsan.M.loaded_segments (0x63208 : word) = Some W_631b0.
Proof. vm_refl. Qed.
Lemma D_631b0 : decode_any W_631b0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631b8 : bv 32 := 0xfe010113.
Lemma F_631b8 : fetch_word Ubsan.M.loaded_segments (0x63210 : word) = Some W_631b8.
Proof. vm_refl. Qed.
Lemma D_631b8 : decode_any W_631b8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631bc : bv 32 := 0x00113c23.
Lemma F_631bc : fetch_word Ubsan.M.loaded_segments (0x63214 : word) = Some W_631bc.
Proof. vm_refl. Qed.
Lemma D_631bc : decode_any W_631bc = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631c0 : bv 32 := 0x00813823.
Lemma F_631c0 : fetch_word Ubsan.M.loaded_segments (0x63218 : word) = Some W_631c0.
Proof. vm_refl. Qed.
Lemma D_631c0 : decode_any W_631c0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631c4 : bv 32 := 0x00913423.
Lemma F_631c4 : fetch_word Ubsan.M.loaded_segments (0x6321c : word) = Some W_631c4.
Proof. vm_refl. Qed.
Lemma D_631c4 : decode_any W_631c4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631c8 : bv 32 := 0x00058493.
Lemma F_631c8 : fetch_word Ubsan.M.loaded_segments (0x63220 : word) = Some W_631c8.
Proof. vm_refl. Qed.
Lemma D_631c8 : decode_any W_631c8 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631cc : bv 32 := 0x134000ef.
Lemma F_631cc : fetch_word Ubsan.M.loaded_segments (0x63224 : word) = Some W_631cc.
Proof. vm_refl. Qed.
Lemma D_631cc : decode_any W_631cc = Some (Jal 1 308, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631d0 : bv 32 := 0x04050863.
Lemma F_631d0 : fetch_word Ubsan.M.loaded_segments (0x63228 : word) = Some W_631d0.
Proof. vm_refl. Qed.
Lemma D_631d0 : decode_any W_631d0 = Some (Branch BC_EQ 10 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631d4 : bv 32 := 0x00050413.
Lemma F_631d4 : fetch_word Ubsan.M.loaded_segments (0x6322c : word) = Some W_631d4.
Proof. vm_refl. Qed.
Lemma D_631d4 : decode_any W_631d4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631d8 : bv 32 := 0x00757513.
Lemma F_631d8 : fetch_word Ubsan.M.loaded_segments (0x63230 : word) = Some W_631d8.
Proof. vm_refl. Qed.
Lemma D_631d8 : decode_any W_631d8 = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631dc : bv 32 := 0x12051063.
Lemma F_631dc : fetch_word Ubsan.M.loaded_segments (0x63234 : word) = Some W_631dc.
Proof. vm_refl. Qed.
Lemma D_631dc : decode_any W_631dc = Some (Branch BC_NE 10 0 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631e0 : bv 32 := 0x01042503.
Lemma F_631e0 : fetch_word Ubsan.M.loaded_segments (0x63238 : word) = Some W_631e0.
Proof. vm_refl. Qed.
Lemma D_631e0 : decode_any W_631e0 = Some (Load SZ4 true 10 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631e4 : bv 32 := 0x00251513.
Lemma F_631e4 : fetch_word Ubsan.M.loaded_segments (0x6323c : word) = Some W_631e4.
Proof. vm_refl. Qed.
Lemma D_631e4 : decode_any W_631e4 = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631e8 : bv 32 := 0x029515b3.
Lemma F_631e8 : fetch_word Ubsan.M.loaded_segments (0x63240 : word) = Some W_631e8.
Proof. vm_refl. Qed.
Lemma D_631e8 : decode_any W_631e8 = Some (Mul M_MULH 11 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631ec : bv 32 := 0x02950533.
Lemma F_631ec : fetch_word Ubsan.M.loaded_segments (0x63244 : word) = Some W_631ec.
Proof. vm_refl. Qed.
Lemma D_631ec : decode_any W_631ec = Some (Mul M_MUL 10 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631f0 : bv 32 := 0x43f55613.
Lemma F_631f0 : fetch_word Ubsan.M.loaded_segments (0x63248 : word) = Some W_631f0.
Proof. vm_refl. Qed.
Lemma D_631f0 : decode_any W_631f0 = Some (ShiftImm ALU_SRA 12 10 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631f4 : bv 32 := 0x10c59463.
Lemma F_631f4 : fetch_word Ubsan.M.loaded_segments (0x6324c : word) = Some W_631f4.
Proof. vm_refl. Qed.
Lemma D_631f4 : decode_any W_631f4 = Some (Branch BC_NE 11 12 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631f8 : bv 32 := 0x00097597.
Lemma F_631f8 : fetch_word Ubsan.M.loaded_segments (0x63250 : word) = Some W_631f8.
Proof. vm_refl. Qed.
Lemma D_631f8 : decode_any W_631f8 = Some (Auipc 11 151, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_631fc : bv 32 := 0x0c858493.
Lemma F_631fc : fetch_word Ubsan.M.loaded_segments (0x63254 : word) = Some W_631fc.
Proof. vm_refl. Qed.
Lemma D_631fc : decode_any W_631fc = Some (OpImm ALU_ADD 9 11 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63200 : bv 32 := 0x0004b583.
Lemma F_63200 : fetch_word Ubsan.M.loaded_segments (0x63258 : word) = Some W_63200.
Proof. vm_refl. Qed.
Lemma D_63200 : decode_any W_63200 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63204 : bv 32 := 0x000580e7.
Lemma F_63204 : fetch_word Ubsan.M.loaded_segments (0x6325c : word) = Some W_63204.
Proof. vm_refl. Qed.
Lemma D_63204 : decode_any W_63204 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63208 : bv 32 := 0x04050a63.
Lemma F_63208 : fetch_word Ubsan.M.loaded_segments (0x63260 : word) = Some W_63208.
Proof. vm_refl. Qed.
Lemma D_63208 : decode_any W_63208 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6320c : bv 32 := 0x02a43c23.
Lemma F_6320c : fetch_word Ubsan.M.loaded_segments (0x63264 : word) = Some W_6320c.
Proof. vm_refl. Qed.
Lemma D_6320c : decode_any W_6320c = Some (Store SZ8 8 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63210 : bv 32 := 0x00040513.
Lemma F_63210 : fetch_word Ubsan.M.loaded_segments (0x63268 : word) = Some W_63210.
Proof. vm_refl. Qed.
Lemma D_63210 : decode_any W_63210 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63214 : bv 32 := 0x00000593.
Lemma F_63214 : fetch_word Ubsan.M.loaded_segments (0x6326c : word) = Some W_63214.
Proof. vm_refl. Qed.
Lemma D_63214 : decode_any W_63214 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63218 : bv 32 := 0x384020ef.
Lemma F_63218 : fetch_word Ubsan.M.loaded_segments (0x63270 : word) = Some W_63218.
Proof. vm_refl. Qed.
Lemma D_63218 : decode_any W_63218 = Some (Jal 1 9092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6321c : bv 32 := 0x0c80006f.
Lemma F_6321c : fetch_word Ubsan.M.loaded_segments (0x63274 : word) = Some W_6321c.
Proof. vm_refl. Qed.
Lemma D_6321c : decode_any W_6321c = Some (Jal 0 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63220 : bv 32 := 0x00096517.
Lemma F_63220 : fetch_word Ubsan.M.loaded_segments (0x63278 : word) = Some W_63220.
Proof. vm_refl. Qed.
Lemma D_63220 : decode_any W_63220 = Some (Auipc 10 150, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63224 : bv 32 := 0xea853503.
Lemma F_63224 : fetch_word Ubsan.M.loaded_segments (0x6327c : word) = Some W_63224.
Proof. vm_refl. Qed.
Lemma D_63224 : decode_any W_63224 = Some (Load SZ8 true 10 10 3752, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63228 : bv 32 := 0x00052503.
Lemma F_63228 : fetch_word Ubsan.M.loaded_segments (0x63280 : word) = Some W_63228.
Proof. vm_refl. Qed.
Lemma D_63228 : decode_any W_63228 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6322c : bv 32 := 0x00500593.
Lemma F_6322c : fetch_word Ubsan.M.loaded_segments (0x63284 : word) = Some W_6322c.
Proof. vm_refl. Qed.
Lemma D_6322c : decode_any W_6322c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63230 : bv 32 := 0x0aa5c863.
Lemma F_63230 : fetch_word Ubsan.M.loaded_segments (0x63288 : word) = Some W_63230.
Proof. vm_refl. Qed.
Lemma D_63230 : decode_any W_63230 = Some (Branch BC_LT 11 10 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63234 : bv 32 := 0xfffaf517.
Lemma F_63234 : fetch_word Ubsan.M.loaded_segments (0x6328c : word) = Some W_63234.
Proof. vm_refl. Qed.
Lemma D_63234 : decode_any W_63234 = Some (Auipc 10 1048495, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63238 : bv 32 := 0xfffb0597.
Lemma F_63238 : fetch_word Ubsan.M.loaded_segments (0x63290 : word) = Some W_63238.
Proof. vm_refl. Qed.
Lemma D_63238 : decode_any W_63238 = Some (Auipc 11 1048496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6323c : bv 32 := 0xdd650513.
Lemma F_6323c : fetch_word Ubsan.M.loaded_segments (0x63294 : word) = Some W_6323c.
Proof. vm_refl. Qed.
Lemma D_6323c : decode_any W_6323c = Some (OpImm ALU_ADD 10 10 3542, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63240 : bv 32 := 0xf9958593.
Lemma F_63240 : fetch_word Ubsan.M.loaded_segments (0x63298 : word) = Some W_63240.
Proof. vm_refl. Qed.
Lemma D_63240 : decode_any W_63240 = Some (OpImm ALU_ADD 11 11 3993, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63244 : bv 32 := 0x00000613.
Lemma F_63244 : fetch_word Ubsan.M.loaded_segments (0x6329c : word) = Some W_63244.
Proof. vm_refl. Qed.
Lemma D_63244 : decode_any W_63244 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63248 : bv 32 := 0x01813083.
Lemma F_63248 : fetch_word Ubsan.M.loaded_segments (0x632a0 : word) = Some W_63248.
Proof. vm_refl. Qed.
Lemma D_63248 : decode_any W_63248 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6324c : bv 32 := 0x01013403.
Lemma F_6324c : fetch_word Ubsan.M.loaded_segments (0x632a4 : word) = Some W_6324c.
Proof. vm_refl. Qed.
Lemma D_6324c : decode_any W_6324c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63250 : bv 32 := 0x00813483.
Lemma F_63250 : fetch_word Ubsan.M.loaded_segments (0x632a8 : word) = Some W_63250.
Proof. vm_refl. Qed.
Lemma D_63250 : decode_any W_63250 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63254 : bv 32 := 0x02010113.
Lemma F_63254 : fetch_word Ubsan.M.loaded_segments (0x632ac : word) = Some W_63254.
Proof. vm_refl. Qed.
Lemma D_63254 : decode_any W_63254 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63258 : bv 32 := 0xfe5f906f.
Lemma F_63258 : fetch_word Ubsan.M.loaded_segments (0x632b0 : word) = Some W_63258.
Proof. vm_refl. Qed.
Lemma D_63258 : decode_any W_63258 = Some (Jal 0 2072548, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6325c : bv 32 := 0x01440513.
Lemma F_6325c : fetch_word Ubsan.M.loaded_segments (0x632b4 : word) = Some W_6325c.
Proof. vm_refl. Qed.
Lemma D_6325c : decode_any W_6325c = Some (OpImm ALU_ADD 10 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63260 : bv 32 := 0xfff00593.
Lemma F_63260 : fetch_word Ubsan.M.loaded_segments (0x632b8 : word) = Some W_63260.
Proof. vm_refl. Qed.
Lemma D_63260 : decode_any W_63260 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63264 : bv 32 := 0x06b5252f.
Lemma F_63264 : fetch_word Ubsan.M.loaded_segments (0x632bc : word) = Some W_63264.
Proof. vm_refl. Qed.
Lemma D_63264 : decode_any W_63264 = Some (Amo AMO_ADD AW true true 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63268 : bv 32 := 0x00100593.
Lemma F_63268 : fetch_word Ubsan.M.loaded_segments (0x632c0 : word) = Some W_63268.
Proof. vm_refl. Qed.
Lemma D_63268 : decode_any W_63268 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6326c : bv 32 := 0x04b51063.
Lemma F_6326c : fetch_word Ubsan.M.loaded_segments (0x632c4 : word) = Some W_6326c.
Proof. vm_refl. Qed.
Lemma D_6326c : decode_any W_6326c = Some (Branch BC_NE 10 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63270 : bv 32 := 0x03843503.
Lemma F_63270 : fetch_word Ubsan.M.loaded_segments (0x632c8 : word) = Some W_63270.
Proof. vm_refl. Qed.
Lemma D_63270 : decode_any W_63270 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63274 : bv 32 := 0x00050663.
Lemma F_63274 : fetch_word Ubsan.M.loaded_segments (0x632cc : word) = Some W_63274.
Proof. vm_refl. Qed.
Lemma D_63274 : decode_any W_63274 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63280 : bv 32 := 0x02843503.
Lemma F_63280 : fetch_word Ubsan.M.loaded_segments (0x632d8 : word) = Some W_63280.
Proof. vm_refl. Qed.
Lemma D_63280 : decode_any W_63280 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63284 : bv 32 := 0x00050463.
Lemma F_63284 : fetch_word Ubsan.M.loaded_segments (0x632dc : word) = Some W_63284.
Proof. vm_refl. Qed.
Lemma D_63284 : decode_any W_63284 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6328c : bv 32 := 0x03043503.
Lemma F_6328c : fetch_word Ubsan.M.loaded_segments (0x632e4 : word) = Some W_6328c.
Proof. vm_refl. Qed.
Lemma D_6328c : decode_any W_6328c = Some (Load SZ8 true 10 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63290 : bv 32 := 0x00a13023.
Lemma F_63290 : fetch_word Ubsan.M.loaded_segments (0x632e8 : word) = Some W_63290.
Proof. vm_refl. Qed.
Lemma D_63290 : decode_any W_63290 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63294 : bv 32 := 0x00050863.
Lemma F_63294 : fetch_word Ubsan.M.loaded_segments (0x632ec : word) = Some W_63294.
Proof. vm_refl. Qed.
Lemma D_63294 : decode_any W_63294 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_632a4 : bv 32 := 0x00040513.
Lemma F_632a4 : fetch_word Ubsan.M.loaded_segments (0x632fc : word) = Some W_632a4.
Proof. vm_refl. Qed.
Lemma D_632a4 : decode_any W_632a4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_632a8 : bv 32 := 0x2b87f0ef.
Lemma F_632a8 : fetch_word Ubsan.M.loaded_segments (0x63300 : word) = Some W_632a8.
Proof. vm_refl. Qed.
Lemma D_632a8 : decode_any W_632a8 = Some (Jal 1 520888, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_632ac : bv 32 := 0x00096517.
Lemma F_632ac : fetch_word Ubsan.M.loaded_segments (0x63304 : word) = Some W_632ac.
Proof. vm_refl. Qed.
Lemma D_632ac : decode_any W_632ac = Some (Auipc 10 150, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_632b0 : bv 32 := 0xe1c53503.
Lemma F_632b0 : fetch_word Ubsan.M.loaded_segments (0x63308 : word) = Some W_632b0.
Proof. vm_refl. Qed.
Lemma D_632b0 : decode_any W_632b0 = Some (Load SZ8 true 10 10 3612, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_632b4 : bv 32 := 0x00052503.
Lemma F_632b4 : fetch_word Ubsan.M.loaded_segments (0x6330c : word) = Some W_632b4.
Proof. vm_refl. Qed.
Lemma D_632b4 : decode_any W_632b4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_632b8 : bv 32 := 0x00500593.
Lemma F_632b8 : fetch_word Ubsan.M.loaded_segments (0x63310 : word) = Some W_632b8.
Proof. vm_refl. Qed.
Lemma D_632b8 : decode_any W_632b8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_632bc : bv 32 := 0x02a5c263.
Lemma F_632bc : fetch_word Ubsan.M.loaded_segments (0x63314 : word) = Some W_632bc.
Proof. vm_refl. Qed.
Lemma D_632bc : decode_any W_632bc = Some (Branch BC_LT 11 10 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_632c0 : bv 32 := 0xfffb6517.
Lemma F_632c0 : fetch_word Ubsan.M.loaded_segments (0x63318 : word) = Some W_632c0.
Proof. vm_refl. Qed.
Lemma D_632c0 : decode_any W_632c0 = Some (Auipc 10 1048502, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_632c4 : bv 32 := 0xfffb0597.
Lemma F_632c4 : fetch_word Ubsan.M.loaded_segments (0x6331c : word) = Some W_632c4.
Proof. vm_refl. Qed.
Lemma D_632c4 : decode_any W_632c4 = Some (Auipc 11 1048496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_632c8 : bv 32 := 0x67f50513.
Lemma F_632c8 : fetch_word Ubsan.M.loaded_segments (0x63320 : word) = Some W_632c8.
Proof. vm_refl. Qed.
Lemma D_632c8 : decode_any W_632c8 = Some (OpImm ALU_ADD 10 10 1663, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_632cc : bv 32 := 0xf0d58593.
Lemma F_632cc : fetch_word Ubsan.M.loaded_segments (0x63324 : word) = Some W_632cc.
Proof. vm_refl. Qed.
Lemma D_632cc : decode_any W_632cc = Some (OpImm ALU_ADD 11 11 3853, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_632d0 : bv 32 := 0x00000613.
Lemma F_632d0 : fetch_word Ubsan.M.loaded_segments (0x63328 : word) = Some W_632d0.
Proof. vm_refl. Qed.
Lemma D_632d0 : decode_any W_632d0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_632d4 : bv 32 := 0xf69f90ef.
Lemma F_632d4 : fetch_word Ubsan.M.loaded_segments (0x6332c : word) = Some W_632d4.
Proof. vm_refl. Qed.
Lemma D_632d4 : decode_any W_632d4 = Some (Jal 1 2072424, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_632d8 : bv 32 := 0x00050413.
Lemma F_632d8 : fetch_word Ubsan.M.loaded_segments (0x63330 : word) = Some W_632d8.
Proof. vm_refl. Qed.
Lemma D_632d8 : decode_any W_632d8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_632dc : bv 32 := 0x0080006f.
Lemma F_632dc : fetch_word Ubsan.M.loaded_segments (0x63334 : word) = Some W_632dc.
Proof. vm_refl. Qed.
Lemma D_632dc : decode_any W_632dc = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_632e4 : bv 32 := 0x00040513.
Lemma F_632e4 : fetch_word Ubsan.M.loaded_segments (0x6333c : word) = Some W_632e4.
Proof. vm_refl. Qed.
Lemma D_632e4 : decode_any W_632e4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_632e8 : bv 32 := 0x01813083.
Lemma F_632e8 : fetch_word Ubsan.M.loaded_segments (0x63340 : word) = Some W_632e8.
Proof. vm_refl. Qed.
Lemma D_632e8 : decode_any W_632e8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_632ec : bv 32 := 0x01013403.
Lemma F_632ec : fetch_word Ubsan.M.loaded_segments (0x63344 : word) = Some W_632ec.
Proof. vm_refl. Qed.
Lemma D_632ec : decode_any W_632ec = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_632f0 : bv 32 := 0x00813483.
Lemma F_632f0 : fetch_word Ubsan.M.loaded_segments (0x63348 : word) = Some W_632f0.
Proof. vm_refl. Qed.
Lemma D_632f0 : decode_any W_632f0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_632f4 : bv 32 := 0x02010113.
Lemma F_632f4 : fetch_word Ubsan.M.loaded_segments (0x6334c : word) = Some W_632f4.
Proof. vm_refl. Qed.
Lemma D_632f4 : decode_any W_632f4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_632f8 : bv 32 := 0x00008067.
Lemma F_632f8 : fetch_word Ubsan.M.loaded_segments (0x63350 : word) = Some W_632f8.
Proof. vm_refl. Qed.
Lemma D_632f8 : decode_any W_632f8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63820 : bv 32 := 0xfe010113.
Lemma F_63820 : fetch_word Ubsan.M.loaded_segments (0x63878 : word) = Some W_63820.
Proof. vm_refl. Qed.
Lemma D_63820 : decode_any W_63820 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63824 : bv 32 := 0x00113c23.
Lemma F_63824 : fetch_word Ubsan.M.loaded_segments (0x6387c : word) = Some W_63824.
Proof. vm_refl. Qed.
Lemma D_63824 : decode_any W_63824 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63828 : bv 32 := 0x00813823.
Lemma F_63828 : fetch_word Ubsan.M.loaded_segments (0x63880 : word) = Some W_63828.
Proof. vm_refl. Qed.
Lemma D_63828 : decode_any W_63828 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6382c : bv 32 := 0x00913423.
Lemma F_6382c : fetch_word Ubsan.M.loaded_segments (0x63884 : word) = Some W_6382c.
Proof. vm_refl. Qed.
Lemma D_6382c : decode_any W_6382c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63830 : bv 32 := 0x01213023.
Lemma F_63830 : fetch_word Ubsan.M.loaded_segments (0x63888 : word) = Some W_63830.
Proof. vm_refl. Qed.
Lemma D_63830 : decode_any W_63830 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63834 : bv 32 := 0x04050263.
Lemma F_63834 : fetch_word Ubsan.M.loaded_segments (0x6388c : word) = Some W_63834.
Proof. vm_refl. Qed.
Lemma D_63834 : decode_any W_63834 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63838 : bv 32 := 0x00050493.
Lemma F_63838 : fetch_word Ubsan.M.loaded_segments (0x63890 : word) = Some W_63838.
Proof. vm_refl. Qed.
Lemma D_63838 : decode_any W_63838 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6383c : bv 32 := 0x00757513.
Lemma F_6383c : fetch_word Ubsan.M.loaded_segments (0x63894 : word) = Some W_6383c.
Proof. vm_refl. Qed.
Lemma D_6383c : decode_any W_6383c = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63840 : bv 32 := 0x12051c63.
Lemma F_63840 : fetch_word Ubsan.M.loaded_segments (0x63898 : word) = Some W_63840.
Proof. vm_refl. Qed.
Lemma D_63840 : decode_any W_63840 = Some (Branch BC_NE 10 0 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63844 : bv 32 := 0x0004a503.
Lemma F_63844 : fetch_word Ubsan.M.loaded_segments (0x6389c : word) = Some W_63844.
Proof. vm_refl. Qed.
Lemma D_63844 : decode_any W_63844 = Some (Load SZ4 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63848 : bv 32 := 0x0044a583.
Lemma F_63848 : fetch_word Ubsan.M.loaded_segments (0x638a0 : word) = Some W_63848.
Proof. vm_refl. Qed.
Lemma D_63848 : decode_any W_63848 = Some (Load SZ4 true 11 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6384c : bv 32 := 0x0084a603.
Lemma F_6384c : fetch_word Ubsan.M.loaded_segments (0x638a4 : word) = Some W_6384c.
Proof. vm_refl. Qed.
Lemma D_6384c : decode_any W_6384c = Some (Load SZ4 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63850 : bv 32 := 0x969ff0ef.
Lemma F_63850 : fetch_word Ubsan.M.loaded_segments (0x638a8 : word) = Some W_63850.
Proof. vm_refl. Qed.
Lemma D_63850 : decode_any W_63850 = Some (Jal 1 2095464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63854 : bv 32 := 0x04050663.
Lemma F_63854 : fetch_word Ubsan.M.loaded_segments (0x638ac : word) = Some W_63854.
Proof. vm_refl. Qed.
Lemma D_63854 : decode_any W_63854 = Some (Branch BC_EQ 10 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63858 : bv 32 := 0x00050413.
Lemma F_63858 : fetch_word Ubsan.M.loaded_segments (0x638b0 : word) = Some W_63858.
Proof. vm_refl. Qed.
Lemma D_63858 : decode_any W_63858 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6385c : bv 32 := 0x08a48663.
Lemma F_6385c : fetch_word Ubsan.M.loaded_segments (0x638b4 : word) = Some W_6385c.
Proof. vm_refl. Qed.
Lemma D_6385c : decode_any W_6385c = Some (Branch BC_EQ 9 10 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63860 : bv 32 := 0x00c4a503.
Lemma F_63860 : fetch_word Ubsan.M.loaded_segments (0x638b8 : word) = Some W_63860.
Proof. vm_refl. Qed.
Lemma D_63860 : decode_any W_63860 = Some (Load SZ4 true 10 9 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63864 : bv 32 := 0x00747913.
Lemma F_63864 : fetch_word Ubsan.M.loaded_segments (0x638bc : word) = Some W_63864.
Proof. vm_refl. Qed.
Lemma D_63864 : decode_any W_63864 = Some (OpImm ALU_AND 18 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63868 : bv 32 := 0x08a05863.
Lemma F_63868 : fetch_word Ubsan.M.loaded_segments (0x638c0 : word) = Some W_63868.
Proof. vm_refl. Qed.
Lemma D_63868 : decode_any W_63868 = Some (Branch BC_GE 0 10 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6386c : bv 32 := 0x10091663.
Lemma F_6386c : fetch_word Ubsan.M.loaded_segments (0x638c4 : word) = Some W_6386c.
Proof. vm_refl. Qed.
Lemma D_6386c : decode_any W_6386c = Some (Branch BC_NE 18 0 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63870 : bv 32 := 0x00a42623.
Lemma F_63870 : fetch_word Ubsan.M.loaded_segments (0x638c8 : word) = Some W_63870.
Proof. vm_refl. Qed.
Lemma D_63870 : decode_any W_63870 = Some (Store SZ4 8 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63874 : bv 32 := 0x0b00006f.
Lemma F_63874 : fetch_word Ubsan.M.loaded_segments (0x638cc : word) = Some W_63874.
Proof. vm_refl. Qed.
Lemma D_63874 : decode_any W_63874 = Some (Jal 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_638a0 : bv 32 := 0x00096517.
Lemma F_638a0 : fetch_word Ubsan.M.loaded_segments (0x638f8 : word) = Some W_638a0.
Proof. vm_refl. Qed.
Lemma D_638a0 : decode_any W_638a0 = Some (Auipc 10 150, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_638a4 : bv 32 := 0x82853503.
Lemma F_638a4 : fetch_word Ubsan.M.loaded_segments (0x638fc : word) = Some W_638a4.
Proof. vm_refl. Qed.
Lemma D_638a4 : decode_any W_638a4 = Some (Load SZ8 true 10 10 2088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_638a8 : bv 32 := 0x00052503.
Lemma F_638a8 : fetch_word Ubsan.M.loaded_segments (0x63900 : word) = Some W_638a8.
Proof. vm_refl. Qed.
Lemma D_638a8 : decode_any W_638a8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_638ac : bv 32 := 0x00500593.
Lemma F_638ac : fetch_word Ubsan.M.loaded_segments (0x63904 : word) = Some W_638ac.
Proof. vm_refl. Qed.
Lemma D_638ac : decode_any W_638ac = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_638b0 : bv 32 := 0x02a5c863.
Lemma F_638b0 : fetch_word Ubsan.M.loaded_segments (0x63908 : word) = Some W_638b0.
Proof. vm_refl. Qed.
Lemma D_638b0 : decode_any W_638b0 = Some (Branch BC_LT 11 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_638b4 : bv 32 := 0xfffae517.
Lemma F_638b4 : fetch_word Ubsan.M.loaded_segments (0x6390c : word) = Some W_638b4.
Proof. vm_refl. Qed.
Lemma D_638b4 : decode_any W_638b4 = Some (Auipc 10 1048494, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_638b8 : bv 32 := 0xfffb6597.
Lemma F_638b8 : fetch_word Ubsan.M.loaded_segments (0x63910 : word) = Some W_638b8.
Proof. vm_refl. Qed.
Lemma D_638b8 : decode_any W_638b8 = Some (Auipc 11 1048502, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_638bc : bv 32 := 0x75650513.
Lemma F_638bc : fetch_word Ubsan.M.loaded_segments (0x63914 : word) = Some W_638bc.
Proof. vm_refl. Qed.
Lemma D_638bc : decode_any W_638bc = Some (OpImm ALU_ADD 10 10 1878, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_638c0 : bv 32 := 0x0a458593.
Lemma F_638c0 : fetch_word Ubsan.M.loaded_segments (0x63918 : word) = Some W_638c0.
Proof. vm_refl. Qed.
Lemma D_638c0 : decode_any W_638c0 = Some (OpImm ALU_ADD 11 11 164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_638c4 : bv 32 := 0x00000613.
Lemma F_638c4 : fetch_word Ubsan.M.loaded_segments (0x6391c : word) = Some W_638c4.
Proof. vm_refl. Qed.
Lemma D_638c4 : decode_any W_638c4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_638c8 : bv 32 := 0x01813083.
Lemma F_638c8 : fetch_word Ubsan.M.loaded_segments (0x63920 : word) = Some W_638c8.
Proof. vm_refl. Qed.
Lemma D_638c8 : decode_any W_638c8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_638cc : bv 32 := 0x01013403.
Lemma F_638cc : fetch_word Ubsan.M.loaded_segments (0x63924 : word) = Some W_638cc.
Proof. vm_refl. Qed.
Lemma D_638cc : decode_any W_638cc = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_638d0 : bv 32 := 0x00813483.
Lemma F_638d0 : fetch_word Ubsan.M.loaded_segments (0x63928 : word) = Some W_638d0.
Proof. vm_refl. Qed.
Lemma D_638d0 : decode_any W_638d0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_638d4 : bv 32 := 0x00013903.
Lemma F_638d4 : fetch_word Ubsan.M.loaded_segments (0x6392c : word) = Some W_638d4.
Proof. vm_refl. Qed.
Lemma D_638d4 : decode_any W_638d4 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_638d8 : bv 32 := 0x02010113.
Lemma F_638d8 : fetch_word Ubsan.M.loaded_segments (0x63930 : word) = Some W_638d8.
Proof. vm_refl. Qed.
Lemma D_638d8 : decode_any W_638d8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_638dc : bv 32 := 0x961f906f.
Lemma F_638dc : fetch_word Ubsan.M.loaded_segments (0x63934 : word) = Some W_638dc.
Proof. vm_refl. Qed.
Lemma D_638dc : decode_any W_638dc = Some (Jal 0 2070880, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63924 : bv 32 := 0x04091a63.
Lemma F_63924 : fetch_word Ubsan.M.loaded_segments (0x6397c : word) = Some W_63924.
Proof. vm_refl. Qed.
Lemma D_63924 : decode_any W_63924 = Some (Branch BC_NE 18 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63928 : bv 32 := 0x0184b503.
Lemma F_63928 : fetch_word Ubsan.M.loaded_segments (0x63980 : word) = Some W_63928.
Proof. vm_refl. Qed.
Lemma D_63928 : decode_any W_63928 = Some (Load SZ8 true 10 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6392c : bv 32 := 0x00a43c23.
Lemma F_6392c : fetch_word Ubsan.M.loaded_segments (0x63984 : word) = Some W_6392c.
Proof. vm_refl. Qed.
Lemma D_6392c : decode_any W_6392c = Some (Store SZ8 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63930 : bv 32 := 0x00040513.
Lemma F_63930 : fetch_word Ubsan.M.loaded_segments (0x63988 : word) = Some W_63930.
Proof. vm_refl. Qed.
Lemma D_63930 : decode_any W_63930 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63934 : bv 32 := 0x00048593.
Lemma F_63934 : fetch_word Ubsan.M.loaded_segments (0x6398c : word) = Some W_63934.
Proof. vm_refl. Qed.
Lemma D_63934 : decode_any W_63934 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63938 : bv 32 := 0x190000ef.
Lemma F_63938 : fetch_word Ubsan.M.loaded_segments (0x63990 : word) = Some W_63938.
Proof. vm_refl. Qed.
Lemma D_63938 : decode_any W_63938 = Some (Jal 1 400, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6393c : bv 32 := 0x0284b583.
Lemma F_6393c : fetch_word Ubsan.M.loaded_segments (0x63994 : word) = Some W_6393c.
Proof. vm_refl. Qed.
Lemma D_6393c : decode_any W_6393c = Some (Load SZ8 true 11 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63940 : bv 32 := 0x02840513.
Lemma F_63940 : fetch_word Ubsan.M.loaded_segments (0x63998 : word) = Some W_63940.
Proof. vm_refl. Qed.
Lemma D_63940 : decode_any W_63940 = Some (OpImm ALU_ADD 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63944 : bv 32 := 0xf6df90ef.
Lemma F_63944 : fetch_word Ubsan.M.loaded_segments (0x6399c : word) = Some W_63944.
Proof. vm_refl. Qed.
Lemma D_63944 : decode_any W_63944 = Some (Jal 1 2072428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63948 : bv 32 := 0x0204a503.
Lemma F_63948 : fetch_word Ubsan.M.loaded_segments (0x639a0 : word) = Some W_63948.
Proof. vm_refl. Qed.
Lemma D_63948 : decode_any W_63948 = Some (Load SZ4 true 10 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6394c : bv 32 := 0x02a42023.
Lemma F_6394c : fetch_word Ubsan.M.loaded_segments (0x639a4 : word) = Some W_6394c.
Proof. vm_refl. Qed.
Lemma D_6394c : decode_any W_6394c = Some (Store SZ4 8 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63950 : bv 32 := 0x00040513.
Lemma F_63950 : fetch_word Ubsan.M.loaded_segments (0x639a8 : word) = Some W_63950.
Proof. vm_refl. Qed.
Lemma D_63950 : decode_any W_63950 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63954 : bv 32 := 0x00000593.
Lemma F_63954 : fetch_word Ubsan.M.loaded_segments (0x639ac : word) = Some W_63954.
Proof. vm_refl. Qed.
Lemma D_63954 : decode_any W_63954 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63958 : bv 32 := 0x445010ef.
Lemma F_63958 : fetch_word Ubsan.M.loaded_segments (0x639b0 : word) = Some W_63958.
Proof. vm_refl. Qed.
Lemma D_63958 : decode_any W_63958 = Some (Jal 1 7236, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6395c : bv 32 := 0x00040513.
Lemma F_6395c : fetch_word Ubsan.M.loaded_segments (0x639b4 : word) = Some W_6395c.
Proof. vm_refl. Qed.
Lemma D_6395c : decode_any W_6395c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63960 : bv 32 := 0x01813083.
Lemma F_63960 : fetch_word Ubsan.M.loaded_segments (0x639b8 : word) = Some W_63960.
Proof. vm_refl. Qed.
Lemma D_63960 : decode_any W_63960 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63964 : bv 32 := 0x01013403.
Lemma F_63964 : fetch_word Ubsan.M.loaded_segments (0x639bc : word) = Some W_63964.
Proof. vm_refl. Qed.
Lemma D_63964 : decode_any W_63964 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63968 : bv 32 := 0x00813483.
Lemma F_63968 : fetch_word Ubsan.M.loaded_segments (0x639c0 : word) = Some W_63968.
Proof. vm_refl. Qed.
Lemma D_63968 : decode_any W_63968 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6396c : bv 32 := 0x00013903.
Lemma F_6396c : fetch_word Ubsan.M.loaded_segments (0x639c4 : word) = Some W_6396c.
Proof. vm_refl. Qed.
Lemma D_6396c : decode_any W_6396c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63970 : bv 32 := 0x02010113.
Lemma F_63970 : fetch_word Ubsan.M.loaded_segments (0x639c8 : word) = Some W_63970.
Proof. vm_refl. Qed.
Lemma D_63970 : decode_any W_63970 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63974 : bv 32 := 0x00008067.
Lemma F_63974 : fetch_word Ubsan.M.loaded_segments (0x639cc : word) = Some W_63974.
Proof. vm_refl. Qed.
Lemma D_63974 : decode_any W_63974 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6397c : bv 32 := 0x0035f713.
Lemma F_6397c : fetch_word Ubsan.M.loaded_segments (0x639d4 : word) = Some W_6397c.
Proof. vm_refl. Qed.
Lemma D_6397c : decode_any W_6397c = Some (OpImm ALU_AND 14 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63980 : bv 32 := 0x00058663.
Lemma F_63980 : fetch_word Ubsan.M.loaded_segments (0x639d8 : word) = Some W_63980.
Proof. vm_refl. Qed.
Lemma D_63980 : decode_any W_63980 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63984 : bv 32 := 0x0a071863.
Lemma F_63984 : fetch_word Ubsan.M.loaded_segments (0x639dc : word) = Some W_63984.
Proof. vm_refl. Qed.
Lemma D_63984 : decode_any W_63984 = Some (Branch BC_NE 14 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63988 : bv 32 := 0x0005a023.
Lemma F_63988 : fetch_word Ubsan.M.loaded_segments (0x639e0 : word) = Some W_63988.
Proof. vm_refl. Qed.
Lemma D_63988 : decode_any W_63988 = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6398c : bv 32 := 0x00367793.
Lemma F_6398c : fetch_word Ubsan.M.loaded_segments (0x639e4 : word) = Some W_6398c.
Proof. vm_refl. Qed.
Lemma D_6398c : decode_any W_6398c = Some (OpImm ALU_AND 15 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63990 : bv 32 := 0x00060663.
Lemma F_63990 : fetch_word Ubsan.M.loaded_segments (0x639e8 : word) = Some W_63990.
Proof. vm_refl. Qed.
Lemma D_63990 : decode_any W_63990 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63994 : bv 32 := 0x0a079063.
Lemma F_63994 : fetch_word Ubsan.M.loaded_segments (0x639ec : word) = Some W_63994.
Proof. vm_refl. Qed.
Lemma D_63994 : decode_any W_63994 = Some (Branch BC_NE 15 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63998 : bv 32 := 0x00062023.
Lemma F_63998 : fetch_word Ubsan.M.loaded_segments (0x639f0 : word) = Some W_63998.
Proof. vm_refl. Qed.
Lemma D_63998 : decode_any W_63998 = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6399c : bv 32 := 0x0036f813.
Lemma F_6399c : fetch_word Ubsan.M.loaded_segments (0x639f4 : word) = Some W_6399c.
Proof. vm_refl. Qed.
Lemma D_6399c : decode_any W_6399c = Some (OpImm ALU_AND 16 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639a0 : bv 32 := 0x00068663.
Lemma F_639a0 : fetch_word Ubsan.M.loaded_segments (0x639f8 : word) = Some W_639a0.
Proof. vm_refl. Qed.
Lemma D_639a0 : decode_any W_639a0 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639a4 : bv 32 := 0x08081863.
Lemma F_639a4 : fetch_word Ubsan.M.loaded_segments (0x639fc : word) = Some W_639a4.
Proof. vm_refl. Qed.
Lemma D_639a4 : decode_any W_639a4 = Some (Branch BC_NE 16 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639a8 : bv 32 := 0x0006a023.
Lemma F_639a8 : fetch_word Ubsan.M.loaded_segments (0x63a00 : word) = Some W_639a8.
Proof. vm_refl. Qed.
Lemma D_639a8 : decode_any W_639a8 = Some (Store SZ4 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639ac : bv 32 := 0x04050663.
Lemma F_639ac : fetch_word Ubsan.M.loaded_segments (0x63a04 : word) = Some W_639ac.
Proof. vm_refl. Qed.
Lemma D_639ac : decode_any W_639ac = Some (Branch BC_EQ 10 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639b0 : bv 32 := 0x00757893.
Lemma F_639b0 : fetch_word Ubsan.M.loaded_segments (0x63a08 : word) = Some W_639b0.
Proof. vm_refl. Qed.
Lemma D_639b0 : decode_any W_639b0 = Some (OpImm ALU_AND 17 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639b4 : bv 32 := 0x00058a63.
Lemma F_639b4 : fetch_word Ubsan.M.loaded_segments (0x63a0c : word) = Some W_639b4.
Proof. vm_refl. Qed.
Lemma D_639b4 : decode_any W_639b4 = Some (Branch BC_EQ 11 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639b8 : bv 32 := 0x00e8e733.
Lemma F_639b8 : fetch_word Ubsan.M.loaded_segments (0x63a10 : word) = Some W_639b8.
Proof. vm_refl. Qed.
Lemma D_639b8 : decode_any W_639b8 = Some (Op ALU_OR 14 17 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639bc : bv 32 := 0x06071c63.
Lemma F_639bc : fetch_word Ubsan.M.loaded_segments (0x63a14 : word) = Some W_639bc.
Proof. vm_refl. Qed.
Lemma D_639bc : decode_any W_639bc = Some (Branch BC_NE 14 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639c0 : bv 32 := 0x00052703.
Lemma F_639c0 : fetch_word Ubsan.M.loaded_segments (0x63a18 : word) = Some W_639c0.
Proof. vm_refl. Qed.
Lemma D_639c0 : decode_any W_639c0 = Some (Load SZ4 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639c4 : bv 32 := 0x00e5a023.
Lemma F_639c4 : fetch_word Ubsan.M.loaded_segments (0x63a1c : word) = Some W_639c4.
Proof. vm_refl. Qed.
Lemma D_639c4 : decode_any W_639c4 = Some (Store SZ4 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639c8 : bv 32 := 0x00060a63.
Lemma F_639c8 : fetch_word Ubsan.M.loaded_segments (0x63a20 : word) = Some W_639c8.
Proof. vm_refl. Qed.
Lemma D_639c8 : decode_any W_639c8 = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639cc : bv 32 := 0x00f8e5b3.
Lemma F_639cc : fetch_word Ubsan.M.loaded_segments (0x63a24 : word) = Some W_639cc.
Proof. vm_refl. Qed.
Lemma D_639cc : decode_any W_639cc = Some (Op ALU_OR 11 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639d0 : bv 32 := 0x06059263.
Lemma F_639d0 : fetch_word Ubsan.M.loaded_segments (0x63a28 : word) = Some W_639d0.
Proof. vm_refl. Qed.
Lemma D_639d0 : decode_any W_639d0 = Some (Branch BC_NE 11 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639d4 : bv 32 := 0x00452583.
Lemma F_639d4 : fetch_word Ubsan.M.loaded_segments (0x63a2c : word) = Some W_639d4.
Proof. vm_refl. Qed.
Lemma D_639d4 : decode_any W_639d4 = Some (Load SZ4 true 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639d8 : bv 32 := 0x00b62023.
Lemma F_639d8 : fetch_word Ubsan.M.loaded_segments (0x63a30 : word) = Some W_639d8.
Proof. vm_refl. Qed.
Lemma D_639d8 : decode_any W_639d8 = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639dc : bv 32 := 0x04068463.
Lemma F_639dc : fetch_word Ubsan.M.loaded_segments (0x63a34 : word) = Some W_639dc.
Proof. vm_refl. Qed.
Lemma D_639dc : decode_any W_639dc = Some (Branch BC_EQ 13 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639e0 : bv 32 := 0x0108e5b3.
Lemma F_639e0 : fetch_word Ubsan.M.loaded_segments (0x63a38 : word) = Some W_639e0.
Proof. vm_refl. Qed.
Lemma D_639e0 : decode_any W_639e0 = Some (Op ALU_OR 11 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639e4 : bv 32 := 0x04059863.
Lemma F_639e4 : fetch_word Ubsan.M.loaded_segments (0x63a3c : word) = Some W_639e4.
Proof. vm_refl. Qed.
Lemma D_639e4 : decode_any W_639e4 = Some (Branch BC_NE 11 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639e8 : bv 32 := 0x00852503.
Lemma F_639e8 : fetch_word Ubsan.M.loaded_segments (0x63a40 : word) = Some W_639e8.
Proof. vm_refl. Qed.
Lemma D_639e8 : decode_any W_639e8 = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639ec : bv 32 := 0x00a6a023.
Lemma F_639ec : fetch_word Ubsan.M.loaded_segments (0x63a44 : word) = Some W_639ec.
Proof. vm_refl. Qed.
Lemma D_639ec : decode_any W_639ec = Some (Store SZ4 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639f0 : bv 32 := 0x00058513.
Lemma F_639f0 : fetch_word Ubsan.M.loaded_segments (0x63a48 : word) = Some W_639f0.
Proof. vm_refl. Qed.
Lemma D_639f0 : decode_any W_639f0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639f4 : bv 32 := 0x00008067.
Lemma F_639f4 : fetch_word Ubsan.M.loaded_segments (0x63a4c : word) = Some W_639f4.
Proof. vm_refl. Qed.
Lemma D_639f4 : decode_any W_639f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63ac8 : bv 32 := 0xfd010113.
Lemma F_63ac8 : fetch_word Ubsan.M.loaded_segments (0x63b20 : word) = Some W_63ac8.
Proof. vm_refl. Qed.
Lemma D_63ac8 : decode_any W_63ac8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63acc : bv 32 := 0x02113423.
Lemma F_63acc : fetch_word Ubsan.M.loaded_segments (0x63b24 : word) = Some W_63acc.
Proof. vm_refl. Qed.
Lemma D_63acc : decode_any W_63acc = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63ad0 : bv 32 := 0x02813023.
Lemma F_63ad0 : fetch_word Ubsan.M.loaded_segments (0x63b28 : word) = Some W_63ad0.
Proof. vm_refl. Qed.
Lemma D_63ad0 : decode_any W_63ad0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63ad4 : bv 32 := 0x00913c23.
Lemma F_63ad4 : fetch_word Ubsan.M.loaded_segments (0x63b2c : word) = Some W_63ad4.
Proof. vm_refl. Qed.
Lemma D_63ad4 : decode_any W_63ad4 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63ad8 : bv 32 := 0x0e058863.
Lemma F_63ad8 : fetch_word Ubsan.M.loaded_segments (0x63b30 : word) = Some W_63ad8.
Proof. vm_refl. Qed.
Lemma D_63ad8 : decode_any W_63ad8 = Some (Branch BC_EQ 11 0 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63adc : bv 32 := 0x10050a63.
Lemma F_63adc : fetch_word Ubsan.M.loaded_segments (0x63b34 : word) = Some W_63adc.
Proof. vm_refl. Qed.
Lemma D_63adc : decode_any W_63adc = Some (Branch BC_EQ 10 0 276, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63ae0 : bv 32 := 0x0ea58063.
Lemma F_63ae0 : fetch_word Ubsan.M.loaded_segments (0x63b38 : word) = Some W_63ae0.
Proof. vm_refl. Qed.
Lemma D_63ae0 : decode_any W_63ae0 = Some (Branch BC_EQ 11 10 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63ae4 : bv 32 := 0x0075f613.
Lemma F_63ae4 : fetch_word Ubsan.M.loaded_segments (0x63b3c : word) = Some W_63ae4.
Proof. vm_refl. Qed.
Lemma D_63ae4 : decode_any W_63ae4 = Some (OpImm ALU_AND 12 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63ae8 : bv 32 := 0x1c061e63.
Lemma F_63ae8 : fetch_word Ubsan.M.loaded_segments (0x63b40 : word) = Some W_63ae8.
Proof. vm_refl. Qed.
Lemma D_63ae8 : decode_any W_63ae8 = Some (Branch BC_NE 12 0 476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63aec : bv 32 := 0x00757613.
Lemma F_63aec : fetch_word Ubsan.M.loaded_segments (0x63b44 : word) = Some W_63aec.
Proof. vm_refl. Qed.
Lemma D_63aec : decode_any W_63aec = Some (OpImm ALU_AND 12 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63af0 : bv 32 := 0x1c061a63.
Lemma F_63af0 : fetch_word Ubsan.M.loaded_segments (0x63b48 : word) = Some W_63af0.
Proof. vm_refl. Qed.
Lemma D_63af0 : decode_any W_63af0 = Some (Branch BC_NE 12 0 468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63af4 : bv 32 := 0x0085a603.
Lemma F_63af4 : fetch_word Ubsan.M.loaded_segments (0x63b4c : word) = Some W_63af4.
Proof. vm_refl. Qed.
Lemma D_63af4 : decode_any W_63af4 = Some (Load SZ4 true 12 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63af8 : bv 32 := 0x00852683.
Lemma F_63af8 : fetch_word Ubsan.M.loaded_segments (0x63b50 : word) = Some W_63af8.
Proof. vm_refl. Qed.
Lemma D_63af8 : decode_any W_63af8 = Some (Load SZ4 true 13 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63afc : bv 32 := 0x10d61e63.
Lemma F_63afc : fetch_word Ubsan.M.loaded_segments (0x63b54 : word) = Some W_63afc.
Proof. vm_refl. Qed.
Lemma D_63afc : decode_any W_63afc = Some (Branch BC_NE 12 13 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b00 : bv 32 := 0x03053603.
Lemma F_63b00 : fetch_word Ubsan.M.loaded_segments (0x63b58 : word) = Some W_63b00.
Proof. vm_refl. Qed.
Lemma D_63b00 : decode_any W_63b00 = Some (Load SZ8 true 12 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b04 : bv 32 := 0x00c13823.
Lemma F_63b04 : fetch_word Ubsan.M.loaded_segments (0x63b5c : word) = Some W_63b04.
Proof. vm_refl. Qed.
Lemma D_63b04 : decode_any W_63b04 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b08 : bv 32 := 0x02060063.
Lemma F_63b08 : fetch_word Ubsan.M.loaded_segments (0x63b60 : word) = Some W_63b08.
Proof. vm_refl. Qed.
Lemma D_63b08 : decode_any W_63b08 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b28 : bv 32 := 0x0305b403.
Lemma F_63b28 : fetch_word Ubsan.M.loaded_segments (0x63b80 : word) = Some W_63b28.
Proof. vm_refl. Qed.
Lemma D_63b28 : decode_any W_63b28 = Some (Load SZ8 true 8 11 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b2c : bv 32 := 0x08040a63.
Lemma F_63b2c : fetch_word Ubsan.M.loaded_segments (0x63b84 : word) = Some W_63b2c.
Proof. vm_refl. Qed.
Lemma D_63b2c : decode_any W_63b2c = Some (Branch BC_EQ 8 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b30 : bv 32 := 0x00050493.
Lemma F_63b30 : fetch_word Ubsan.M.loaded_segments (0x63b88 : word) = Some W_63b30.
Proof. vm_refl. Qed.
Lemma D_63b30 : decode_any W_63b30 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b34 : bv 32 := 0x00c10613.
Lemma F_63b34 : fetch_word Ubsan.M.loaded_segments (0x63b8c : word) = Some W_63b34.
Proof. vm_refl. Qed.
Lemma D_63b34 : decode_any W_63b34 = Some (OpImm ALU_ADD 12 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b38 : bv 32 := 0x00040513.
Lemma F_63b38 : fetch_word Ubsan.M.loaded_segments (0x63b90 : word) = Some W_63b38.
Proof. vm_refl. Qed.
Lemma D_63b38 : decode_any W_63b38 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b3c : bv 32 := 0x00000593.
Lemma F_63b3c : fetch_word Ubsan.M.loaded_segments (0x63b94 : word) = Some W_63b3c.
Proof. vm_refl. Qed.
Lemma D_63b3c : decode_any W_63b3c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b40 : bv 32 := 0x719020ef.
Lemma F_63b40 : fetch_word Ubsan.M.loaded_segments (0x63b98 : word) = Some W_63b40.
Proof. vm_refl. Qed.
Lemma D_63b40 : decode_any W_63b40 = Some (Jal 1 12056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b44 : bv 32 := 0x00c12503.
Lemma F_63b44 : fetch_word Ubsan.M.loaded_segments (0x63b9c : word) = Some W_63b44.
Proof. vm_refl. Qed.
Lemma D_63b44 : decode_any W_63b44 = Some (Load SZ4 true 10 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b48 : bv 32 := 0x10050663.
Lemma F_63b48 : fetch_word Ubsan.M.loaded_segments (0x63ba0 : word) = Some W_63b48.
Proof. vm_refl. Qed.
Lemma D_63b48 : decode_any W_63b48 = Some (Branch BC_EQ 10 0 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b4c : bv 32 := 0x00040513.
Lemma F_63b4c : fetch_word Ubsan.M.loaded_segments (0x63ba4 : word) = Some W_63b4c.
Proof. vm_refl. Qed.
Lemma D_63b4c : decode_any W_63b4c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b50 : bv 32 := 0x5f1020ef.
Lemma F_63b50 : fetch_word Ubsan.M.loaded_segments (0x63ba8 : word) = Some W_63b50.
Proof. vm_refl. Qed.
Lemma D_63b50 : decode_any W_63b50 = Some (Jal 1 11760, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b54 : bv 32 := 0x12050463.
Lemma F_63b54 : fetch_word Ubsan.M.loaded_segments (0x63bac : word) = Some W_63b54.
Proof. vm_refl. Qed.
Lemma D_63b54 : decode_any W_63b54 = Some (Branch BC_EQ 10 0 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b58 : bv 32 := 0x00048593.
Lemma F_63b58 : fetch_word Ubsan.M.loaded_segments (0x63bb0 : word) = Some W_63b58.
Proof. vm_refl. Qed.
Lemma D_63b58 : decode_any W_63b58 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b5c : bv 32 := 0x0304b603.
Lemma F_63b5c : fetch_word Ubsan.M.loaded_segments (0x63bb4 : word) = Some W_63b5c.
Proof. vm_refl. Qed.
Lemma D_63b5c : decode_any W_63b5c = Some (Load SZ8 true 12 9 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b60 : bv 32 := 0x00c13823.
Lemma F_63b60 : fetch_word Ubsan.M.loaded_segments (0x63bb8 : word) = Some W_63b60.
Proof. vm_refl. Qed.
Lemma D_63b60 : decode_any W_63b60 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b64 : bv 32 := 0x00060c63.
Lemma F_63b64 : fetch_word Ubsan.M.loaded_segments (0x63bbc : word) = Some W_63b64.
Proof. vm_refl. Qed.
Lemma D_63b64 : decode_any W_63b64 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b7c : bv 32 := 0x02a5b823.
Lemma F_63b7c : fetch_word Ubsan.M.loaded_segments (0x63bd4 : word) = Some W_63b7c.
Proof. vm_refl. Qed.
Lemma D_63b7c : decode_any W_63b7c = Some (Store SZ8 11 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b80 : bv 32 := 0x01010613.
Lemma F_63b80 : fetch_word Ubsan.M.loaded_segments (0x63bd8 : word) = Some W_63b80.
Proof. vm_refl. Qed.
Lemma D_63b80 : decode_any W_63b80 = Some (OpImm ALU_ADD 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b84 : bv 32 := 0x00000593.
Lemma F_63b84 : fetch_word Ubsan.M.loaded_segments (0x63bdc : word) = Some W_63b84.
Proof. vm_refl. Qed.
Lemma D_63b84 : decode_any W_63b84 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b88 : bv 32 := 0x6d1020ef.
Lemma F_63b88 : fetch_word Ubsan.M.loaded_segments (0x63be0 : word) = Some W_63b88.
Proof. vm_refl. Qed.
Lemma D_63b88 : decode_any W_63b88 = Some (Jal 1 11984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b8c : bv 32 := 0x01012503.
Lemma F_63b8c : fetch_word Ubsan.M.loaded_segments (0x63be4 : word) = Some W_63b8c.
Proof. vm_refl. Qed.
Lemma D_63b8c : decode_any W_63b8c = Some (Load SZ4 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b90 : bv 32 := 0x02051863.
Lemma F_63b90 : fetch_word Ubsan.M.loaded_segments (0x63be8 : word) = Some W_63b90.
Proof. vm_refl. Qed.
Lemma D_63b90 : decode_any W_63b90 = Some (Branch BC_NE 10 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63bc0 : bv 32 := 0x00000513.
Lemma F_63bc0 : fetch_word Ubsan.M.loaded_segments (0x63c18 : word) = Some W_63bc0.
Proof. vm_refl. Qed.
Lemma D_63bc0 : decode_any W_63bc0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63bc4 : bv 32 := 0x0ec0006f.
Lemma F_63bc4 : fetch_word Ubsan.M.loaded_segments (0x63c1c : word) = Some W_63bc4.
Proof. vm_refl. Qed.
Lemma D_63bc4 : decode_any W_63bc4 = Some (Jal 0 236, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63c7c : bv 32 := 0x00095517.
Lemma F_63c7c : fetch_word Ubsan.M.loaded_segments (0x63cd4 : word) = Some W_63c7c.
Proof. vm_refl. Qed.
Lemma D_63c7c : decode_any W_63c7c = Some (Auipc 10 149, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63c80 : bv 32 := 0x44c53503.
Lemma F_63c80 : fetch_word Ubsan.M.loaded_segments (0x63cd8 : word) = Some W_63c80.
Proof. vm_refl. Qed.
Lemma D_63c80 : decode_any W_63c80 = Some (Load SZ8 true 10 10 1100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63c84 : bv 32 := 0x00052503.
Lemma F_63c84 : fetch_word Ubsan.M.loaded_segments (0x63cdc : word) = Some W_63c84.
Proof. vm_refl. Qed.
Lemma D_63c84 : decode_any W_63c84 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63c88 : bv 32 := 0x00500593.
Lemma F_63c88 : fetch_word Ubsan.M.loaded_segments (0x63ce0 : word) = Some W_63c88.
Proof. vm_refl. Qed.
Lemma D_63c88 : decode_any W_63c88 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63c8c : bv 32 := 0x02a5c063.
Lemma F_63c8c : fetch_word Ubsan.M.loaded_segments (0x63ce4 : word) = Some W_63c8c.
Proof. vm_refl. Qed.
Lemma D_63c8c : decode_any W_63c8c = Some (Branch BC_LT 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63c90 : bv 32 := 0xfffae517.
Lemma F_63c90 : fetch_word Ubsan.M.loaded_segments (0x63ce8 : word) = Some W_63c90.
Proof. vm_refl. Qed.
Lemma D_63c90 : decode_any W_63c90 = Some (Auipc 10 1048494, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63c94 : bv 32 := 0xfffaf597.
Lemma F_63c94 : fetch_word Ubsan.M.loaded_segments (0x63cec : word) = Some W_63c94.
Proof. vm_refl. Qed.
Lemma D_63c94 : decode_any W_63c94 = Some (Auipc 11 1048495, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63c98 : bv 32 := 0x38850513.
Lemma F_63c98 : fetch_word Ubsan.M.loaded_segments (0x63cf0 : word) = Some W_63c98.
Proof. vm_refl. Qed.
Lemma D_63c98 : decode_any W_63c98 = Some (OpImm ALU_ADD 10 10 904, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63c9c : bv 32 := 0x9e158593.
Lemma F_63c9c : fetch_word Ubsan.M.loaded_segments (0x63cf4 : word) = Some W_63c9c.
Proof. vm_refl. Qed.
Lemma D_63c9c : decode_any W_63c9c = Some (OpImm ALU_ADD 11 11 2529, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63ca0 : bv 32 := 0x00100613.
Lemma F_63ca0 : fetch_word Ubsan.M.loaded_segments (0x63cf8 : word) = Some W_63ca0.
Proof. vm_refl. Qed.
Lemma D_63ca0 : decode_any W_63ca0 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63ca4 : bv 32 := 0xcc8f90ef.
Lemma F_63ca4 : fetch_word Ubsan.M.loaded_segments (0x63cfc : word) = Some W_63ca4.
Proof. vm_refl. Qed.
Lemma D_63ca4 : decode_any W_63ca4 = Some (Jal 1 2069704, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63ca8 : bv 32 := 0x0080006f.
Lemma F_63ca8 : fetch_word Ubsan.M.loaded_segments (0x63d00 : word) = Some W_63ca8.
Proof. vm_refl. Qed.
Lemma D_63ca8 : decode_any W_63ca8 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63cb0 : bv 32 := 0x02813083.
Lemma F_63cb0 : fetch_word Ubsan.M.loaded_segments (0x63d08 : word) = Some W_63cb0.
Proof. vm_refl. Qed.
Lemma D_63cb0 : decode_any W_63cb0 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63cb4 : bv 32 := 0x02013403.
Lemma F_63cb4 : fetch_word Ubsan.M.loaded_segments (0x63d0c : word) = Some W_63cb4.
Proof. vm_refl. Qed.
Lemma D_63cb4 : decode_any W_63cb4 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63cb8 : bv 32 := 0x01813483.
Lemma F_63cb8 : fetch_word Ubsan.M.loaded_segments (0x63d10 : word) = Some W_63cb8.
Proof. vm_refl. Qed.
Lemma D_63cb8 : decode_any W_63cb8 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63cbc : bv 32 := 0x03010113.
Lemma F_63cbc : fetch_word Ubsan.M.loaded_segments (0x63d14 : word) = Some W_63cbc.
Proof. vm_refl. Qed.
Lemma D_63cbc : decode_any W_63cbc = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63cc0 : bv 32 := 0x00008067.
Lemma F_63cc0 : fetch_word Ubsan.M.loaded_segments (0x63d18 : word) = Some W_63cc0.
Proof. vm_refl. Qed.
Lemma D_63cc0 : decode_any W_63cc0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

