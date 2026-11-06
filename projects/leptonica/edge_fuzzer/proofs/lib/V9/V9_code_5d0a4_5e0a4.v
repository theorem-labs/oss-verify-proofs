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
Definition W_5d16c : bv 32 := 0xff010113.
Lemma F_5d16c : fetch_word Ubsan.M.loaded_segments (0x5d1c4 : word) = Some W_5d16c.
Proof. vm_refl. Qed.
Lemma D_5d16c : decode_any W_5d16c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d170 : bv 32 := 0x00113423.
Lemma F_5d170 : fetch_word Ubsan.M.loaded_segments (0x5d1c8 : word) = Some W_5d170.
Proof. vm_refl. Qed.
Lemma D_5d170 : decode_any W_5d170 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d174 : bv 32 := 0x00813023.
Lemma F_5d174 : fetch_word Ubsan.M.loaded_segments (0x5d1cc : word) = Some W_5d174.
Proof. vm_refl. Qed.
Lemma D_5d174 : decode_any W_5d174 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d178 : bv 32 := 0x00060413.
Lemma F_5d178 : fetch_word Ubsan.M.loaded_segments (0x5d1d0 : word) = Some W_5d178.
Proof. vm_refl. Qed.
Lemma D_5d178 : decode_any W_5d178 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d17c : bv 32 := 0x00050613.
Lemma F_5d17c : fetch_word Ubsan.M.loaded_segments (0x5d1d4 : word) = Some W_5d17c.
Proof. vm_refl. Qed.
Lemma D_5d17c : decode_any W_5d17c = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d180 : bv 32 := 0xfffbf517.
Lemma F_5d180 : fetch_word Ubsan.M.loaded_segments (0x5d1d8 : word) = Some W_5d180.
Proof. vm_refl. Qed.
Lemma D_5d180 : decode_any W_5d180 = Some (Auipc 10 1048511, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d184 : bv 32 := 0xa8a50513.
Lemma F_5d184 : fetch_word Ubsan.M.loaded_segments (0x5d1dc : word) = Some W_5d184.
Proof. vm_refl. Qed.
Lemma D_5d184 : decode_any W_5d184 = Some (OpImm ALU_ADD 10 10 2698, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d188 : bv 32 := 0x018000ef.
Lemma F_5d188 : fetch_word Ubsan.M.loaded_segments (0x5d1e0 : word) = Some W_5d188.
Proof. vm_refl. Qed.
Lemma D_5d188 : decode_any W_5d188 = Some (Jal 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d18c : bv 32 := 0x00040513.
Lemma F_5d18c : fetch_word Ubsan.M.loaded_segments (0x5d1e4 : word) = Some W_5d18c.
Proof. vm_refl. Qed.
Lemma D_5d18c : decode_any W_5d18c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d190 : bv 32 := 0x00813083.
Lemma F_5d190 : fetch_word Ubsan.M.loaded_segments (0x5d1e8 : word) = Some W_5d190.
Proof. vm_refl. Qed.
Lemma D_5d190 : decode_any W_5d190 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d194 : bv 32 := 0x00013403.
Lemma F_5d194 : fetch_word Ubsan.M.loaded_segments (0x5d1ec : word) = Some W_5d194.
Proof. vm_refl. Qed.
Lemma D_5d194 : decode_any W_5d194 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d198 : bv 32 := 0x01010113.
Lemma F_5d198 : fetch_word Ubsan.M.loaded_segments (0x5d1f0 : word) = Some W_5d198.
Proof. vm_refl. Qed.
Lemma D_5d198 : decode_any W_5d198 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d19c : bv 32 := 0x00008067.
Lemma F_5d19c : fetch_word Ubsan.M.loaded_segments (0x5d1f4 : word) = Some W_5d19c.
Proof. vm_refl. Qed.
Lemma D_5d19c : decode_any W_5d19c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d23c : bv 32 := 0xff010113.
Lemma F_5d23c : fetch_word Ubsan.M.loaded_segments (0x5d294 : word) = Some W_5d23c.
Proof. vm_refl. Qed.
Lemma D_5d23c : decode_any W_5d23c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d240 : bv 32 := 0x00113423.
Lemma F_5d240 : fetch_word Ubsan.M.loaded_segments (0x5d298 : word) = Some W_5d240.
Proof. vm_refl. Qed.
Lemma D_5d240 : decode_any W_5d240 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d244 : bv 32 := 0x00813023.
Lemma F_5d244 : fetch_word Ubsan.M.loaded_segments (0x5d29c : word) = Some W_5d244.
Proof. vm_refl. Qed.
Lemma D_5d244 : decode_any W_5d244 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d248 : bv 32 := 0x00060413.
Lemma F_5d248 : fetch_word Ubsan.M.loaded_segments (0x5d2a0 : word) = Some W_5d248.
Proof. vm_refl. Qed.
Lemma D_5d248 : decode_any W_5d248 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d24c : bv 32 := 0x00050613.
Lemma F_5d24c : fetch_word Ubsan.M.loaded_segments (0x5d2a4 : word) = Some W_5d24c.
Proof. vm_refl. Qed.
Lemma D_5d24c : decode_any W_5d24c = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d250 : bv 32 := 0xfffbf517.
Lemma F_5d250 : fetch_word Ubsan.M.loaded_segments (0x5d2a8 : word) = Some W_5d250.
Proof. vm_refl. Qed.
Lemma D_5d250 : decode_any W_5d250 = Some (Auipc 10 1048511, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d254 : bv 32 := 0x9ba50513.
Lemma F_5d254 : fetch_word Ubsan.M.loaded_segments (0x5d2ac : word) = Some W_5d254.
Proof. vm_refl. Qed.
Lemma D_5d254 : decode_any W_5d254 = Some (OpImm ALU_ADD 10 10 2490, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d258 : bv 32 := 0xf49ff0ef.
Lemma F_5d258 : fetch_word Ubsan.M.loaded_segments (0x5d2b0 : word) = Some W_5d258.
Proof. vm_refl. Qed.
Lemma D_5d258 : decode_any W_5d258 = Some (Jal 1 2096968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d25c : bv 32 := 0x00040513.
Lemma F_5d25c : fetch_word Ubsan.M.loaded_segments (0x5d2b4 : word) = Some W_5d25c.
Proof. vm_refl. Qed.
Lemma D_5d25c : decode_any W_5d25c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d260 : bv 32 := 0x00813083.
Lemma F_5d260 : fetch_word Ubsan.M.loaded_segments (0x5d2b8 : word) = Some W_5d260.
Proof. vm_refl. Qed.
Lemma D_5d260 : decode_any W_5d260 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d264 : bv 32 := 0x00013403.
Lemma F_5d264 : fetch_word Ubsan.M.loaded_segments (0x5d2bc : word) = Some W_5d264.
Proof. vm_refl. Qed.
Lemma D_5d264 : decode_any W_5d264 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d268 : bv 32 := 0x01010113.
Lemma F_5d268 : fetch_word Ubsan.M.loaded_segments (0x5d2c0 : word) = Some W_5d268.
Proof. vm_refl. Qed.
Lemma D_5d268 : decode_any W_5d268 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d26c : bv 32 := 0x00008067.
Lemma F_5d26c : fetch_word Ubsan.M.loaded_segments (0x5d2c4 : word) = Some W_5d26c.
Proof. vm_refl. Qed.
Lemma D_5d26c : decode_any W_5d26c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8b0 : bv 32 := 0xfe010113.
Lemma F_5d8b0 : fetch_word Ubsan.M.loaded_segments (0x5d908 : word) = Some W_5d8b0.
Proof. vm_refl. Qed.
Lemma D_5d8b0 : decode_any W_5d8b0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8b4 : bv 32 := 0x00113c23.
Lemma F_5d8b4 : fetch_word Ubsan.M.loaded_segments (0x5d90c : word) = Some W_5d8b4.
Proof. vm_refl. Qed.
Lemma D_5d8b4 : decode_any W_5d8b4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8b8 : bv 32 := 0x00813823.
Lemma F_5d8b8 : fetch_word Ubsan.M.loaded_segments (0x5d910 : word) = Some W_5d8b8.
Proof. vm_refl. Qed.
Lemma D_5d8b8 : decode_any W_5d8b8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8bc : bv 32 := 0x00913423.
Lemma F_5d8bc : fetch_word Ubsan.M.loaded_segments (0x5d914 : word) = Some W_5d8bc.
Proof. vm_refl. Qed.
Lemma D_5d8bc : decode_any W_5d8bc = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8c0 : bv 32 := 0x02050a63.
Lemma F_5d8c0 : fetch_word Ubsan.M.loaded_segments (0x5d918 : word) = Some W_5d8c0.
Proof. vm_refl. Qed.
Lemma D_5d8c0 : decode_any W_5d8c0 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8c4 : bv 32 := 0x00050413.
Lemma F_5d8c4 : fetch_word Ubsan.M.loaded_segments (0x5d91c : word) = Some W_5d8c4.
Proof. vm_refl. Qed.
Lemma D_5d8c4 : decode_any W_5d8c4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8c8 : bv 32 := 0x00757513.
Lemma F_5d8c8 : fetch_word Ubsan.M.loaded_segments (0x5d920 : word) = Some W_5d8c8.
Proof. vm_refl. Qed.
Lemma D_5d8c8 : decode_any W_5d8c8 = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8cc : bv 32 := 0x08051663.
Lemma F_5d8cc : fetch_word Ubsan.M.loaded_segments (0x5d924 : word) = Some W_5d8cc.
Proof. vm_refl. Qed.
Lemma D_5d8cc : decode_any W_5d8cc = Some (Branch BC_NE 10 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8d0 : bv 32 := 0x00058493.
Lemma F_5d8d0 : fetch_word Ubsan.M.loaded_segments (0x5d928 : word) = Some W_5d8d0.
Proof. vm_refl. Qed.
Lemma D_5d8d0 : decode_any W_5d8d0 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8d4 : bv 32 := 0x00043503.
Lemma F_5d8d4 : fetch_word Ubsan.M.loaded_segments (0x5d92c : word) = Some W_5d8d4.
Proof. vm_refl. Qed.
Lemma D_5d8d4 : decode_any W_5d8d4 = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8d8 : bv 32 := 0x00050463.
Lemma F_5d8d8 : fetch_word Ubsan.M.loaded_segments (0x5d930 : word) = Some W_5d8d8.
Proof. vm_refl. Qed.
Lemma D_5d8d8 : decode_any W_5d8d8 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8e0 : bv 32 := 0x04048863.
Lemma F_5d8e0 : fetch_word Ubsan.M.loaded_segments (0x5d938 : word) = Some W_5d8e0.
Proof. vm_refl. Qed.
Lemma D_5d8e0 : decode_any W_5d8e0 = Some (Branch BC_EQ 9 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d930 : bv 32 := 0x00000593.
Lemma F_5d930 : fetch_word Ubsan.M.loaded_segments (0x5d988 : word) = Some W_5d930.
Proof. vm_refl. Qed.
Lemma D_5d930 : decode_any W_5d930 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d934 : bv 32 := 0x00000513.
Lemma F_5d934 : fetch_word Ubsan.M.loaded_segments (0x5d98c : word) = Some W_5d934.
Proof. vm_refl. Qed.
Lemma D_5d934 : decode_any W_5d934 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d938 : bv 32 := 0x00b43023.
Lemma F_5d938 : fetch_word Ubsan.M.loaded_segments (0x5d990 : word) = Some W_5d938.
Proof. vm_refl. Qed.
Lemma D_5d938 : decode_any W_5d938 = Some (Store SZ8 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d93c : bv 32 := 0x0080006f.
Lemma F_5d93c : fetch_word Ubsan.M.loaded_segments (0x5d994 : word) = Some W_5d93c.
Proof. vm_refl. Qed.
Lemma D_5d93c : decode_any W_5d93c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d944 : bv 32 := 0x01813083.
Lemma F_5d944 : fetch_word Ubsan.M.loaded_segments (0x5d99c : word) = Some W_5d944.
Proof. vm_refl. Qed.
Lemma D_5d944 : decode_any W_5d944 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d948 : bv 32 := 0x01013403.
Lemma F_5d948 : fetch_word Ubsan.M.loaded_segments (0x5d9a0 : word) = Some W_5d948.
Proof. vm_refl. Qed.
Lemma D_5d948 : decode_any W_5d948 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d94c : bv 32 := 0x00813483.
Lemma F_5d94c : fetch_word Ubsan.M.loaded_segments (0x5d9a4 : word) = Some W_5d94c.
Proof. vm_refl. Qed.
Lemma D_5d94c : decode_any W_5d94c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d950 : bv 32 := 0x02010113.
Lemma F_5d950 : fetch_word Ubsan.M.loaded_segments (0x5d9a8 : word) = Some W_5d950.
Proof. vm_refl. Qed.
Lemma D_5d950 : decode_any W_5d950 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d954 : bv 32 := 0x00008067.
Lemma F_5d954 : fetch_word Ubsan.M.loaded_segments (0x5d9ac : word) = Some W_5d954.
Proof. vm_refl. Qed.
Lemma D_5d954 : decode_any W_5d954 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

