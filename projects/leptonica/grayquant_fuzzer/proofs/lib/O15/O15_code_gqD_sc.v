(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.H Require GcFlushS15.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.grayquant_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_170cc : bv 32 := 0xfd010113.
Lemma F_170cc : fetch_word Plain.M.loaded_segments (0x17124 : word) = Some W_170cc.
Proof. vm_refl. Qed.
Lemma D_170cc : decode_any W_170cc = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170d0 : bv 32 := 0x02113423.
Lemma F_170d0 : fetch_word Plain.M.loaded_segments (0x17128 : word) = Some W_170d0.
Proof. vm_refl. Qed.
Lemma D_170d0 : decode_any W_170d0 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170d4 : bv 32 := 0x02813023.
Lemma F_170d4 : fetch_word Plain.M.loaded_segments (0x1712c : word) = Some W_170d4.
Proof. vm_refl. Qed.
Lemma D_170d4 : decode_any W_170d4 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170d8 : bv 32 := 0x00913c23.
Lemma F_170d8 : fetch_word Plain.M.loaded_segments (0x17130 : word) = Some W_170d8.
Proof. vm_refl. Qed.
Lemma D_170d8 : decode_any W_170d8 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170dc : bv 32 := 0x04050863.
Lemma F_170dc : fetch_word Plain.M.loaded_segments (0x17134 : word) = Some W_170dc.
Proof. vm_refl. Qed.
Lemma D_170dc : decode_any W_170dc = Some (Branch BC_EQ 10 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170e0 : bv 32 := 0x04058263.
Lemma F_170e0 : fetch_word Plain.M.loaded_segments (0x17138 : word) = Some W_170e0.
Proof. vm_refl. Qed.
Lemma D_170e0 : decode_any W_170e0 = Some (Branch BC_EQ 11 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170e4 : bv 32 := 0x03053603.
Lemma F_170e4 : fetch_word Plain.M.loaded_segments (0x1713c : word) = Some W_170e4.
Proof. vm_refl. Qed.
Lemma D_170e4 : decode_any W_170e4 = Some (Load SZ8 true 12 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170e8 : bv 32 := 0x00c13823.
Lemma F_170e8 : fetch_word Plain.M.loaded_segments (0x17140 : word) = Some W_170e8.
Proof. vm_refl. Qed.
Lemma D_170e8 : decode_any W_170e8 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170ec : bv 32 := 0x00060e63.
Lemma F_170ec : fetch_word Plain.M.loaded_segments (0x17144 : word) = Some W_170ec.
Proof. vm_refl. Qed.
Lemma D_170ec : decode_any W_170ec = Some (Branch BC_EQ 12 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170f0 : bv 32 := 0x00050413.
Lemma F_170f0 : fetch_word Plain.M.loaded_segments (0x17148 : word) = Some W_170f0.
Proof. vm_refl. Qed.
Lemma D_170f0 : decode_any W_170f0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170f4 : bv 32 := 0x01010513.
Lemma F_170f4 : fetch_word Plain.M.loaded_segments (0x1714c : word) = Some W_170f4.
Proof. vm_refl. Qed.
Lemma D_170f4 : decode_any W_170f4 = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170f8 : bv 32 := 0x00058493.
Lemma F_170f8 : fetch_word Plain.M.loaded_segments (0x17150 : word) = Some W_170f8.
Proof. vm_refl. Qed.
Lemma D_170f8 : decode_any W_170f8 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170fc : bv 32 := 0x190010ef.
Lemma F_170fc : fetch_word Plain.M.loaded_segments (0x17154 : word) = Some W_170fc.
Proof. vm_refl. Qed.
Lemma D_170fc : decode_any W_170fc = Some (Jal 1 4496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17100 : bv 32 := 0x00040513.
Lemma F_17100 : fetch_word Plain.M.loaded_segments (0x17158 : word) = Some W_17100.
Proof. vm_refl. Qed.
Lemma D_17100 : decode_any W_17100 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17104 : bv 32 := 0x00048593.
Lemma F_17104 : fetch_word Plain.M.loaded_segments (0x1715c : word) = Some W_17104.
Proof. vm_refl. Qed.
Lemma D_17104 : decode_any W_17104 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17108 : bv 32 := 0x02b53823.
Lemma F_17108 : fetch_word Plain.M.loaded_segments (0x17160 : word) = Some W_17108.
Proof. vm_refl. Qed.
Lemma D_17108 : decode_any W_17108 = Some (Store SZ8 10 11 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1710c : bv 32 := 0x00c10613.
Lemma F_1710c : fetch_word Plain.M.loaded_segments (0x17164 : word) = Some W_1710c.
Proof. vm_refl. Qed.
Lemma D_1710c : decode_any W_1710c = Some (OpImm ALU_ADD 12 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17110 : bv 32 := 0x00058513.
Lemma F_17110 : fetch_word Plain.M.loaded_segments (0x17168 : word) = Some W_17110.
Proof. vm_refl. Qed.
Lemma D_17110 : decode_any W_17110 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17114 : bv 32 := 0x00000593.
Lemma F_17114 : fetch_word Plain.M.loaded_segments (0x1716c : word) = Some W_17114.
Proof. vm_refl. Qed.
Lemma D_17114 : decode_any W_17114 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17118 : bv 32 := 0x679000ef.
Lemma F_17118 : fetch_word Plain.M.loaded_segments (0x17170 : word) = Some W_17118.
Proof. vm_refl. Qed.
Lemma D_17118 : decode_any W_17118 = Some (Jal 1 3704, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1711c : bv 32 := 0x00c12503.
Lemma F_1711c : fetch_word Plain.M.loaded_segments (0x17174 : word) = Some W_1711c.
Proof. vm_refl. Qed.
Lemma D_1711c : decode_any W_1711c = Some (Load SZ4 true 10 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17120 : bv 32 := 0x04050463.
Lemma F_17120 : fetch_word Plain.M.loaded_segments (0x17178 : word) = Some W_17120.
Proof. vm_refl. Qed.
Lemma D_17120 : decode_any W_17120 = Some (Branch BC_EQ 10 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17124 : bv 32 := 0x00000513.
Lemma F_17124 : fetch_word Plain.M.loaded_segments (0x1717c : word) = Some W_17124.
Proof. vm_refl. Qed.
Lemma D_17124 : decode_any W_17124 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17128 : bv 32 := 0x0740006f.
Lemma F_17128 : fetch_word Plain.M.loaded_segments (0x17180 : word) = Some W_17128.
Proof. vm_refl. Qed.
Lemma D_17128 : decode_any W_17128 = Some (Jal 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1712c : bv 32 := 0x00015517.
Lemma F_1712c : fetch_word Plain.M.loaded_segments (0x17184 : word) = Some W_1712c.
Proof. vm_refl. Qed.
Lemma D_1712c : decode_any W_1712c = Some (Auipc 10 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17130 : bv 32 := 0x5fc53503.
Lemma F_17130 : fetch_word Plain.M.loaded_segments (0x17188 : word) = Some W_17130.
Proof. vm_refl. Qed.
Lemma D_17130 : decode_any W_17130 = Some (Load SZ8 true 10 10 1532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17134 : bv 32 := 0x00052503.
Lemma F_17134 : fetch_word Plain.M.loaded_segments (0x1718c : word) = Some W_17134.
Proof. vm_refl. Qed.
Lemma D_17134 : decode_any W_17134 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17138 : bv 32 := 0x00500593.
Lemma F_17138 : fetch_word Plain.M.loaded_segments (0x17190 : word) = Some W_17138.
Proof. vm_refl. Qed.
Lemma D_17138 : decode_any W_17138 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1713c : bv 32 := 0x04a5ce63.
Lemma F_1713c : fetch_word Plain.M.loaded_segments (0x17194 : word) = Some W_1713c.
Proof. vm_refl. Qed.
Lemma D_1713c : decode_any W_1713c = Some (Branch BC_LT 11 10 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17140 : bv 32 := 0xffff9517.
Lemma F_17140 : fetch_word Plain.M.loaded_segments (0x17198 : word) = Some W_17140.
Proof. vm_refl. Qed.
Lemma D_17140 : decode_any W_17140 = Some (Auipc 10 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17144 : bv 32 := 0xffffa597.
Lemma F_17144 : fetch_word Plain.M.loaded_segments (0x1719c : word) = Some W_17144.
Proof. vm_refl. Qed.
Lemma D_17144 : decode_any W_17144 = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17148 : bv 32 := 0x23350513.
Lemma F_17148 : fetch_word Plain.M.loaded_segments (0x171a0 : word) = Some W_17148.
Proof. vm_refl. Qed.
Lemma D_17148 : decode_any W_17148 = Some (OpImm ALU_ADD 10 10 563, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1714c : bv 32 := 0x9ac58593.
Lemma F_1714c : fetch_word Plain.M.loaded_segments (0x171a4 : word) = Some W_1714c.
Proof. vm_refl. Qed.
Lemma D_1714c : decode_any W_1714c = Some (OpImm ALU_ADD 11 11 2476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17150 : bv 32 := 0x00100613.
Lemma F_17150 : fetch_word Plain.M.loaded_segments (0x171a8 : word) = Some W_17150.
Proof. vm_refl. Qed.
Lemma D_17150 : decode_any W_17150 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17154 : bv 32 := 0x02813083.
Lemma F_17154 : fetch_word Plain.M.loaded_segments (0x171ac : word) = Some W_17154.
Proof. vm_refl. Qed.
Lemma D_17154 : decode_any W_17154 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17158 : bv 32 := 0x02013403.
Lemma F_17158 : fetch_word Plain.M.loaded_segments (0x171b0 : word) = Some W_17158.
Proof. vm_refl. Qed.
Lemma D_17158 : decode_any W_17158 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1715c : bv 32 := 0x01813483.
Lemma F_1715c : fetch_word Plain.M.loaded_segments (0x171b4 : word) = Some W_1715c.
Proof. vm_refl. Qed.
Lemma D_1715c : decode_any W_1715c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17160 : bv 32 := 0x03010113.
Lemma F_17160 : fetch_word Plain.M.loaded_segments (0x171b8 : word) = Some W_17160.
Proof. vm_refl. Qed.
Lemma D_17160 : decode_any W_17160 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17164 : bv 32 := 0x9ecfe06f.
Lemma F_17164 : fetch_word Plain.M.loaded_segments (0x171bc : word) = Some W_17164.
Proof. vm_refl. Qed.
Lemma D_17164 : decode_any W_17164 = Some (Jal 0 2089452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17168 : bv 32 := 0x00015517.
Lemma F_17168 : fetch_word Plain.M.loaded_segments (0x171c0 : word) = Some W_17168.
Proof. vm_refl. Qed.
Lemma D_17168 : decode_any W_17168 = Some (Auipc 10 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1716c : bv 32 := 0x5c053503.
Lemma F_1716c : fetch_word Plain.M.loaded_segments (0x171c4 : word) = Some W_1716c.
Proof. vm_refl. Qed.
Lemma D_1716c : decode_any W_1716c = Some (Load SZ8 true 10 10 1472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17170 : bv 32 := 0x00052503.
Lemma F_17170 : fetch_word Plain.M.loaded_segments (0x171c8 : word) = Some W_17170.
Proof. vm_refl. Qed.
Lemma D_17170 : decode_any W_17170 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17174 : bv 32 := 0x00500593.
Lemma F_17174 : fetch_word Plain.M.loaded_segments (0x171cc : word) = Some W_17174.
Proof. vm_refl. Qed.
Lemma D_17174 : decode_any W_17174 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17178 : bv 32 := 0x02a5c063.
Lemma F_17178 : fetch_word Plain.M.loaded_segments (0x171d0 : word) = Some W_17178.
Proof. vm_refl. Qed.
Lemma D_17178 : decode_any W_17178 = Some (Branch BC_LT 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1717c : bv 32 := 0xffffa517.
Lemma F_1717c : fetch_word Plain.M.loaded_segments (0x171d4 : word) = Some W_1717c.
Proof. vm_refl. Qed.
Lemma D_1717c : decode_any W_1717c = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17180 : bv 32 := 0xffffa597.
Lemma F_17180 : fetch_word Plain.M.loaded_segments (0x171d8 : word) = Some W_17180.
Proof. vm_refl. Qed.
Lemma D_17180 : decode_any W_17180 = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17184 : bv 32 := 0xde350513.
Lemma F_17184 : fetch_word Plain.M.loaded_segments (0x171dc : word) = Some W_17184.
Proof. vm_refl. Qed.
Lemma D_17184 : decode_any W_17184 = Some (OpImm ALU_ADD 10 10 3555, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17188 : bv 32 := 0x97058593.
Lemma F_17188 : fetch_word Plain.M.loaded_segments (0x171e0 : word) = Some W_17188.
Proof. vm_refl. Qed.
Lemma D_17188 : decode_any W_17188 = Some (OpImm ALU_ADD 11 11 2416, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1718c : bv 32 := 0x00100613.
Lemma F_1718c : fetch_word Plain.M.loaded_segments (0x171e4 : word) = Some W_1718c.
Proof. vm_refl. Qed.
Lemma D_1718c : decode_any W_1718c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17190 : bv 32 := 0x9c0fe0ef.
Lemma F_17190 : fetch_word Plain.M.loaded_segments (0x171e8 : word) = Some W_17190.
Proof. vm_refl. Qed.
Lemma D_17190 : decode_any W_17190 = Some (Jal 1 2089408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17194 : bv 32 := 0x0080006f.
Lemma F_17194 : fetch_word Plain.M.loaded_segments (0x171ec : word) = Some W_17194.
Proof. vm_refl. Qed.
Lemma D_17194 : decode_any W_17194 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17198 : bv 32 := 0x00100513.
Lemma F_17198 : fetch_word Plain.M.loaded_segments (0x171f0 : word) = Some W_17198.
Proof. vm_refl. Qed.
Lemma D_17198 : decode_any W_17198 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1719c : bv 32 := 0x02813083.
Lemma F_1719c : fetch_word Plain.M.loaded_segments (0x171f4 : word) = Some W_1719c.
Proof. vm_refl. Qed.
Lemma D_1719c : decode_any W_1719c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171a0 : bv 32 := 0x02013403.
Lemma F_171a0 : fetch_word Plain.M.loaded_segments (0x171f8 : word) = Some W_171a0.
Proof. vm_refl. Qed.
Lemma D_171a0 : decode_any W_171a0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171a4 : bv 32 := 0x01813483.
Lemma F_171a4 : fetch_word Plain.M.loaded_segments (0x171fc : word) = Some W_171a4.
Proof. vm_refl. Qed.
Lemma D_171a4 : decode_any W_171a4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171a8 : bv 32 := 0x03010113.
Lemma F_171a8 : fetch_word Plain.M.loaded_segments (0x17200 : word) = Some W_171a8.
Proof. vm_refl. Qed.
Lemma D_171a8 : decode_any W_171a8 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171ac : bv 32 := 0x00008067.
Lemma F_171ac : fetch_word Plain.M.loaded_segments (0x17204 : word) = Some W_171ac.
Proof. vm_refl. Qed.
Lemma D_171ac : decode_any W_171ac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

