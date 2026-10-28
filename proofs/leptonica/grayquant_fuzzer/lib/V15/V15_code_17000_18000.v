(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.H Require GcFlushU15.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_17080 : bv 32 := 0xfe010113.
Lemma F_17080 : fetch_word Ubsan.M.loaded_segments (0x17184 : word) = Some W_17080.
Proof. vm_refl. Qed.
Lemma D_17080 : decode_any W_17080 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17084 : bv 32 := 0x00113c23.
Lemma F_17084 : fetch_word Ubsan.M.loaded_segments (0x17188 : word) = Some W_17084.
Proof. vm_refl. Qed.
Lemma D_17084 : decode_any W_17084 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17088 : bv 32 := 0x00813823.
Lemma F_17088 : fetch_word Ubsan.M.loaded_segments (0x1718c : word) = Some W_17088.
Proof. vm_refl. Qed.
Lemma D_17088 : decode_any W_17088 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1708c : bv 32 := 0x00913423.
Lemma F_1708c : fetch_word Ubsan.M.loaded_segments (0x17190 : word) = Some W_1708c.
Proof. vm_refl. Qed.
Lemma D_1708c : decode_any W_1708c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17090 : bv 32 := 0x01213023.
Lemma F_17090 : fetch_word Ubsan.M.loaded_segments (0x17194 : word) = Some W_17090.
Proof. vm_refl. Qed.
Lemma D_17090 : decode_any W_17090 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17094 : bv 32 := 0x04050263.
Lemma F_17094 : fetch_word Ubsan.M.loaded_segments (0x17198 : word) = Some W_17094.
Proof. vm_refl. Qed.
Lemma D_17094 : decode_any W_17094 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17098 : bv 32 := 0x00050493.
Lemma F_17098 : fetch_word Ubsan.M.loaded_segments (0x1719c : word) = Some W_17098.
Proof. vm_refl. Qed.
Lemma D_17098 : decode_any W_17098 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1709c : bv 32 := 0x00757513.
Lemma F_1709c : fetch_word Ubsan.M.loaded_segments (0x171a0 : word) = Some W_1709c.
Proof. vm_refl. Qed.
Lemma D_1709c : decode_any W_1709c = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170a0 : bv 32 := 0x12051c63.
Lemma F_170a0 : fetch_word Ubsan.M.loaded_segments (0x171a4 : word) = Some W_170a0.
Proof. vm_refl. Qed.
Lemma D_170a0 : decode_any W_170a0 = Some (Branch BC_NE 10 0 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170a4 : bv 32 := 0x0004a503.
Lemma F_170a4 : fetch_word Ubsan.M.loaded_segments (0x171a8 : word) = Some W_170a4.
Proof. vm_refl. Qed.
Lemma D_170a4 : decode_any W_170a4 = Some (Load SZ4 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170a8 : bv 32 := 0x0044a583.
Lemma F_170a8 : fetch_word Ubsan.M.loaded_segments (0x171ac : word) = Some W_170a8.
Proof. vm_refl. Qed.
Lemma D_170a8 : decode_any W_170a8 = Some (Load SZ4 true 11 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170ac : bv 32 := 0x0084a603.
Lemma F_170ac : fetch_word Ubsan.M.loaded_segments (0x171b0 : word) = Some W_170ac.
Proof. vm_refl. Qed.
Lemma D_170ac : decode_any W_170ac = Some (Load SZ4 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170b0 : bv 32 := 0xa39ff0ef.
Lemma F_170b0 : fetch_word Ubsan.M.loaded_segments (0x171b4 : word) = Some W_170b0.
Proof. vm_refl. Qed.
Lemma D_170b0 : decode_any W_170b0 = Some (Jal 1 2095672, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170b4 : bv 32 := 0x04050663.
Lemma F_170b4 : fetch_word Ubsan.M.loaded_segments (0x171b8 : word) = Some W_170b4.
Proof. vm_refl. Qed.
Lemma D_170b4 : decode_any W_170b4 = Some (Branch BC_EQ 10 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170b8 : bv 32 := 0x00050413.
Lemma F_170b8 : fetch_word Ubsan.M.loaded_segments (0x171bc : word) = Some W_170b8.
Proof. vm_refl. Qed.
Lemma D_170b8 : decode_any W_170b8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170bc : bv 32 := 0x08a48663.
Lemma F_170bc : fetch_word Ubsan.M.loaded_segments (0x171c0 : word) = Some W_170bc.
Proof. vm_refl. Qed.
Lemma D_170bc : decode_any W_170bc = Some (Branch BC_EQ 9 10 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170c0 : bv 32 := 0x00c4a503.
Lemma F_170c0 : fetch_word Ubsan.M.loaded_segments (0x171c4 : word) = Some W_170c0.
Proof. vm_refl. Qed.
Lemma D_170c0 : decode_any W_170c0 = Some (Load SZ4 true 10 9 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170c4 : bv 32 := 0x00747913.
Lemma F_170c4 : fetch_word Ubsan.M.loaded_segments (0x171c8 : word) = Some W_170c4.
Proof. vm_refl. Qed.
Lemma D_170c4 : decode_any W_170c4 = Some (OpImm ALU_AND 18 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170c8 : bv 32 := 0x08a05863.
Lemma F_170c8 : fetch_word Ubsan.M.loaded_segments (0x171cc : word) = Some W_170c8.
Proof. vm_refl. Qed.
Lemma D_170c8 : decode_any W_170c8 = Some (Branch BC_GE 0 10 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170cc : bv 32 := 0x10091663.
Lemma F_170cc : fetch_word Ubsan.M.loaded_segments (0x171d0 : word) = Some W_170cc.
Proof. vm_refl. Qed.
Lemma D_170cc : decode_any W_170cc = Some (Branch BC_NE 18 0 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170d0 : bv 32 := 0x00a42623.
Lemma F_170d0 : fetch_word Ubsan.M.loaded_segments (0x171d4 : word) = Some W_170d0.
Proof. vm_refl. Qed.
Lemma D_170d0 : decode_any W_170d0 = Some (Store SZ4 8 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_170d4 : bv 32 := 0x0b00006f.
Lemma F_170d4 : fetch_word Ubsan.M.loaded_segments (0x171d8 : word) = Some W_170d4.
Proof. vm_refl. Qed.
Lemma D_170d4 : decode_any W_170d4 = Some (Jal 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17100 : bv 32 := 0x0001d517.
Lemma F_17100 : fetch_word Ubsan.M.loaded_segments (0x17204 : word) = Some W_17100.
Proof. vm_refl. Qed.
Lemma D_17100 : decode_any W_17100 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17104 : bv 32 := 0xff453503.
Lemma F_17104 : fetch_word Ubsan.M.loaded_segments (0x17208 : word) = Some W_17104.
Proof. vm_refl. Qed.
Lemma D_17104 : decode_any W_17104 = Some (Load SZ8 true 10 10 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17108 : bv 32 := 0x00052503.
Lemma F_17108 : fetch_word Ubsan.M.loaded_segments (0x1720c : word) = Some W_17108.
Proof. vm_refl. Qed.
Lemma D_17108 : decode_any W_17108 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1710c : bv 32 := 0x00500593.
Lemma F_1710c : fetch_word Ubsan.M.loaded_segments (0x17210 : word) = Some W_1710c.
Proof. vm_refl. Qed.
Lemma D_1710c : decode_any W_1710c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17110 : bv 32 := 0x02a5c863.
Lemma F_17110 : fetch_word Ubsan.M.loaded_segments (0x17214 : word) = Some W_17110.
Proof. vm_refl. Qed.
Lemma D_17110 : decode_any W_17110 = Some (Branch BC_LT 11 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17114 : bv 32 := 0xffff9517.
Lemma F_17114 : fetch_word Ubsan.M.loaded_segments (0x17218 : word) = Some W_17114.
Proof. vm_refl. Qed.
Lemma D_17114 : decode_any W_17114 = Some (Auipc 10 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17118 : bv 32 := 0xffffa597.
Lemma F_17118 : fetch_word Ubsan.M.loaded_segments (0x1721c : word) = Some W_17118.
Proof. vm_refl. Qed.
Lemma D_17118 : decode_any W_17118 = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1711c : bv 32 := 0x30750513.
Lemma F_1711c : fetch_word Ubsan.M.loaded_segments (0x17220 : word) = Some W_1711c.
Proof. vm_refl. Qed.
Lemma D_1711c : decode_any W_1711c = Some (OpImm ALU_ADD 10 10 775, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17120 : bv 32 := 0xee858593.
Lemma F_17120 : fetch_word Ubsan.M.loaded_segments (0x17224 : word) = Some W_17120.
Proof. vm_refl. Qed.
Lemma D_17120 : decode_any W_17120 = Some (OpImm ALU_ADD 11 11 3816, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17124 : bv 32 := 0x00000613.
Lemma F_17124 : fetch_word Ubsan.M.loaded_segments (0x17228 : word) = Some W_17124.
Proof. vm_refl. Qed.
Lemma D_17124 : decode_any W_17124 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17128 : bv 32 := 0x01813083.
Lemma F_17128 : fetch_word Ubsan.M.loaded_segments (0x1722c : word) = Some W_17128.
Proof. vm_refl. Qed.
Lemma D_17128 : decode_any W_17128 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1712c : bv 32 := 0x01013403.
Lemma F_1712c : fetch_word Ubsan.M.loaded_segments (0x17230 : word) = Some W_1712c.
Proof. vm_refl. Qed.
Lemma D_1712c : decode_any W_1712c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17130 : bv 32 := 0x00813483.
Lemma F_17130 : fetch_word Ubsan.M.loaded_segments (0x17234 : word) = Some W_17130.
Proof. vm_refl. Qed.
Lemma D_17130 : decode_any W_17130 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17134 : bv 32 := 0x00013903.
Lemma F_17134 : fetch_word Ubsan.M.loaded_segments (0x17238 : word) = Some W_17134.
Proof. vm_refl. Qed.
Lemma D_17134 : decode_any W_17134 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17138 : bv 32 := 0x02010113.
Lemma F_17138 : fetch_word Ubsan.M.loaded_segments (0x1723c : word) = Some W_17138.
Proof. vm_refl. Qed.
Lemma D_17138 : decode_any W_17138 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1713c : bv 32 := 0xb7cfe06f.
Lemma F_1713c : fetch_word Ubsan.M.loaded_segments (0x17240 : word) = Some W_1713c.
Proof. vm_refl. Qed.
Lemma D_1713c : decode_any W_1713c = Some (Jal 0 2089852, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17184 : bv 32 := 0x04091a63.
Lemma F_17184 : fetch_word Ubsan.M.loaded_segments (0x17288 : word) = Some W_17184.
Proof. vm_refl. Qed.
Lemma D_17184 : decode_any W_17184 = Some (Branch BC_NE 18 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17188 : bv 32 := 0x0184b503.
Lemma F_17188 : fetch_word Ubsan.M.loaded_segments (0x1728c : word) = Some W_17188.
Proof. vm_refl. Qed.
Lemma D_17188 : decode_any W_17188 = Some (Load SZ8 true 10 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1718c : bv 32 := 0x00a43c23.
Lemma F_1718c : fetch_word Ubsan.M.loaded_segments (0x17290 : word) = Some W_1718c.
Proof. vm_refl. Qed.
Lemma D_1718c : decode_any W_1718c = Some (Store SZ8 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17190 : bv 32 := 0x00040513.
Lemma F_17190 : fetch_word Ubsan.M.loaded_segments (0x17294 : word) = Some W_17190.
Proof. vm_refl. Qed.
Lemma D_17190 : decode_any W_17190 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17194 : bv 32 := 0x00048593.
Lemma F_17194 : fetch_word Ubsan.M.loaded_segments (0x17298 : word) = Some W_17194.
Proof. vm_refl. Qed.
Lemma D_17194 : decode_any W_17194 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17198 : bv 32 := 0x190000ef.
Lemma F_17198 : fetch_word Ubsan.M.loaded_segments (0x1729c : word) = Some W_17198.
Proof. vm_refl. Qed.
Lemma D_17198 : decode_any W_17198 = Some (Jal 1 400, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1719c : bv 32 := 0x0284b583.
Lemma F_1719c : fetch_word Ubsan.M.loaded_segments (0x172a0 : word) = Some W_1719c.
Proof. vm_refl. Qed.
Lemma D_1719c : decode_any W_1719c = Some (Load SZ8 true 11 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171a0 : bv 32 := 0x02840513.
Lemma F_171a0 : fetch_word Ubsan.M.loaded_segments (0x172a4 : word) = Some W_171a0.
Proof. vm_refl. Qed.
Lemma D_171a0 : decode_any W_171a0 = Some (OpImm ALU_ADD 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171a4 : bv 32 := 0xcb4fe0ef.
Lemma F_171a4 : fetch_word Ubsan.M.loaded_segments (0x172a8 : word) = Some W_171a4.
Proof. vm_refl. Qed.
Lemma D_171a4 : decode_any W_171a4 = Some (Jal 1 2090164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171a8 : bv 32 := 0x0204a503.
Lemma F_171a8 : fetch_word Ubsan.M.loaded_segments (0x172ac : word) = Some W_171a8.
Proof. vm_refl. Qed.
Lemma D_171a8 : decode_any W_171a8 = Some (Load SZ4 true 10 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171ac : bv 32 := 0x02a42023.
Lemma F_171ac : fetch_word Ubsan.M.loaded_segments (0x172b0 : word) = Some W_171ac.
Proof. vm_refl. Qed.
Lemma D_171ac : decode_any W_171ac = Some (Store SZ4 8 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171b0 : bv 32 := 0x00040513.
Lemma F_171b0 : fetch_word Ubsan.M.loaded_segments (0x172b4 : word) = Some W_171b0.
Proof. vm_refl. Qed.
Lemma D_171b0 : decode_any W_171b0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171b4 : bv 32 := 0x00000593.
Lemma F_171b4 : fetch_word Ubsan.M.loaded_segments (0x172b8 : word) = Some W_171b4.
Proof. vm_refl. Qed.
Lemma D_171b4 : decode_any W_171b4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171b8 : bv 32 := 0x6f1000ef.
Lemma F_171b8 : fetch_word Ubsan.M.loaded_segments (0x172bc : word) = Some W_171b8.
Proof. vm_refl. Qed.
Lemma D_171b8 : decode_any W_171b8 = Some (Jal 1 3824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171bc : bv 32 := 0x00040513.
Lemma F_171bc : fetch_word Ubsan.M.loaded_segments (0x172c0 : word) = Some W_171bc.
Proof. vm_refl. Qed.
Lemma D_171bc : decode_any W_171bc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171c0 : bv 32 := 0x01813083.
Lemma F_171c0 : fetch_word Ubsan.M.loaded_segments (0x172c4 : word) = Some W_171c0.
Proof. vm_refl. Qed.
Lemma D_171c0 : decode_any W_171c0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171c4 : bv 32 := 0x01013403.
Lemma F_171c4 : fetch_word Ubsan.M.loaded_segments (0x172c8 : word) = Some W_171c4.
Proof. vm_refl. Qed.
Lemma D_171c4 : decode_any W_171c4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171c8 : bv 32 := 0x00813483.
Lemma F_171c8 : fetch_word Ubsan.M.loaded_segments (0x172cc : word) = Some W_171c8.
Proof. vm_refl. Qed.
Lemma D_171c8 : decode_any W_171c8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171cc : bv 32 := 0x00013903.
Lemma F_171cc : fetch_word Ubsan.M.loaded_segments (0x172d0 : word) = Some W_171cc.
Proof. vm_refl. Qed.
Lemma D_171cc : decode_any W_171cc = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171d0 : bv 32 := 0x02010113.
Lemma F_171d0 : fetch_word Ubsan.M.loaded_segments (0x172d4 : word) = Some W_171d0.
Proof. vm_refl. Qed.
Lemma D_171d0 : decode_any W_171d0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171d4 : bv 32 := 0x00008067.
Lemma F_171d4 : fetch_word Ubsan.M.loaded_segments (0x172d8 : word) = Some W_171d4.
Proof. vm_refl. Qed.
Lemma D_171d4 : decode_any W_171d4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171dc : bv 32 := 0x0035f713.
Lemma F_171dc : fetch_word Ubsan.M.loaded_segments (0x172e0 : word) = Some W_171dc.
Proof. vm_refl. Qed.
Lemma D_171dc : decode_any W_171dc = Some (OpImm ALU_AND 14 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171e0 : bv 32 := 0x00058663.
Lemma F_171e0 : fetch_word Ubsan.M.loaded_segments (0x172e4 : word) = Some W_171e0.
Proof. vm_refl. Qed.
Lemma D_171e0 : decode_any W_171e0 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171e4 : bv 32 := 0x0a071863.
Lemma F_171e4 : fetch_word Ubsan.M.loaded_segments (0x172e8 : word) = Some W_171e4.
Proof. vm_refl. Qed.
Lemma D_171e4 : decode_any W_171e4 = Some (Branch BC_NE 14 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171e8 : bv 32 := 0x0005a023.
Lemma F_171e8 : fetch_word Ubsan.M.loaded_segments (0x172ec : word) = Some W_171e8.
Proof. vm_refl. Qed.
Lemma D_171e8 : decode_any W_171e8 = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171ec : bv 32 := 0x00367793.
Lemma F_171ec : fetch_word Ubsan.M.loaded_segments (0x172f0 : word) = Some W_171ec.
Proof. vm_refl. Qed.
Lemma D_171ec : decode_any W_171ec = Some (OpImm ALU_AND 15 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171f0 : bv 32 := 0x00060663.
Lemma F_171f0 : fetch_word Ubsan.M.loaded_segments (0x172f4 : word) = Some W_171f0.
Proof. vm_refl. Qed.
Lemma D_171f0 : decode_any W_171f0 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171f4 : bv 32 := 0x0a079063.
Lemma F_171f4 : fetch_word Ubsan.M.loaded_segments (0x172f8 : word) = Some W_171f4.
Proof. vm_refl. Qed.
Lemma D_171f4 : decode_any W_171f4 = Some (Branch BC_NE 15 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171f8 : bv 32 := 0x00062023.
Lemma F_171f8 : fetch_word Ubsan.M.loaded_segments (0x172fc : word) = Some W_171f8.
Proof. vm_refl. Qed.
Lemma D_171f8 : decode_any W_171f8 = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171fc : bv 32 := 0x0036f813.
Lemma F_171fc : fetch_word Ubsan.M.loaded_segments (0x17300 : word) = Some W_171fc.
Proof. vm_refl. Qed.
Lemma D_171fc : decode_any W_171fc = Some (OpImm ALU_AND 16 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17200 : bv 32 := 0x00068663.
Lemma F_17200 : fetch_word Ubsan.M.loaded_segments (0x17304 : word) = Some W_17200.
Proof. vm_refl. Qed.
Lemma D_17200 : decode_any W_17200 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17204 : bv 32 := 0x08081863.
Lemma F_17204 : fetch_word Ubsan.M.loaded_segments (0x17308 : word) = Some W_17204.
Proof. vm_refl. Qed.
Lemma D_17204 : decode_any W_17204 = Some (Branch BC_NE 16 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17208 : bv 32 := 0x0006a023.
Lemma F_17208 : fetch_word Ubsan.M.loaded_segments (0x1730c : word) = Some W_17208.
Proof. vm_refl. Qed.
Lemma D_17208 : decode_any W_17208 = Some (Store SZ4 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1720c : bv 32 := 0x04050663.
Lemma F_1720c : fetch_word Ubsan.M.loaded_segments (0x17310 : word) = Some W_1720c.
Proof. vm_refl. Qed.
Lemma D_1720c : decode_any W_1720c = Some (Branch BC_EQ 10 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17210 : bv 32 := 0x00757893.
Lemma F_17210 : fetch_word Ubsan.M.loaded_segments (0x17314 : word) = Some W_17210.
Proof. vm_refl. Qed.
Lemma D_17210 : decode_any W_17210 = Some (OpImm ALU_AND 17 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17214 : bv 32 := 0x00058a63.
Lemma F_17214 : fetch_word Ubsan.M.loaded_segments (0x17318 : word) = Some W_17214.
Proof. vm_refl. Qed.
Lemma D_17214 : decode_any W_17214 = Some (Branch BC_EQ 11 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17218 : bv 32 := 0x00e8e733.
Lemma F_17218 : fetch_word Ubsan.M.loaded_segments (0x1731c : word) = Some W_17218.
Proof. vm_refl. Qed.
Lemma D_17218 : decode_any W_17218 = Some (Op ALU_OR 14 17 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1721c : bv 32 := 0x06071c63.
Lemma F_1721c : fetch_word Ubsan.M.loaded_segments (0x17320 : word) = Some W_1721c.
Proof. vm_refl. Qed.
Lemma D_1721c : decode_any W_1721c = Some (Branch BC_NE 14 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17220 : bv 32 := 0x00052703.
Lemma F_17220 : fetch_word Ubsan.M.loaded_segments (0x17324 : word) = Some W_17220.
Proof. vm_refl. Qed.
Lemma D_17220 : decode_any W_17220 = Some (Load SZ4 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17224 : bv 32 := 0x00e5a023.
Lemma F_17224 : fetch_word Ubsan.M.loaded_segments (0x17328 : word) = Some W_17224.
Proof. vm_refl. Qed.
Lemma D_17224 : decode_any W_17224 = Some (Store SZ4 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17228 : bv 32 := 0x00060a63.
Lemma F_17228 : fetch_word Ubsan.M.loaded_segments (0x1732c : word) = Some W_17228.
Proof. vm_refl. Qed.
Lemma D_17228 : decode_any W_17228 = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1722c : bv 32 := 0x00f8e5b3.
Lemma F_1722c : fetch_word Ubsan.M.loaded_segments (0x17330 : word) = Some W_1722c.
Proof. vm_refl. Qed.
Lemma D_1722c : decode_any W_1722c = Some (Op ALU_OR 11 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17230 : bv 32 := 0x06059263.
Lemma F_17230 : fetch_word Ubsan.M.loaded_segments (0x17334 : word) = Some W_17230.
Proof. vm_refl. Qed.
Lemma D_17230 : decode_any W_17230 = Some (Branch BC_NE 11 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17234 : bv 32 := 0x00452583.
Lemma F_17234 : fetch_word Ubsan.M.loaded_segments (0x17338 : word) = Some W_17234.
Proof. vm_refl. Qed.
Lemma D_17234 : decode_any W_17234 = Some (Load SZ4 true 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17238 : bv 32 := 0x00b62023.
Lemma F_17238 : fetch_word Ubsan.M.loaded_segments (0x1733c : word) = Some W_17238.
Proof. vm_refl. Qed.
Lemma D_17238 : decode_any W_17238 = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1723c : bv 32 := 0x04068463.
Lemma F_1723c : fetch_word Ubsan.M.loaded_segments (0x17340 : word) = Some W_1723c.
Proof. vm_refl. Qed.
Lemma D_1723c : decode_any W_1723c = Some (Branch BC_EQ 13 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17240 : bv 32 := 0x0108e5b3.
Lemma F_17240 : fetch_word Ubsan.M.loaded_segments (0x17344 : word) = Some W_17240.
Proof. vm_refl. Qed.
Lemma D_17240 : decode_any W_17240 = Some (Op ALU_OR 11 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17244 : bv 32 := 0x04059863.
Lemma F_17244 : fetch_word Ubsan.M.loaded_segments (0x17348 : word) = Some W_17244.
Proof. vm_refl. Qed.
Lemma D_17244 : decode_any W_17244 = Some (Branch BC_NE 11 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17248 : bv 32 := 0x00852503.
Lemma F_17248 : fetch_word Ubsan.M.loaded_segments (0x1734c : word) = Some W_17248.
Proof. vm_refl. Qed.
Lemma D_17248 : decode_any W_17248 = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1724c : bv 32 := 0x00a6a023.
Lemma F_1724c : fetch_word Ubsan.M.loaded_segments (0x17350 : word) = Some W_1724c.
Proof. vm_refl. Qed.
Lemma D_1724c : decode_any W_1724c = Some (Store SZ4 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17250 : bv 32 := 0x00058513.
Lemma F_17250 : fetch_word Ubsan.M.loaded_segments (0x17354 : word) = Some W_17250.
Proof. vm_refl. Qed.
Lemma D_17250 : decode_any W_17250 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17254 : bv 32 := 0x00008067.
Lemma F_17254 : fetch_word Ubsan.M.loaded_segments (0x17358 : word) = Some W_17254.
Proof. vm_refl. Qed.
Lemma D_17254 : decode_any W_17254 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17328 : bv 32 := 0xfd010113.
Lemma F_17328 : fetch_word Ubsan.M.loaded_segments (0x1742c : word) = Some W_17328.
Proof. vm_refl. Qed.
Lemma D_17328 : decode_any W_17328 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1732c : bv 32 := 0x02113423.
Lemma F_1732c : fetch_word Ubsan.M.loaded_segments (0x17430 : word) = Some W_1732c.
Proof. vm_refl. Qed.
Lemma D_1732c : decode_any W_1732c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17330 : bv 32 := 0x02813023.
Lemma F_17330 : fetch_word Ubsan.M.loaded_segments (0x17434 : word) = Some W_17330.
Proof. vm_refl. Qed.
Lemma D_17330 : decode_any W_17330 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17334 : bv 32 := 0x00913c23.
Lemma F_17334 : fetch_word Ubsan.M.loaded_segments (0x17438 : word) = Some W_17334.
Proof. vm_refl. Qed.
Lemma D_17334 : decode_any W_17334 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17338 : bv 32 := 0x0e058863.
Lemma F_17338 : fetch_word Ubsan.M.loaded_segments (0x1743c : word) = Some W_17338.
Proof. vm_refl. Qed.
Lemma D_17338 : decode_any W_17338 = Some (Branch BC_EQ 11 0 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1733c : bv 32 := 0x10050a63.
Lemma F_1733c : fetch_word Ubsan.M.loaded_segments (0x17440 : word) = Some W_1733c.
Proof. vm_refl. Qed.
Lemma D_1733c : decode_any W_1733c = Some (Branch BC_EQ 10 0 276, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17340 : bv 32 := 0x0ea58063.
Lemma F_17340 : fetch_word Ubsan.M.loaded_segments (0x17444 : word) = Some W_17340.
Proof. vm_refl. Qed.
Lemma D_17340 : decode_any W_17340 = Some (Branch BC_EQ 11 10 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17344 : bv 32 := 0x0075f613.
Lemma F_17344 : fetch_word Ubsan.M.loaded_segments (0x17448 : word) = Some W_17344.
Proof. vm_refl. Qed.
Lemma D_17344 : decode_any W_17344 = Some (OpImm ALU_AND 12 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17348 : bv 32 := 0x1c061e63.
Lemma F_17348 : fetch_word Ubsan.M.loaded_segments (0x1744c : word) = Some W_17348.
Proof. vm_refl. Qed.
Lemma D_17348 : decode_any W_17348 = Some (Branch BC_NE 12 0 476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1734c : bv 32 := 0x00757613.
Lemma F_1734c : fetch_word Ubsan.M.loaded_segments (0x17450 : word) = Some W_1734c.
Proof. vm_refl. Qed.
Lemma D_1734c : decode_any W_1734c = Some (OpImm ALU_AND 12 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17350 : bv 32 := 0x1c061a63.
Lemma F_17350 : fetch_word Ubsan.M.loaded_segments (0x17454 : word) = Some W_17350.
Proof. vm_refl. Qed.
Lemma D_17350 : decode_any W_17350 = Some (Branch BC_NE 12 0 468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17354 : bv 32 := 0x0085a603.
Lemma F_17354 : fetch_word Ubsan.M.loaded_segments (0x17458 : word) = Some W_17354.
Proof. vm_refl. Qed.
Lemma D_17354 : decode_any W_17354 = Some (Load SZ4 true 12 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17358 : bv 32 := 0x00852683.
Lemma F_17358 : fetch_word Ubsan.M.loaded_segments (0x1745c : word) = Some W_17358.
Proof. vm_refl. Qed.
Lemma D_17358 : decode_any W_17358 = Some (Load SZ4 true 13 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1735c : bv 32 := 0x10d61e63.
Lemma F_1735c : fetch_word Ubsan.M.loaded_segments (0x17460 : word) = Some W_1735c.
Proof. vm_refl. Qed.
Lemma D_1735c : decode_any W_1735c = Some (Branch BC_NE 12 13 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17360 : bv 32 := 0x03053603.
Lemma F_17360 : fetch_word Ubsan.M.loaded_segments (0x17464 : word) = Some W_17360.
Proof. vm_refl. Qed.
Lemma D_17360 : decode_any W_17360 = Some (Load SZ8 true 12 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17364 : bv 32 := 0x00c13823.
Lemma F_17364 : fetch_word Ubsan.M.loaded_segments (0x17468 : word) = Some W_17364.
Proof. vm_refl. Qed.
Lemma D_17364 : decode_any W_17364 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17368 : bv 32 := 0x02060063.
Lemma F_17368 : fetch_word Ubsan.M.loaded_segments (0x1746c : word) = Some W_17368.
Proof. vm_refl. Qed.
Lemma D_17368 : decode_any W_17368 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17388 : bv 32 := 0x0305b403.
Lemma F_17388 : fetch_word Ubsan.M.loaded_segments (0x1748c : word) = Some W_17388.
Proof. vm_refl. Qed.
Lemma D_17388 : decode_any W_17388 = Some (Load SZ8 true 8 11 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1738c : bv 32 := 0x08040a63.
Lemma F_1738c : fetch_word Ubsan.M.loaded_segments (0x17490 : word) = Some W_1738c.
Proof. vm_refl. Qed.
Lemma D_1738c : decode_any W_1738c = Some (Branch BC_EQ 8 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17390 : bv 32 := 0x00050493.
Lemma F_17390 : fetch_word Ubsan.M.loaded_segments (0x17494 : word) = Some W_17390.
Proof. vm_refl. Qed.
Lemma D_17390 : decode_any W_17390 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17394 : bv 32 := 0x00c10613.
Lemma F_17394 : fetch_word Ubsan.M.loaded_segments (0x17498 : word) = Some W_17394.
Proof. vm_refl. Qed.
Lemma D_17394 : decode_any W_17394 = Some (OpImm ALU_ADD 12 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17398 : bv 32 := 0x00040513.
Lemma F_17398 : fetch_word Ubsan.M.loaded_segments (0x1749c : word) = Some W_17398.
Proof. vm_refl. Qed.
Lemma D_17398 : decode_any W_17398 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1739c : bv 32 := 0x00000593.
Lemma F_1739c : fetch_word Ubsan.M.loaded_segments (0x174a0 : word) = Some W_1739c.
Proof. vm_refl. Qed.
Lemma D_1739c : decode_any W_1739c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_173a0 : bv 32 := 0x3e4010ef.
Lemma F_173a0 : fetch_word Ubsan.M.loaded_segments (0x174a4 : word) = Some W_173a0.
Proof. vm_refl. Qed.
Lemma D_173a0 : decode_any W_173a0 = Some (Jal 1 5092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_173a4 : bv 32 := 0x00c12503.
Lemma F_173a4 : fetch_word Ubsan.M.loaded_segments (0x174a8 : word) = Some W_173a4.
Proof. vm_refl. Qed.
Lemma D_173a4 : decode_any W_173a4 = Some (Load SZ4 true 10 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_173a8 : bv 32 := 0x10050663.
Lemma F_173a8 : fetch_word Ubsan.M.loaded_segments (0x174ac : word) = Some W_173a8.
Proof. vm_refl. Qed.
Lemma D_173a8 : decode_any W_173a8 = Some (Branch BC_EQ 10 0 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_173ac : bv 32 := 0x00040513.
Lemma F_173ac : fetch_word Ubsan.M.loaded_segments (0x174b0 : word) = Some W_173ac.
Proof. vm_refl. Qed.
Lemma D_173ac : decode_any W_173ac = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_173b0 : bv 32 := 0x2bc010ef.
Lemma F_173b0 : fetch_word Ubsan.M.loaded_segments (0x174b4 : word) = Some W_173b0.
Proof. vm_refl. Qed.
Lemma D_173b0 : decode_any W_173b0 = Some (Jal 1 4796, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_173b4 : bv 32 := 0x12050463.
Lemma F_173b4 : fetch_word Ubsan.M.loaded_segments (0x174b8 : word) = Some W_173b4.
Proof. vm_refl. Qed.
Lemma D_173b4 : decode_any W_173b4 = Some (Branch BC_EQ 10 0 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_173b8 : bv 32 := 0x00048593.
Lemma F_173b8 : fetch_word Ubsan.M.loaded_segments (0x174bc : word) = Some W_173b8.
Proof. vm_refl. Qed.
Lemma D_173b8 : decode_any W_173b8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_173bc : bv 32 := 0x0304b603.
Lemma F_173bc : fetch_word Ubsan.M.loaded_segments (0x174c0 : word) = Some W_173bc.
Proof. vm_refl. Qed.
Lemma D_173bc : decode_any W_173bc = Some (Load SZ8 true 12 9 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_173c0 : bv 32 := 0x00c13823.
Lemma F_173c0 : fetch_word Ubsan.M.loaded_segments (0x174c4 : word) = Some W_173c0.
Proof. vm_refl. Qed.
Lemma D_173c0 : decode_any W_173c0 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_173c4 : bv 32 := 0x00060c63.
Lemma F_173c4 : fetch_word Ubsan.M.loaded_segments (0x174c8 : word) = Some W_173c4.
Proof. vm_refl. Qed.
Lemma D_173c4 : decode_any W_173c4 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_173dc : bv 32 := 0x02a5b823.
Lemma F_173dc : fetch_word Ubsan.M.loaded_segments (0x174e0 : word) = Some W_173dc.
Proof. vm_refl. Qed.
Lemma D_173dc : decode_any W_173dc = Some (Store SZ8 11 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_173e0 : bv 32 := 0x01010613.
Lemma F_173e0 : fetch_word Ubsan.M.loaded_segments (0x174e4 : word) = Some W_173e0.
Proof. vm_refl. Qed.
Lemma D_173e0 : decode_any W_173e0 = Some (OpImm ALU_ADD 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_173e4 : bv 32 := 0x00000593.
Lemma F_173e4 : fetch_word Ubsan.M.loaded_segments (0x174e8 : word) = Some W_173e4.
Proof. vm_refl. Qed.
Lemma D_173e4 : decode_any W_173e4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_173e8 : bv 32 := 0x39c010ef.
Lemma F_173e8 : fetch_word Ubsan.M.loaded_segments (0x174ec : word) = Some W_173e8.
Proof. vm_refl. Qed.
Lemma D_173e8 : decode_any W_173e8 = Some (Jal 1 5020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_173ec : bv 32 := 0x01012503.
Lemma F_173ec : fetch_word Ubsan.M.loaded_segments (0x174f0 : word) = Some W_173ec.
Proof. vm_refl. Qed.
Lemma D_173ec : decode_any W_173ec = Some (Load SZ4 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_173f0 : bv 32 := 0x02051863.
Lemma F_173f0 : fetch_word Ubsan.M.loaded_segments (0x174f4 : word) = Some W_173f0.
Proof. vm_refl. Qed.
Lemma D_173f0 : decode_any W_173f0 = Some (Branch BC_NE 10 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17420 : bv 32 := 0x00000513.
Lemma F_17420 : fetch_word Ubsan.M.loaded_segments (0x17524 : word) = Some W_17420.
Proof. vm_refl. Qed.
Lemma D_17420 : decode_any W_17420 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17424 : bv 32 := 0x0ec0006f.
Lemma F_17424 : fetch_word Ubsan.M.loaded_segments (0x17528 : word) = Some W_17424.
Proof. vm_refl. Qed.
Lemma D_17424 : decode_any W_17424 = Some (Jal 0 236, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_174dc : bv 32 := 0x0001d517.
Lemma F_174dc : fetch_word Ubsan.M.loaded_segments (0x175e0 : word) = Some W_174dc.
Proof. vm_refl. Qed.
Lemma D_174dc : decode_any W_174dc = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_174e0 : bv 32 := 0xc1853503.
Lemma F_174e0 : fetch_word Ubsan.M.loaded_segments (0x175e4 : word) = Some W_174e0.
Proof. vm_refl. Qed.
Lemma D_174e0 : decode_any W_174e0 = Some (Load SZ8 true 10 10 3096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_174e4 : bv 32 := 0x00052503.
Lemma F_174e4 : fetch_word Ubsan.M.loaded_segments (0x175e8 : word) = Some W_174e4.
Proof. vm_refl. Qed.
Lemma D_174e4 : decode_any W_174e4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_174e8 : bv 32 := 0x00500593.
Lemma F_174e8 : fetch_word Ubsan.M.loaded_segments (0x175ec : word) = Some W_174e8.
Proof. vm_refl. Qed.
Lemma D_174e8 : decode_any W_174e8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_174ec : bv 32 := 0x02a5c063.
Lemma F_174ec : fetch_word Ubsan.M.loaded_segments (0x175f0 : word) = Some W_174ec.
Proof. vm_refl. Qed.
Lemma D_174ec : decode_any W_174ec = Some (Branch BC_LT 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_174f0 : bv 32 := 0xffff9517.
Lemma F_174f0 : fetch_word Ubsan.M.loaded_segments (0x175f4 : word) = Some W_174f0.
Proof. vm_refl. Qed.
Lemma D_174f0 : decode_any W_174f0 = Some (Auipc 10 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_174f4 : bv 32 := 0xffff9597.
Lemma F_174f4 : fetch_word Ubsan.M.loaded_segments (0x175f8 : word) = Some W_174f4.
Proof. vm_refl. Qed.
Lemma D_174f4 : decode_any W_174f4 = Some (Auipc 11 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_174f8 : bv 32 := 0xf3950513.
Lemma F_174f8 : fetch_word Ubsan.M.loaded_segments (0x175fc : word) = Some W_174f8.
Proof. vm_refl. Qed.
Lemma D_174f8 : decode_any W_174f8 = Some (OpImm ALU_ADD 10 10 3897, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_174fc : bv 32 := 0xff358593.
Lemma F_174fc : fetch_word Ubsan.M.loaded_segments (0x17600 : word) = Some W_174fc.
Proof. vm_refl. Qed.
Lemma D_174fc : decode_any W_174fc = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17500 : bv 32 := 0x00100613.
Lemma F_17500 : fetch_word Ubsan.M.loaded_segments (0x17604 : word) = Some W_17500.
Proof. vm_refl. Qed.
Lemma D_17500 : decode_any W_17500 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17504 : bv 32 := 0xee5fd0ef.
Lemma F_17504 : fetch_word Ubsan.M.loaded_segments (0x17608 : word) = Some W_17504.
Proof. vm_refl. Qed.
Lemma D_17504 : decode_any W_17504 = Some (Jal 1 2088676, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17508 : bv 32 := 0x0080006f.
Lemma F_17508 : fetch_word Ubsan.M.loaded_segments (0x1760c : word) = Some W_17508.
Proof. vm_refl. Qed.
Lemma D_17508 : decode_any W_17508 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17510 : bv 32 := 0x02813083.
Lemma F_17510 : fetch_word Ubsan.M.loaded_segments (0x17614 : word) = Some W_17510.
Proof. vm_refl. Qed.
Lemma D_17510 : decode_any W_17510 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17514 : bv 32 := 0x02013403.
Lemma F_17514 : fetch_word Ubsan.M.loaded_segments (0x17618 : word) = Some W_17514.
Proof. vm_refl. Qed.
Lemma D_17514 : decode_any W_17514 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17518 : bv 32 := 0x01813483.
Lemma F_17518 : fetch_word Ubsan.M.loaded_segments (0x1761c : word) = Some W_17518.
Proof. vm_refl. Qed.
Lemma D_17518 : decode_any W_17518 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1751c : bv 32 := 0x03010113.
Lemma F_1751c : fetch_word Ubsan.M.loaded_segments (0x17620 : word) = Some W_1751c.
Proof. vm_refl. Qed.
Lemma D_1751c : decode_any W_1751c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17520 : bv 32 := 0x00008067.
Lemma F_17520 : fetch_word Ubsan.M.loaded_segments (0x17624 : word) = Some W_17520.
Proof. vm_refl. Qed.
Lemma D_17520 : decode_any W_17520 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1790c : bv 32 := 0xfd010113.
Lemma F_1790c : fetch_word Ubsan.M.loaded_segments (0x17a10 : word) = Some W_1790c.
Proof. vm_refl. Qed.
Lemma D_1790c : decode_any W_1790c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17910 : bv 32 := 0x02113423.
Lemma F_17910 : fetch_word Ubsan.M.loaded_segments (0x17a14 : word) = Some W_17910.
Proof. vm_refl. Qed.
Lemma D_17910 : decode_any W_17910 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17914 : bv 32 := 0x02813023.
Lemma F_17914 : fetch_word Ubsan.M.loaded_segments (0x17a18 : word) = Some W_17914.
Proof. vm_refl. Qed.
Lemma D_17914 : decode_any W_17914 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17918 : bv 32 := 0x00913c23.
Lemma F_17918 : fetch_word Ubsan.M.loaded_segments (0x17a1c : word) = Some W_17918.
Proof. vm_refl. Qed.
Lemma D_17918 : decode_any W_17918 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1791c : bv 32 := 0x01213823.
Lemma F_1791c : fetch_word Ubsan.M.loaded_segments (0x17a20 : word) = Some W_1791c.
Proof. vm_refl. Qed.
Lemma D_1791c : decode_any W_1791c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17920 : bv 32 := 0x01313423.
Lemma F_17920 : fetch_word Ubsan.M.loaded_segments (0x17a24 : word) = Some W_17920.
Proof. vm_refl. Qed.
Lemma D_17920 : decode_any W_17920 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17924 : bv 32 := 0x00050413.
Lemma F_17924 : fetch_word Ubsan.M.loaded_segments (0x17a28 : word) = Some W_17924.
Proof. vm_refl. Qed.
Lemma D_17924 : decode_any W_17924 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17928 : bv 32 := 0x08058063.
Lemma F_17928 : fetch_word Ubsan.M.loaded_segments (0x17a2c : word) = Some W_17928.
Proof. vm_refl. Qed.
Lemma D_17928 : decode_any W_17928 = Some (Branch BC_EQ 11 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1792c : bv 32 := 0x00058493.
Lemma F_1792c : fetch_word Ubsan.M.loaded_segments (0x17a30 : word) = Some W_1792c.
Proof. vm_refl. Qed.
Lemma D_1792c : decode_any W_1792c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17930 : bv 32 := 0x1e858e63.
Lemma F_17930 : fetch_word Ubsan.M.loaded_segments (0x17a34 : word) = Some W_17930.
Proof. vm_refl. Qed.
Lemma D_17930 : decode_any W_17930 = Some (Branch BC_EQ 11 8 508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17934 : bv 32 := 0x0074f513.
Lemma F_17934 : fetch_word Ubsan.M.loaded_segments (0x17a38 : word) = Some W_17934.
Proof. vm_refl. Qed.
Lemma D_17934 : decode_any W_17934 = Some (OpImm ALU_AND 10 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17938 : bv 32 := 0x20051a63.
Lemma F_17938 : fetch_word Ubsan.M.loaded_segments (0x17a3c : word) = Some W_17938.
Proof. vm_refl. Qed.
Lemma D_17938 : decode_any W_17938 = Some (Branch BC_NE 10 0 532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1793c : bv 32 := 0x0104a503.
Lemma F_1793c : fetch_word Ubsan.M.loaded_segments (0x17a40 : word) = Some W_1793c.
Proof. vm_refl. Qed.
Lemma D_1793c : decode_any W_1793c = Some (Load SZ4 true 10 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17940 : bv 32 := 0x200005b7.
Lemma F_17940 : fetch_word Ubsan.M.loaded_segments (0x17a44 : word) = Some W_17940.
Proof. vm_refl. Qed.
Lemma D_17940 : decode_any W_17940 = Some (Lui 11 131072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17944 : bv 32 := 0x00b505b3.
Lemma F_17944 : fetch_word Ubsan.M.loaded_segments (0x17a48 : word) = Some W_17944.
Proof. vm_refl. Qed.
Lemma D_17944 : decode_any W_17944 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17948 : bv 32 := 0x01e5d59b.
Lemma F_17948 : fetch_word Ubsan.M.loaded_segments (0x17a4c : word) = Some W_17948.
Proof. vm_refl. Qed.
Lemma D_17948 : decode_any W_17948 = Some (ShiftImm32 ALU_SRL 11 11 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1794c : bv 32 := 0x20059063.
Lemma F_1794c : fetch_word Ubsan.M.loaded_segments (0x17a50 : word) = Some W_1794c.
Proof. vm_refl. Qed.
Lemma D_1794c : decode_any W_1794c = Some (Branch BC_NE 11 0 512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17950 : bv 32 := 0x0044a583.
Lemma F_17950 : fetch_word Ubsan.M.loaded_segments (0x17a54 : word) = Some W_17950.
Proof. vm_refl. Qed.
Lemma D_17950 : decode_any W_17950 = Some (Load SZ4 true 11 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17954 : bv 32 := 0x0025151b.
Lemma F_17954 : fetch_word Ubsan.M.loaded_segments (0x17a58 : word) = Some W_17954.
Proof. vm_refl. Qed.
Lemma D_17954 : decode_any W_17954 = Some (ShiftImm32 ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17958 : bv 32 := 0x02b50933.
Lemma F_17958 : fetch_word Ubsan.M.loaded_segments (0x17a5c : word) = Some W_17958.
Proof. vm_refl. Qed.
Lemma D_17958 : decode_any W_17958 = Some (Mul M_MUL 18 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1795c : bv 32 := 0x02b5053b.
Lemma F_1795c : fetch_word Ubsan.M.loaded_segments (0x17a60 : word) = Some W_1795c.
Proof. vm_refl. Qed.
Lemma D_1795c : decode_any W_1795c = Some (Mul32 M_MUL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17960 : bv 32 := 0x1f251663.
Lemma F_17960 : fetch_word Ubsan.M.loaded_segments (0x17a64 : word) = Some W_17960.
Proof. vm_refl. Qed.
Lemma D_17960 : decode_any W_17960 = Some (Branch BC_NE 10 18 492, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17964 : bv 32 := 0x08040463.
Lemma F_17964 : fetch_word Ubsan.M.loaded_segments (0x17a68 : word) = Some W_17964.
Proof. vm_refl. Qed.
Lemma D_17964 : decode_any W_17964 = Some (Branch BC_EQ 8 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179a0 : bv 32 := 0x00000613.
Lemma F_179a0 : fetch_word Ubsan.M.loaded_segments (0x17aa4 : word) = Some W_179a0.
Proof. vm_refl. Qed.
Lemma D_179a0 : decode_any W_179a0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179a4 : bv 32 := 0x02c0006f.
Lemma F_179a4 : fetch_word Ubsan.M.loaded_segments (0x17aa8 : word) = Some W_179a4.
Proof. vm_refl. Qed.
Lemma D_179a4 : decode_any W_179a4 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179d0 : bv 32 := 0x02813083.
Lemma F_179d0 : fetch_word Ubsan.M.loaded_segments (0x17ad4 : word) = Some W_179d0.
Proof. vm_refl. Qed.
Lemma D_179d0 : decode_any W_179d0 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179d4 : bv 32 := 0x02013403.
Lemma F_179d4 : fetch_word Ubsan.M.loaded_segments (0x17ad8 : word) = Some W_179d4.
Proof. vm_refl. Qed.
Lemma D_179d4 : decode_any W_179d4 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179d8 : bv 32 := 0x01813483.
Lemma F_179d8 : fetch_word Ubsan.M.loaded_segments (0x17adc : word) = Some W_179d8.
Proof. vm_refl. Qed.
Lemma D_179d8 : decode_any W_179d8 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179dc : bv 32 := 0x01013903.
Lemma F_179dc : fetch_word Ubsan.M.loaded_segments (0x17ae0 : word) = Some W_179dc.
Proof. vm_refl. Qed.
Lemma D_179dc : decode_any W_179dc = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179e0 : bv 32 := 0x00813983.
Lemma F_179e0 : fetch_word Ubsan.M.loaded_segments (0x17ae4 : word) = Some W_179e0.
Proof. vm_refl. Qed.
Lemma D_179e0 : decode_any W_179e0 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179e4 : bv 32 := 0x03010113.
Lemma F_179e4 : fetch_word Ubsan.M.loaded_segments (0x17ae8 : word) = Some W_179e4.
Proof. vm_refl. Qed.
Lemma D_179e4 : decode_any W_179e4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179e8 : bv 32 := 0xad1fd06f.
Lemma F_179e8 : fetch_word Ubsan.M.loaded_segments (0x17aec : word) = Some W_179e8.
Proof. vm_refl. Qed.
Lemma D_179e8 : decode_any W_179e8 = Some (Jal 0 2087632, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179ec : bv 32 := 0x00048513.
Lemma F_179ec : fetch_word Ubsan.M.loaded_segments (0x17af0 : word) = Some W_179ec.
Proof. vm_refl. Qed.
Lemma D_179ec : decode_any W_179ec = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179f0 : bv 32 := 0xe90ff0ef.
Lemma F_179f0 : fetch_word Ubsan.M.loaded_segments (0x17af4 : word) = Some W_179f0.
Proof. vm_refl. Qed.
Lemma D_179f0 : decode_any W_179f0 = Some (Jal 1 2094736, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179f4 : bv 32 := 0x06050463.
Lemma F_179f4 : fetch_word Ubsan.M.loaded_segments (0x17af8 : word) = Some W_179f4.
Proof. vm_refl. Qed.
Lemma D_179f4 : decode_any W_179f4 = Some (Branch BC_EQ 10 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179f8 : bv 32 := 0x00050413.
Lemma F_179f8 : fetch_word Ubsan.M.loaded_segments (0x17afc : word) = Some W_179f8.
Proof. vm_refl. Qed.
Lemma D_179f8 : decode_any W_179f8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179fc : bv 32 := 0x00757513.
Lemma F_179fc : fetch_word Ubsan.M.loaded_segments (0x17b00 : word) = Some W_179fc.
Proof. vm_refl. Qed.
Lemma D_179fc : decode_any W_179fc = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a00 : bv 32 := 0x14051663.
Lemma F_17a00 : fetch_word Ubsan.M.loaded_segments (0x17b04 : word) = Some W_17a00.
Proof. vm_refl. Qed.
Lemma D_17a00 : decode_any W_17a00 = Some (Branch BC_NE 10 0 332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a04 : bv 32 := 0x01046503.
Lemma F_17a04 : fetch_word Ubsan.M.loaded_segments (0x17b08 : word) = Some W_17a04.
Proof. vm_refl. Qed.
Lemma D_17a04 : decode_any W_17a04 = Some (Load SZ4 false 10 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a08 : bv 32 := 0x00446583.
Lemma F_17a08 : fetch_word Ubsan.M.loaded_segments (0x17b0c : word) = Some W_17a08.
Proof. vm_refl. Qed.
Lemma D_17a08 : decode_any W_17a08 = Some (Load SZ4 false 11 8 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a0c : bv 32 := 0x00251513.
Lemma F_17a0c : fetch_word Ubsan.M.loaded_segments (0x17b10 : word) = Some W_17a0c.
Proof. vm_refl. Qed.
Lemma D_17a0c : decode_any W_17a0c = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a10 : bv 32 := 0x02b516b3.
Lemma F_17a10 : fetch_word Ubsan.M.loaded_segments (0x17b14 : word) = Some W_17a10.
Proof. vm_refl. Qed.
Lemma D_17a10 : decode_any W_17a10 = Some (Mul M_MULH 13 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a14 : bv 32 := 0x02b50633.
Lemma F_17a14 : fetch_word Ubsan.M.loaded_segments (0x17b18 : word) = Some W_17a14.
Proof. vm_refl. Qed.
Lemma D_17a14 : decode_any W_17a14 = Some (Mul M_MUL 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a18 : bv 32 := 0x43f65513.
Lemma F_17a18 : fetch_word Ubsan.M.loaded_segments (0x17b1c : word) = Some W_17a18.
Proof. vm_refl. Qed.
Lemma D_17a18 : decode_any W_17a18 = Some (ShiftImm ALU_SRA 10 12 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a1c : bv 32 := 0x12a69863.
Lemma F_17a1c : fetch_word Ubsan.M.loaded_segments (0x17b20 : word) = Some W_17a1c.
Proof. vm_refl. Qed.
Lemma D_17a1c : decode_any W_17a1c = Some (Branch BC_NE 13 10 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a20 : bv 32 := 0x03843503.
Lemma F_17a20 : fetch_word Ubsan.M.loaded_segments (0x17b24 : word) = Some W_17a20.
Proof. vm_refl. Qed.
Lemma D_17a20 : decode_any W_17a20 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a24 : bv 32 := 0x00000593.
Lemma F_17a24 : fetch_word Ubsan.M.loaded_segments (0x17b28 : word) = Some W_17a24.
Proof. vm_refl. Qed.
Lemma D_17a24 : decode_any W_17a24 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a28 : bv 32 := 0x79d1a0ef.
Lemma F_17a28 : fetch_word Ubsan.M.loaded_segments (0x17b2c : word) = Some W_17a28.
Proof. vm_refl. Qed.
Lemma D_17a28 : decode_any W_17a28 = Some (Jal 1 110492, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a2c : bv 32 := 0x00747513.
Lemma F_17a2c : fetch_word Ubsan.M.loaded_segments (0x17b30 : word) = Some W_17a2c.
Proof. vm_refl. Qed.
Lemma D_17a2c : decode_any W_17a2c = Some (OpImm ALU_AND 10 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a30 : bv 32 := 0x0a050c63.
Lemma F_17a30 : fetch_word Ubsan.M.loaded_segments (0x17b34 : word) = Some W_17a30.
Proof. vm_refl. Qed.
Lemma D_17a30 : decode_any W_17a30 = Some (Branch BC_EQ 10 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a5c : bv 32 := 0x0001c517.
Lemma F_17a5c : fetch_word Ubsan.M.loaded_segments (0x17b60 : word) = Some W_17a5c.
Proof. vm_refl. Qed.
Lemma D_17a5c : decode_any W_17a5c = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a60 : bv 32 := 0x69853983.
Lemma F_17a60 : fetch_word Ubsan.M.loaded_segments (0x17b64 : word) = Some W_17a60.
Proof. vm_refl. Qed.
Lemma D_17a60 : decode_any W_17a60 = Some (Load SZ8 true 19 10 1688, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a64 : bv 32 := 0x0009a503.
Lemma F_17a64 : fetch_word Ubsan.M.loaded_segments (0x17b68 : word) = Some W_17a64.
Proof. vm_refl. Qed.
Lemma D_17a64 : decode_any W_17a64 = Some (Load SZ4 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a68 : bv 32 := 0x00600593.
Lemma F_17a68 : fetch_word Ubsan.M.loaded_segments (0x17b6c : word) = Some W_17a68.
Proof. vm_refl. Qed.
Lemma D_17a68 : decode_any W_17a68 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a6c : bv 32 := 0x0ab55e63.
Lemma F_17a6c : fetch_word Ubsan.M.loaded_segments (0x17b70 : word) = Some W_17a6c.
Proof. vm_refl. Qed.
Lemma D_17a6c : decode_any W_17a6c = Some (Branch BC_GE 10 11 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a70 : bv 32 := 0xffff9517.
Lemma F_17a70 : fetch_word Ubsan.M.loaded_segments (0x17b74 : word) = Some W_17a70.
Proof. vm_refl. Qed.
Lemma D_17a70 : decode_any W_17a70 = Some (Auipc 10 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a74 : bv 32 := 0xffff9597.
Lemma F_17a74 : fetch_word Ubsan.M.loaded_segments (0x17b78 : word) = Some W_17a74.
Proof. vm_refl. Qed.
Lemma D_17a74 : decode_any W_17a74 = Some (Auipc 11 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a78 : bv 32 := 0x9ab50513.
Lemma F_17a78 : fetch_word Ubsan.M.loaded_segments (0x17b7c : word) = Some W_17a78.
Proof. vm_refl. Qed.
Lemma D_17a78 : decode_any W_17a78 = Some (OpImm ALU_ADD 10 10 2475, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a7c : bv 32 := 0x29158593.
Lemma F_17a7c : fetch_word Ubsan.M.loaded_segments (0x17b80 : word) = Some W_17a7c.
Proof. vm_refl. Qed.
Lemma D_17a7c : decode_any W_17a7c = Some (OpImm ALU_ADD 11 11 657, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a80 : bv 32 := 0x00000613.
Lemma F_17a80 : fetch_word Ubsan.M.loaded_segments (0x17b84 : word) = Some W_17a80.
Proof. vm_refl. Qed.
Lemma D_17a80 : decode_any W_17a80 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a84 : bv 32 := 0xa35fd0ef.
Lemma F_17a84 : fetch_word Ubsan.M.loaded_segments (0x17b88 : word) = Some W_17a84.
Proof. vm_refl. Qed.
Lemma D_17a84 : decode_any W_17a84 = Some (Jal 1 2087476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a88 : bv 32 := 0x08050063.
Lemma F_17a88 : fetch_word Ubsan.M.loaded_segments (0x17b8c : word) = Some W_17a88.
Proof. vm_refl. Qed.
Lemma D_17a88 : decode_any W_17a88 = Some (Branch BC_EQ 10 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ae8 : bv 32 := 0x03843503.
Lemma F_17ae8 : fetch_word Ubsan.M.loaded_segments (0x17bec : word) = Some W_17ae8.
Proof. vm_refl. Qed.
Lemma D_17ae8 : decode_any W_17ae8 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17aec : bv 32 := 0x0384b583.
Lemma F_17aec : fetch_word Ubsan.M.loaded_segments (0x17bf0 : word) = Some W_17aec.
Proof. vm_refl. Qed.
Lemma D_17aec : decode_any W_17aec = Some (Load SZ8 true 11 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17af0 : bv 32 := 0x00b56633.
Lemma F_17af0 : fetch_word Ubsan.M.loaded_segments (0x17bf4 : word) = Some W_17af0.
Proof. vm_refl. Qed.
Lemma D_17af0 : decode_any W_17af0 = Some (Op ALU_OR 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17af4 : bv 32 := 0x00367613.
Lemma F_17af4 : fetch_word Ubsan.M.loaded_segments (0x17bf8 : word) = Some W_17af4.
Proof. vm_refl. Qed.
Lemma D_17af4 : decode_any W_17af4 = Some (OpImm ALU_AND 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17af8 : bv 32 := 0x04061a63.
Lemma F_17af8 : fetch_word Ubsan.M.loaded_segments (0x17bfc : word) = Some W_17af8.
Proof. vm_refl. Qed.
Lemma D_17af8 : decode_any W_17af8 = Some (Branch BC_NE 12 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17afc : bv 32 := 0x0009061b.
Lemma F_17afc : fetch_word Ubsan.M.loaded_segments (0x17c00 : word) = Some W_17afc.
Proof. vm_refl. Qed.
Lemma D_17afc : decode_any W_17afc = Some (OpImm32 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b00 : bv 32 := 0x2c11a0ef.
Lemma F_17b00 : fetch_word Ubsan.M.loaded_segments (0x17c04 : word) = Some W_17b00.
Proof. vm_refl. Qed.
Lemma D_17b00 : decode_any W_17b00 = Some (Jal 1 109248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b04 : bv 32 := 0x0280006f.
Lemma F_17b04 : fetch_word Ubsan.M.loaded_segments (0x17c08 : word) = Some W_17b04.
Proof. vm_refl. Qed.
Lemma D_17b04 : decode_any W_17b04 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b08 : bv 32 := 0x0009a503.
Lemma F_17b08 : fetch_word Ubsan.M.loaded_segments (0x17c0c : word) = Some W_17b08.
Proof. vm_refl. Qed.
Lemma D_17b08 : decode_any W_17b08 = Some (Load SZ4 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b0c : bv 32 := 0x00500593.
Lemma F_17b0c : fetch_word Ubsan.M.loaded_segments (0x17c10 : word) = Some W_17b0c.
Proof. vm_refl. Qed.
Lemma D_17b0c : decode_any W_17b0c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b10 : bv 32 := 0x00a5cc63.
Lemma F_17b10 : fetch_word Ubsan.M.loaded_segments (0x17c14 : word) = Some W_17b10.
Proof. vm_refl. Qed.
Lemma D_17b10 : decode_any W_17b10 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b14 : bv 32 := 0xffff9517.
Lemma F_17b14 : fetch_word Ubsan.M.loaded_segments (0x17c18 : word) = Some W_17b14.
Proof. vm_refl. Qed.
Lemma D_17b14 : decode_any W_17b14 = Some (Auipc 10 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b18 : bv 32 := 0xffff9597.
Lemma F_17b18 : fetch_word Ubsan.M.loaded_segments (0x17c1c : word) = Some W_17b18.
Proof. vm_refl. Qed.
Lemma D_17b18 : decode_any W_17b18 = Some (Auipc 11 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b1c : bv 32 := 0x90750513.
Lemma F_17b1c : fetch_word Ubsan.M.loaded_segments (0x17c20 : word) = Some W_17b1c.
Proof. vm_refl. Qed.
Lemma D_17b1c : decode_any W_17b1c = Some (OpImm ALU_ADD 10 10 2311, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b20 : bv 32 := 0x19358593.
Lemma F_17b20 : fetch_word Ubsan.M.loaded_segments (0x17c24 : word) = Some W_17b20.
Proof. vm_refl. Qed.
Lemma D_17b20 : decode_any W_17b20 = Some (OpImm ALU_ADD 11 11 403, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b24 : bv 32 := 0xe7dff06f.
Lemma F_17b24 : fetch_word Ubsan.M.loaded_segments (0x17c28 : word) = Some W_17b24.
Proof. vm_refl. Qed.
Lemma D_17b24 : decode_any W_17b24 = Some (Jal 0 2096764, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b2c : bv 32 := 0x00040513.
Lemma F_17b2c : fetch_word Ubsan.M.loaded_segments (0x17c30 : word) = Some W_17b2c.
Proof. vm_refl. Qed.
Lemma D_17b2c : decode_any W_17b2c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b30 : bv 32 := 0x02813083.
Lemma F_17b30 : fetch_word Ubsan.M.loaded_segments (0x17c34 : word) = Some W_17b30.
Proof. vm_refl. Qed.
Lemma D_17b30 : decode_any W_17b30 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b34 : bv 32 := 0x02013403.
Lemma F_17b34 : fetch_word Ubsan.M.loaded_segments (0x17c38 : word) = Some W_17b34.
Proof. vm_refl. Qed.
Lemma D_17b34 : decode_any W_17b34 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b38 : bv 32 := 0x01813483.
Lemma F_17b38 : fetch_word Ubsan.M.loaded_segments (0x17c3c : word) = Some W_17b38.
Proof. vm_refl. Qed.
Lemma D_17b38 : decode_any W_17b38 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b3c : bv 32 := 0x01013903.
Lemma F_17b3c : fetch_word Ubsan.M.loaded_segments (0x17c40 : word) = Some W_17b3c.
Proof. vm_refl. Qed.
Lemma D_17b3c : decode_any W_17b3c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b40 : bv 32 := 0x00813983.
Lemma F_17b40 : fetch_word Ubsan.M.loaded_segments (0x17c44 : word) = Some W_17b40.
Proof. vm_refl. Qed.
Lemma D_17b40 : decode_any W_17b40 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b44 : bv 32 := 0x03010113.
Lemma F_17b44 : fetch_word Ubsan.M.loaded_segments (0x17c48 : word) = Some W_17b44.
Proof. vm_refl. Qed.
Lemma D_17b44 : decode_any W_17b44 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b48 : bv 32 := 0x00008067.
Lemma F_17b48 : fetch_word Ubsan.M.loaded_segments (0x17c4c : word) = Some W_17b48.
Proof. vm_refl. Qed.
Lemma D_17b48 : decode_any W_17b48 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
