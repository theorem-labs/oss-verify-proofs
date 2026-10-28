(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_18064 : bv 32 := 0xfe010113.
Lemma F_18064 : fetch_word Ubsan.M.loaded_segments (0x18064 : word) = Some W_18064.
Proof. vm_refl. Qed.
Lemma D_18064 : decode_any W_18064 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_18068 : bv 32 := 0x00113c23.
Lemma F_18068 : fetch_word Ubsan.M.loaded_segments (0x18068 : word) = Some W_18068.
Proof. vm_refl. Qed.
Lemma D_18068 : decode_any W_18068 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1806c : bv 32 := 0x00813823.
Lemma F_1806c : fetch_word Ubsan.M.loaded_segments (0x1806c : word) = Some W_1806c.
Proof. vm_refl. Qed.
Lemma D_1806c : decode_any W_1806c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18070 : bv 32 := 0x00913423.
Lemma F_18070 : fetch_word Ubsan.M.loaded_segments (0x18070 : word) = Some W_18070.
Proof. vm_refl. Qed.
Lemma D_18070 : decode_any W_18070 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18074 : bv 32 := 0x02050a63.
Lemma F_18074 : fetch_word Ubsan.M.loaded_segments (0x18074 : word) = Some W_18074.
Proof. vm_refl. Qed.
Lemma D_18074 : decode_any W_18074 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_18078 : bv 32 := 0x00050413.
Lemma F_18078 : fetch_word Ubsan.M.loaded_segments (0x18078 : word) = Some W_18078.
Proof. vm_refl. Qed.
Lemma D_18078 : decode_any W_18078 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1807c : bv 32 := 0x00757513.
Lemma F_1807c : fetch_word Ubsan.M.loaded_segments (0x1807c : word) = Some W_1807c.
Proof. vm_refl. Qed.
Lemma D_1807c : decode_any W_1807c = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_18080 : bv 32 := 0x08051663.
Lemma F_18080 : fetch_word Ubsan.M.loaded_segments (0x18080 : word) = Some W_18080.
Proof. vm_refl. Qed.
Lemma D_18080 : decode_any W_18080 = Some (Branch BC_NE 10 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_18084 : bv 32 := 0x00058493.
Lemma F_18084 : fetch_word Ubsan.M.loaded_segments (0x18084 : word) = Some W_18084.
Proof. vm_refl. Qed.
Lemma D_18084 : decode_any W_18084 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18088 : bv 32 := 0x00043503.
Lemma F_18088 : fetch_word Ubsan.M.loaded_segments (0x18088 : word) = Some W_18088.
Proof. vm_refl. Qed.
Lemma D_18088 : decode_any W_18088 = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1808c : bv 32 := 0x00050463.
Lemma F_1808c : fetch_word Ubsan.M.loaded_segments (0x1808c : word) = Some W_1808c.
Proof. vm_refl. Qed.
Lemma D_1808c : decode_any W_1808c = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18090 : bv 32 := 0x1a0240ef.
Lemma F_18090 : fetch_word Ubsan.M.loaded_segments (0x18090 : word) = Some W_18090.
Proof. vm_refl. Qed.
Lemma D_18090 : decode_any W_18090 = Some (Jal 1 147872, 4%Z).
Proof. vm_refl. Qed.

Definition W_18094 : bv 32 := 0x04048863.
Lemma F_18094 : fetch_word Ubsan.M.loaded_segments (0x18094 : word) = Some W_18094.
Proof. vm_refl. Qed.
Lemma D_18094 : decode_any W_18094 = Some (Branch BC_EQ 9 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_18098 : bv 32 := 0x00048513.
Lemma F_18098 : fetch_word Ubsan.M.loaded_segments (0x18098 : word) = Some W_18098.
Proof. vm_refl. Qed.
Lemma D_18098 : decode_any W_18098 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1809c : bv 32 := 0xe8dff0ef.
Lemma F_1809c : fetch_word Ubsan.M.loaded_segments (0x1809c : word) = Some W_1809c.
Proof. vm_refl. Qed.
Lemma D_1809c : decode_any W_1809c = Some (Jal 1 2096780, 4%Z).
Proof. vm_refl. Qed.

Definition W_180a0 : bv 32 := 0x00050593.
Lemma F_180a0 : fetch_word Ubsan.M.loaded_segments (0x180a0 : word) = Some W_180a0.
Proof. vm_refl. Qed.
Lemma D_180a0 : decode_any W_180a0 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_180a4 : bv 32 := 0x0440006f.
Lemma F_180a4 : fetch_word Ubsan.M.loaded_segments (0x180a4 : word) = Some W_180a4.
Proof. vm_refl. Qed.
Lemma D_180a4 : decode_any W_180a4 = Some (Jal 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_180a8 : bv 32 := 0x0002d517.
Lemma F_180a8 : fetch_word Ubsan.M.loaded_segments (0x180a8 : word) = Some W_180a8.
Proof. vm_refl. Qed.
Lemma D_180a8 : decode_any W_180a8 = Some (Auipc 10 45, 4%Z).
Proof. vm_refl. Qed.

Definition W_180ac : bv 32 := 0xdf053503.
Lemma F_180ac : fetch_word Ubsan.M.loaded_segments (0x180ac : word) = Some W_180ac.
Proof. vm_refl. Qed.
Lemma D_180ac : decode_any W_180ac = Some (Load SZ8 true 10 10 3568, 4%Z).
Proof. vm_refl. Qed.

Definition W_180b0 : bv 32 := 0x00052503.
Lemma F_180b0 : fetch_word Ubsan.M.loaded_segments (0x180b0 : word) = Some W_180b0.
Proof. vm_refl. Qed.
Lemma D_180b0 : decode_any W_180b0 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_180b4 : bv 32 := 0x00500593.
Lemma F_180b4 : fetch_word Ubsan.M.loaded_segments (0x180b4 : word) = Some W_180b4.
Proof. vm_refl. Qed.
Lemma D_180b4 : decode_any W_180b4 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_180b8 : bv 32 := 0x02a5ce63.
Lemma F_180b8 : fetch_word Ubsan.M.loaded_segments (0x180b8 : word) = Some W_180b8.
Proof. vm_refl. Qed.
Lemma D_180b8 : decode_any W_180b8 = Some (Branch BC_LT 11 10 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_180bc : bv 32 := 0xffff9517.
Lemma F_180bc : fetch_word Ubsan.M.loaded_segments (0x180bc : word) = Some W_180bc.
Proof. vm_refl. Qed.
Lemma D_180bc : decode_any W_180bc = Some (Auipc 10 1048569, 4%Z).
Proof. vm_refl. Qed.

Definition W_180c0 : bv 32 := 0xffff9597.
Lemma F_180c0 : fetch_word Ubsan.M.loaded_segments (0x180c0 : word) = Some W_180c0.
Proof. vm_refl. Qed.
Lemma D_180c0 : decode_any W_180c0 = Some (Auipc 11 1048569, 4%Z).
Proof. vm_refl. Qed.

Definition W_180c4 : bv 32 := 0x62050513.
Lemma F_180c4 : fetch_word Ubsan.M.loaded_segments (0x180c4 : word) = Some W_180c4.
Proof. vm_refl. Qed.
Lemma D_180c4 : decode_any W_180c4 = Some (OpImm ALU_ADD 10 10 1568, 4%Z).
Proof. vm_refl. Qed.

Definition W_180c8 : bv 32 := 0xb5c58593.
Lemma F_180c8 : fetch_word Ubsan.M.loaded_segments (0x180c8 : word) = Some W_180c8.
Proof. vm_refl. Qed.
Lemma D_180c8 : decode_any W_180c8 = Some (OpImm ALU_ADD 11 11 2908, 4%Z).
Proof. vm_refl. Qed.

Definition W_180cc : bv 32 := 0x00100613.
Lemma F_180cc : fetch_word Ubsan.M.loaded_segments (0x180cc : word) = Some W_180cc.
Proof. vm_refl. Qed.
Lemma D_180cc : decode_any W_180cc = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_180d0 : bv 32 := 0x01813083.
Lemma F_180d0 : fetch_word Ubsan.M.loaded_segments (0x180d0 : word) = Some W_180d0.
Proof. vm_refl. Qed.
Lemma D_180d0 : decode_any W_180d0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_180d4 : bv 32 := 0x01013403.
Lemma F_180d4 : fetch_word Ubsan.M.loaded_segments (0x180d4 : word) = Some W_180d4.
Proof. vm_refl. Qed.
Lemma D_180d4 : decode_any W_180d4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_180d8 : bv 32 := 0x00813483.
Lemma F_180d8 : fetch_word Ubsan.M.loaded_segments (0x180d8 : word) = Some W_180d8.
Proof. vm_refl. Qed.
Lemma D_180d8 : decode_any W_180d8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_180dc : bv 32 := 0x02010113.
Lemma F_180dc : fetch_word Ubsan.M.loaded_segments (0x180dc : word) = Some W_180dc.
Proof. vm_refl. Qed.
Lemma D_180dc : decode_any W_180dc = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_180e0 : bv 32 := 0xd15ff06f.
Lemma F_180e0 : fetch_word Ubsan.M.loaded_segments (0x180e0 : word) = Some W_180e0.
Proof. vm_refl. Qed.
Lemma D_180e0 : decode_any W_180e0 = Some (Jal 0 2096404, 4%Z).
Proof. vm_refl. Qed.

Definition W_180e4 : bv 32 := 0x00000593.
Lemma F_180e4 : fetch_word Ubsan.M.loaded_segments (0x180e4 : word) = Some W_180e4.
Proof. vm_refl. Qed.
Lemma D_180e4 : decode_any W_180e4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_180e8 : bv 32 := 0x00000513.
Lemma F_180e8 : fetch_word Ubsan.M.loaded_segments (0x180e8 : word) = Some W_180e8.
Proof. vm_refl. Qed.
Lemma D_180e8 : decode_any W_180e8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_180ec : bv 32 := 0x00b43023.
Lemma F_180ec : fetch_word Ubsan.M.loaded_segments (0x180ec : word) = Some W_180ec.
Proof. vm_refl. Qed.
Lemma D_180ec : decode_any W_180ec = Some (Store SZ8 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_180f0 : bv 32 := 0x0080006f.
Lemma F_180f0 : fetch_word Ubsan.M.loaded_segments (0x180f0 : word) = Some W_180f0.
Proof. vm_refl. Qed.
Lemma D_180f0 : decode_any W_180f0 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_180f4 : bv 32 := 0x00100513.
Lemma F_180f4 : fetch_word Ubsan.M.loaded_segments (0x180f4 : word) = Some W_180f4.
Proof. vm_refl. Qed.
Lemma D_180f4 : decode_any W_180f4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_180f8 : bv 32 := 0x01813083.
Lemma F_180f8 : fetch_word Ubsan.M.loaded_segments (0x180f8 : word) = Some W_180f8.
Proof. vm_refl. Qed.
Lemma D_180f8 : decode_any W_180f8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_180fc : bv 32 := 0x01013403.
Lemma F_180fc : fetch_word Ubsan.M.loaded_segments (0x180fc : word) = Some W_180fc.
Proof. vm_refl. Qed.
Lemma D_180fc : decode_any W_180fc = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18100 : bv 32 := 0x00813483.
Lemma F_18100 : fetch_word Ubsan.M.loaded_segments (0x18100 : word) = Some W_18100.
Proof. vm_refl. Qed.
Lemma D_18100 : decode_any W_18100 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18104 : bv 32 := 0x02010113.
Lemma F_18104 : fetch_word Ubsan.M.loaded_segments (0x18104 : word) = Some W_18104.
Proof. vm_refl. Qed.
Lemma D_18104 : decode_any W_18104 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18108 : bv 32 := 0x00008067.
Lemma F_18108 : fetch_word Ubsan.M.loaded_segments (0x18108 : word) = Some W_18108.
Proof. vm_refl. Qed.
Lemma D_18108 : decode_any W_18108 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1810c : bv 32 := 0xc0001073.
Lemma F_1810c : fetch_word Ubsan.M.loaded_segments (0x1810c : word) = Some W_1810c.
Proof. vm_refl. Qed.
Lemma D_1810c : decode_any W_1810c = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.
