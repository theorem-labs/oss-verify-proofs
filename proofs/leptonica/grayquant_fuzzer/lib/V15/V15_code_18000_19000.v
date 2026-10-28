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
Definition W_180a8 : bv 32 := 0xfd010113.
Lemma F_180a8 : fetch_word Ubsan.M.loaded_segments (0x181ac : word) = Some W_180a8.
Proof. vm_refl. Qed.
Lemma D_180a8 : decode_any W_180a8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_180ac : bv 32 := 0x02113423.
Lemma F_180ac : fetch_word Ubsan.M.loaded_segments (0x181b0 : word) = Some W_180ac.
Proof. vm_refl. Qed.
Lemma D_180ac : decode_any W_180ac = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_180b0 : bv 32 := 0x02813023.
Lemma F_180b0 : fetch_word Ubsan.M.loaded_segments (0x181b4 : word) = Some W_180b0.
Proof. vm_refl. Qed.
Lemma D_180b0 : decode_any W_180b0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_180b4 : bv 32 := 0x00913c23.
Lemma F_180b4 : fetch_word Ubsan.M.loaded_segments (0x181b8 : word) = Some W_180b4.
Proof. vm_refl. Qed.
Lemma D_180b4 : decode_any W_180b4 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_180b8 : bv 32 := 0x01213823.
Lemma F_180b8 : fetch_word Ubsan.M.loaded_segments (0x181bc : word) = Some W_180b8.
Proof. vm_refl. Qed.
Lemma D_180b8 : decode_any W_180b8 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_180bc : bv 32 := 0x06050063.
Lemma F_180bc : fetch_word Ubsan.M.loaded_segments (0x181c0 : word) = Some W_180bc.
Proof. vm_refl. Qed.
Lemma D_180bc : decode_any W_180bc = Some (Branch BC_EQ 10 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_180c0 : bv 32 := 0x00058413.
Lemma F_180c0 : fetch_word Ubsan.M.loaded_segments (0x181c4 : word) = Some W_180c0.
Proof. vm_refl. Qed.
Lemma D_180c0 : decode_any W_180c0 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_180c4 : bv 32 := 0x00050913.
Lemma F_180c4 : fetch_word Ubsan.M.loaded_segments (0x181c8 : word) = Some W_180c4.
Proof. vm_refl. Qed.
Lemma D_180c4 : decode_any W_180c4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_180c8 : bv 32 := 0x00c10593.
Lemma F_180c8 : fetch_word Ubsan.M.loaded_segments (0x181cc : word) = Some W_180c8.
Proof. vm_refl. Qed.
Lemma D_180c8 : decode_any W_180c8 = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_180cc : bv 32 := 0x00810613.
Lemma F_180cc : fetch_word Ubsan.M.loaded_segments (0x181d0 : word) = Some W_180cc.
Proof. vm_refl. Qed.
Lemma D_180cc : decode_any W_180cc = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_180d0 : bv 32 := 0x00410693.
Lemma F_180d0 : fetch_word Ubsan.M.loaded_segments (0x181d4 : word) = Some W_180d0.
Proof. vm_refl. Qed.
Lemma D_180d0 : decode_any W_180d0 = Some (OpImm ALU_ADD 13 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_180d4 : bv 32 := 0x908ff0ef.
Lemma F_180d4 : fetch_word Ubsan.M.loaded_segments (0x181d8 : word) = Some W_180d4.
Proof. vm_refl. Qed.
Lemma D_180d4 : decode_any W_180d4 = Some (Jal 1 2093320, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_180d8 : bv 32 := 0x00412503.
Lemma F_180d8 : fetch_word Ubsan.M.loaded_segments (0x181dc : word) = Some W_180d8.
Proof. vm_refl. Qed.
Lemma D_180d8 : decode_any W_180d8 = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_180dc : bv 32 := 0x02000593.
Lemma F_180dc : fetch_word Ubsan.M.loaded_segments (0x181e0 : word) = Some W_180dc.
Proof. vm_refl. Qed.
Lemma D_180dc : decode_any W_180dc = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_180e0 : bv 32 := 0x18b50c63.
Lemma F_180e0 : fetch_word Ubsan.M.loaded_segments (0x181e4 : word) = Some W_180e0.
Proof. vm_refl. Qed.
Lemma D_180e0 : decode_any W_180e0 = Some (Branch BC_EQ 10 11 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18278 : bv 32 := 0x00000513.
Lemma F_18278 : fetch_word Ubsan.M.loaded_segments (0x1837c : word) = Some W_18278.
Proof. vm_refl. Qed.
Lemma D_18278 : decode_any W_18278 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1827c : bv 32 := 0x02813083.
Lemma F_1827c : fetch_word Ubsan.M.loaded_segments (0x18380 : word) = Some W_1827c.
Proof. vm_refl. Qed.
Lemma D_1827c : decode_any W_1827c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18280 : bv 32 := 0x02013403.
Lemma F_18280 : fetch_word Ubsan.M.loaded_segments (0x18384 : word) = Some W_18280.
Proof. vm_refl. Qed.
Lemma D_18280 : decode_any W_18280 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18284 : bv 32 := 0x01813483.
Lemma F_18284 : fetch_word Ubsan.M.loaded_segments (0x18388 : word) = Some W_18284.
Proof. vm_refl. Qed.
Lemma D_18284 : decode_any W_18284 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18288 : bv 32 := 0x01013903.
Lemma F_18288 : fetch_word Ubsan.M.loaded_segments (0x1838c : word) = Some W_18288.
Proof. vm_refl. Qed.
Lemma D_18288 : decode_any W_18288 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1828c : bv 32 := 0x03010113.
Lemma F_1828c : fetch_word Ubsan.M.loaded_segments (0x18390 : word) = Some W_1828c.
Proof. vm_refl. Qed.
Lemma D_1828c : decode_any W_1828c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18290 : bv 32 := 0x00008067.
Lemma F_18290 : fetch_word Ubsan.M.loaded_segments (0x18394 : word) = Some W_18290.
Proof. vm_refl. Qed.
Lemma D_18290 : decode_any W_18290 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1866c : bv 32 := 0xfe010113.
Lemma F_1866c : fetch_word Ubsan.M.loaded_segments (0x18770 : word) = Some W_1866c.
Proof. vm_refl. Qed.
Lemma D_1866c : decode_any W_1866c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18670 : bv 32 := 0x00113c23.
Lemma F_18670 : fetch_word Ubsan.M.loaded_segments (0x18774 : word) = Some W_18670.
Proof. vm_refl. Qed.
Lemma D_18670 : decode_any W_18670 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18674 : bv 32 := 0x00813823.
Lemma F_18674 : fetch_word Ubsan.M.loaded_segments (0x18778 : word) = Some W_18674.
Proof. vm_refl. Qed.
Lemma D_18674 : decode_any W_18674 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18678 : bv 32 := 0x00913423.
Lemma F_18678 : fetch_word Ubsan.M.loaded_segments (0x1877c : word) = Some W_18678.
Proof. vm_refl. Qed.
Lemma D_18678 : decode_any W_18678 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1867c : bv 32 := 0x06050c63.
Lemma F_1867c : fetch_word Ubsan.M.loaded_segments (0x18780 : word) = Some W_1867c.
Proof. vm_refl. Qed.
Lemma D_1867c : decode_any W_1867c = Some (Branch BC_EQ 10 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18680 : bv 32 := 0x00050413.
Lemma F_18680 : fetch_word Ubsan.M.loaded_segments (0x18784 : word) = Some W_18680.
Proof. vm_refl. Qed.
Lemma D_18680 : decode_any W_18680 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18684 : bv 32 := 0x00410613.
Lemma F_18684 : fetch_word Ubsan.M.loaded_segments (0x18788 : word) = Some W_18684.
Proof. vm_refl. Qed.
Lemma D_18684 : decode_any W_18684 = Some (OpImm ALU_ADD 12 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18688 : bv 32 := 0x00000593.
Lemma F_18688 : fetch_word Ubsan.M.loaded_segments (0x1878c : word) = Some W_18688.
Proof. vm_refl. Qed.
Lemma D_18688 : decode_any W_18688 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1868c : bv 32 := 0x0f8000ef.
Lemma F_1868c : fetch_word Ubsan.M.loaded_segments (0x18790 : word) = Some W_1868c.
Proof. vm_refl. Qed.
Lemma D_1868c : decode_any W_1868c = Some (Jal 1 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18690 : bv 32 := 0x00412503.
Lemma F_18690 : fetch_word Ubsan.M.loaded_segments (0x18794 : word) = Some W_18690.
Proof. vm_refl. Qed.
Lemma D_18690 : decode_any W_18690 = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18694 : bv 32 := 0x08050e63.
Lemma F_18694 : fetch_word Ubsan.M.loaded_segments (0x18798 : word) = Some W_18694.
Proof. vm_refl. Qed.
Lemma D_18694 : decode_any W_18694 = Some (Branch BC_EQ 10 0 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18698 : bv 32 := 0x00100513.
Lemma F_18698 : fetch_word Ubsan.M.loaded_segments (0x1879c : word) = Some W_18698.
Proof. vm_refl. Qed.
Lemma D_18698 : decode_any W_18698 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1869c : bv 32 := 0x01800593.
Lemma F_1869c : fetch_word Ubsan.M.loaded_segments (0x187a0 : word) = Some W_1869c.
Proof. vm_refl. Qed.
Lemma D_1869c : decode_any W_1869c = Some (OpImm ALU_ADD 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_186a0 : bv 32 := 0x178100ef.
Lemma F_186a0 : fetch_word Ubsan.M.loaded_segments (0x187a4 : word) = Some W_186a0.
Proof. vm_refl. Qed.
Lemma D_186a0 : decode_any W_186a0 = Some (Jal 1 65912, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_186a4 : bv 32 := 0x00747593.
Lemma F_186a4 : fetch_word Ubsan.M.loaded_segments (0x187a8 : word) = Some W_186a4.
Proof. vm_refl. Qed.
Lemma D_186a4 : decode_any W_186a4 = Some (OpImm ALU_AND 11 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_186a8 : bv 32 := 0x0c059c63.
Lemma F_186a8 : fetch_word Ubsan.M.loaded_segments (0x187ac : word) = Some W_186a8.
Proof. vm_refl. Qed.
Lemma D_186a8 : decode_any W_186a8 = Some (Branch BC_NE 11 0 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_186ac : bv 32 := 0x00050493.
Lemma F_186ac : fetch_word Ubsan.M.loaded_segments (0x187b0 : word) = Some W_186ac.
Proof. vm_refl. Qed.
Lemma D_186ac : decode_any W_186ac = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_186b0 : bv 32 := 0x00c42503.
Lemma F_186b0 : fetch_word Ubsan.M.loaded_segments (0x187b4 : word) = Some W_186b0.
Proof. vm_refl. Qed.
Lemma D_186b0 : decode_any W_186b0 = Some (Load SZ4 true 10 8 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_186b4 : bv 32 := 0x0025159b.
Lemma F_186b4 : fetch_word Ubsan.M.loaded_segments (0x187b8 : word) = Some W_186b4.
Proof. vm_refl. Qed.
Lemma D_186b4 : decode_any W_186b4 = Some (ShiftImm32 ALU_SLL 11 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_186b8 : bv 32 := 0x00100513.
Lemma F_186b8 : fetch_word Ubsan.M.loaded_segments (0x187bc : word) = Some W_186b8.
Proof. vm_refl. Qed.
Lemma D_186b8 : decode_any W_186b8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_186bc : bv 32 := 0x15c100ef.
Lemma F_186bc : fetch_word Ubsan.M.loaded_segments (0x187c0 : word) = Some W_186bc.
Proof. vm_refl. Qed.
Lemma D_186bc : decode_any W_186bc = Some (Jal 1 65884, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_186c0 : bv 32 := 0x0c048063.
Lemma F_186c0 : fetch_word Ubsan.M.loaded_segments (0x187c4 : word) = Some W_186c0.
Proof. vm_refl. Qed.
Lemma D_186c0 : decode_any W_186c0 = Some (Branch BC_EQ 9 0 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_186c4 : bv 32 := 0x0074f593.
Lemma F_186c4 : fetch_word Ubsan.M.loaded_segments (0x187c8 : word) = Some W_186c4.
Proof. vm_refl. Qed.
Lemma D_186c4 : decode_any W_186c4 = Some (OpImm ALU_AND 11 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_186c8 : bv 32 := 0x0a059c63.
Lemma F_186c8 : fetch_word Ubsan.M.loaded_segments (0x187cc : word) = Some W_186c8.
Proof. vm_refl. Qed.
Lemma D_186c8 : decode_any W_186c8 = Some (Branch BC_NE 11 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_186cc : bv 32 := 0x00a4b023.
Lemma F_186cc : fetch_word Ubsan.M.loaded_segments (0x187d0 : word) = Some W_186cc.
Proof. vm_refl. Qed.
Lemma D_186cc : decode_any W_186cc = Some (Store SZ8 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_186d0 : bv 32 := 0x01042603.
Lemma F_186d0 : fetch_word Ubsan.M.loaded_segments (0x187d4 : word) = Some W_186d0.
Proof. vm_refl. Qed.
Lemma D_186d0 : decode_any W_186d0 = Some (Load SZ4 true 12 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_186d4 : bv 32 := 0x00043583.
Lemma F_186d4 : fetch_word Ubsan.M.loaded_segments (0x187d8 : word) = Some W_186d4.
Proof. vm_refl. Qed.
Lemma D_186d4 : decode_any W_186d4 = Some (Load SZ8 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_186d8 : bv 32 := 0x00261613.
Lemma F_186d8 : fetch_word Ubsan.M.loaded_segments (0x187dc : word) = Some W_186d8.
Proof. vm_refl. Qed.
Lemma D_186d8 : decode_any W_186d8 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_186dc : bv 32 := 0x6e5190ef.
Lemma F_186dc : fetch_word Ubsan.M.loaded_segments (0x187e0 : word) = Some W_186dc.
Proof. vm_refl. Qed.
Lemma D_186dc : decode_any W_186dc = Some (Jal 1 106212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_186e0 : bv 32 := 0x01042503.
Lemma F_186e0 : fetch_word Ubsan.M.loaded_segments (0x187e4 : word) = Some W_186e0.
Proof. vm_refl. Qed.
Lemma D_186e0 : decode_any W_186e0 = Some (Load SZ4 true 10 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_186e4 : bv 32 := 0x00a4a823.
Lemma F_186e4 : fetch_word Ubsan.M.loaded_segments (0x187e8 : word) = Some W_186e4.
Proof. vm_refl. Qed.
Lemma D_186e4 : decode_any W_186e4 = Some (Store SZ4 9 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_186e8 : bv 32 := 0x00843503.
Lemma F_186e8 : fetch_word Ubsan.M.loaded_segments (0x187ec : word) = Some W_186e8.
Proof. vm_refl. Qed.
Lemma D_186e8 : decode_any W_186e8 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_186ec : bv 32 := 0x00a4b423.
Lemma F_186ec : fetch_word Ubsan.M.loaded_segments (0x187f0 : word) = Some W_186ec.
Proof. vm_refl. Qed.
Lemma D_186ec : decode_any W_186ec = Some (Store SZ8 9 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_186f0 : bv 32 := 0x0780006f.
Lemma F_186f0 : fetch_word Ubsan.M.loaded_segments (0x187f4 : word) = Some W_186f0.
Proof. vm_refl. Qed.
Lemma D_186f0 : decode_any W_186f0 = Some (Jal 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18768 : bv 32 := 0x00048513.
Lemma F_18768 : fetch_word Ubsan.M.loaded_segments (0x1886c : word) = Some W_18768.
Proof. vm_refl. Qed.
Lemma D_18768 : decode_any W_18768 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1876c : bv 32 := 0x01813083.
Lemma F_1876c : fetch_word Ubsan.M.loaded_segments (0x18870 : word) = Some W_1876c.
Proof. vm_refl. Qed.
Lemma D_1876c : decode_any W_1876c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18770 : bv 32 := 0x01013403.
Lemma F_18770 : fetch_word Ubsan.M.loaded_segments (0x18874 : word) = Some W_18770.
Proof. vm_refl. Qed.
Lemma D_18770 : decode_any W_18770 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18774 : bv 32 := 0x00813483.
Lemma F_18774 : fetch_word Ubsan.M.loaded_segments (0x18878 : word) = Some W_18774.
Proof. vm_refl. Qed.
Lemma D_18774 : decode_any W_18774 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_18778 : bv 32 := 0x02010113.
Lemma F_18778 : fetch_word Ubsan.M.loaded_segments (0x1887c : word) = Some W_18778.
Proof. vm_refl. Qed.
Lemma D_18778 : decode_any W_18778 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1877c : bv 32 := 0x00008067.
Lemma F_1877c : fetch_word Ubsan.M.loaded_segments (0x18880 : word) = Some W_1877c.
Proof. vm_refl. Qed.
Lemma D_1877c : decode_any W_1877c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
