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
Definition W_153e8 : bv 32 := 0xff010113.
Lemma F_153e8 : fetch_word Ubsan.M.loaded_segments (0x154ec : word) = Some W_153e8.
Proof. vm_refl. Qed.
Lemma D_153e8 : decode_any W_153e8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153ec : bv 32 := 0x00113423.
Lemma F_153ec : fetch_word Ubsan.M.loaded_segments (0x154f0 : word) = Some W_153ec.
Proof. vm_refl. Qed.
Lemma D_153ec : decode_any W_153ec = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153f0 : bv 32 := 0x00813023.
Lemma F_153f0 : fetch_word Ubsan.M.loaded_segments (0x154f4 : word) = Some W_153f0.
Proof. vm_refl. Qed.
Lemma D_153f0 : decode_any W_153f0 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153f4 : bv 32 := 0x00060413.
Lemma F_153f4 : fetch_word Ubsan.M.loaded_segments (0x154f8 : word) = Some W_153f4.
Proof. vm_refl. Qed.
Lemma D_153f4 : decode_any W_153f4 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153f8 : bv 32 := 0x00050613.
Lemma F_153f8 : fetch_word Ubsan.M.loaded_segments (0x154fc : word) = Some W_153f8.
Proof. vm_refl. Qed.
Lemma D_153f8 : decode_any W_153f8 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153fc : bv 32 := 0xffffc517.
Lemma F_153fc : fetch_word Ubsan.M.loaded_segments (0x15500 : word) = Some W_153fc.
Proof. vm_refl. Qed.
Lemma D_153fc : decode_any W_153fc = Some (Auipc 10 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15400 : bv 32 := 0xf8350513.
Lemma F_15400 : fetch_word Ubsan.M.loaded_segments (0x15504 : word) = Some W_15400.
Proof. vm_refl. Qed.
Lemma D_15400 : decode_any W_15400 = Some (OpImm ALU_ADD 10 10 3971, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15404 : bv 32 := 0x018000ef.
Lemma F_15404 : fetch_word Ubsan.M.loaded_segments (0x15508 : word) = Some W_15404.
Proof. vm_refl. Qed.
Lemma D_15404 : decode_any W_15404 = Some (Jal 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15408 : bv 32 := 0x00040513.
Lemma F_15408 : fetch_word Ubsan.M.loaded_segments (0x1550c : word) = Some W_15408.
Proof. vm_refl. Qed.
Lemma D_15408 : decode_any W_15408 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1540c : bv 32 := 0x00813083.
Lemma F_1540c : fetch_word Ubsan.M.loaded_segments (0x15510 : word) = Some W_1540c.
Proof. vm_refl. Qed.
Lemma D_1540c : decode_any W_1540c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15410 : bv 32 := 0x00013403.
Lemma F_15410 : fetch_word Ubsan.M.loaded_segments (0x15514 : word) = Some W_15410.
Proof. vm_refl. Qed.
Lemma D_15410 : decode_any W_15410 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15414 : bv 32 := 0x01010113.
Lemma F_15414 : fetch_word Ubsan.M.loaded_segments (0x15518 : word) = Some W_15414.
Proof. vm_refl. Qed.
Lemma D_15414 : decode_any W_15414 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15418 : bv 32 := 0x00008067.
Lemma F_15418 : fetch_word Ubsan.M.loaded_segments (0x1551c : word) = Some W_15418.
Proof. vm_refl. Qed.
Lemma D_15418 : decode_any W_15418 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154b8 : bv 32 := 0xff010113.
Lemma F_154b8 : fetch_word Ubsan.M.loaded_segments (0x155bc : word) = Some W_154b8.
Proof. vm_refl. Qed.
Lemma D_154b8 : decode_any W_154b8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154bc : bv 32 := 0x00113423.
Lemma F_154bc : fetch_word Ubsan.M.loaded_segments (0x155c0 : word) = Some W_154bc.
Proof. vm_refl. Qed.
Lemma D_154bc : decode_any W_154bc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154c0 : bv 32 := 0x00813023.
Lemma F_154c0 : fetch_word Ubsan.M.loaded_segments (0x155c4 : word) = Some W_154c0.
Proof. vm_refl. Qed.
Lemma D_154c0 : decode_any W_154c0 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154c4 : bv 32 := 0x00060413.
Lemma F_154c4 : fetch_word Ubsan.M.loaded_segments (0x155c8 : word) = Some W_154c4.
Proof. vm_refl. Qed.
Lemma D_154c4 : decode_any W_154c4 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154c8 : bv 32 := 0x00050613.
Lemma F_154c8 : fetch_word Ubsan.M.loaded_segments (0x155cc : word) = Some W_154c8.
Proof. vm_refl. Qed.
Lemma D_154c8 : decode_any W_154c8 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154cc : bv 32 := 0xffffc517.
Lemma F_154cc : fetch_word Ubsan.M.loaded_segments (0x155d0 : word) = Some W_154cc.
Proof. vm_refl. Qed.
Lemma D_154cc : decode_any W_154cc = Some (Auipc 10 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154d0 : bv 32 := 0xeb350513.
Lemma F_154d0 : fetch_word Ubsan.M.loaded_segments (0x155d4 : word) = Some W_154d0.
Proof. vm_refl. Qed.
Lemma D_154d0 : decode_any W_154d0 = Some (OpImm ALU_ADD 10 10 3763, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154d4 : bv 32 := 0xf49ff0ef.
Lemma F_154d4 : fetch_word Ubsan.M.loaded_segments (0x155d8 : word) = Some W_154d4.
Proof. vm_refl. Qed.
Lemma D_154d4 : decode_any W_154d4 = Some (Jal 1 2096968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154d8 : bv 32 := 0x00040513.
Lemma F_154d8 : fetch_word Ubsan.M.loaded_segments (0x155dc : word) = Some W_154d8.
Proof. vm_refl. Qed.
Lemma D_154d8 : decode_any W_154d8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154dc : bv 32 := 0x00813083.
Lemma F_154dc : fetch_word Ubsan.M.loaded_segments (0x155e0 : word) = Some W_154dc.
Proof. vm_refl. Qed.
Lemma D_154dc : decode_any W_154dc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154e0 : bv 32 := 0x00013403.
Lemma F_154e0 : fetch_word Ubsan.M.loaded_segments (0x155e4 : word) = Some W_154e0.
Proof. vm_refl. Qed.
Lemma D_154e0 : decode_any W_154e0 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154e4 : bv 32 := 0x01010113.
Lemma F_154e4 : fetch_word Ubsan.M.loaded_segments (0x155e8 : word) = Some W_154e4.
Proof. vm_refl. Qed.
Lemma D_154e4 : decode_any W_154e4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154e8 : bv 32 := 0x00008067.
Lemma F_154e8 : fetch_word Ubsan.M.loaded_segments (0x155ec : word) = Some W_154e8.
Proof. vm_refl. Qed.
Lemma D_154e8 : decode_any W_154e8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15658 : bv 32 := 0xfe010113.
Lemma F_15658 : fetch_word Ubsan.M.loaded_segments (0x1575c : word) = Some W_15658.
Proof. vm_refl. Qed.
Lemma D_15658 : decode_any W_15658 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1565c : bv 32 := 0x00113c23.
Lemma F_1565c : fetch_word Ubsan.M.loaded_segments (0x15760 : word) = Some W_1565c.
Proof. vm_refl. Qed.
Lemma D_1565c : decode_any W_1565c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15660 : bv 32 := 0x00813823.
Lemma F_15660 : fetch_word Ubsan.M.loaded_segments (0x15764 : word) = Some W_15660.
Proof. vm_refl. Qed.
Lemma D_15660 : decode_any W_15660 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15664 : bv 32 := 0x00913423.
Lemma F_15664 : fetch_word Ubsan.M.loaded_segments (0x15768 : word) = Some W_15664.
Proof. vm_refl. Qed.
Lemma D_15664 : decode_any W_15664 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15668 : bv 32 := 0x02050a63.
Lemma F_15668 : fetch_word Ubsan.M.loaded_segments (0x1576c : word) = Some W_15668.
Proof. vm_refl. Qed.
Lemma D_15668 : decode_any W_15668 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1566c : bv 32 := 0x00050413.
Lemma F_1566c : fetch_word Ubsan.M.loaded_segments (0x15770 : word) = Some W_1566c.
Proof. vm_refl. Qed.
Lemma D_1566c : decode_any W_1566c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15670 : bv 32 := 0x00757513.
Lemma F_15670 : fetch_word Ubsan.M.loaded_segments (0x15774 : word) = Some W_15670.
Proof. vm_refl. Qed.
Lemma D_15670 : decode_any W_15670 = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15674 : bv 32 := 0x08051663.
Lemma F_15674 : fetch_word Ubsan.M.loaded_segments (0x15778 : word) = Some W_15674.
Proof. vm_refl. Qed.
Lemma D_15674 : decode_any W_15674 = Some (Branch BC_NE 10 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15678 : bv 32 := 0x00058493.
Lemma F_15678 : fetch_word Ubsan.M.loaded_segments (0x1577c : word) = Some W_15678.
Proof. vm_refl. Qed.
Lemma D_15678 : decode_any W_15678 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1567c : bv 32 := 0x00043503.
Lemma F_1567c : fetch_word Ubsan.M.loaded_segments (0x15780 : word) = Some W_1567c.
Proof. vm_refl. Qed.
Lemma D_1567c : decode_any W_1567c = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15680 : bv 32 := 0x00050463.
Lemma F_15680 : fetch_word Ubsan.M.loaded_segments (0x15784 : word) = Some W_15680.
Proof. vm_refl. Qed.
Lemma D_15680 : decode_any W_15680 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15688 : bv 32 := 0x04048863.
Lemma F_15688 : fetch_word Ubsan.M.loaded_segments (0x1578c : word) = Some W_15688.
Proof. vm_refl. Qed.
Lemma D_15688 : decode_any W_15688 = Some (Branch BC_EQ 9 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156d8 : bv 32 := 0x00000593.
Lemma F_156d8 : fetch_word Ubsan.M.loaded_segments (0x157dc : word) = Some W_156d8.
Proof. vm_refl. Qed.
Lemma D_156d8 : decode_any W_156d8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156dc : bv 32 := 0x00000513.
Lemma F_156dc : fetch_word Ubsan.M.loaded_segments (0x157e0 : word) = Some W_156dc.
Proof. vm_refl. Qed.
Lemma D_156dc : decode_any W_156dc = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156e0 : bv 32 := 0x00b43023.
Lemma F_156e0 : fetch_word Ubsan.M.loaded_segments (0x157e4 : word) = Some W_156e0.
Proof. vm_refl. Qed.
Lemma D_156e0 : decode_any W_156e0 = Some (Store SZ8 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156e4 : bv 32 := 0x0080006f.
Lemma F_156e4 : fetch_word Ubsan.M.loaded_segments (0x157e8 : word) = Some W_156e4.
Proof. vm_refl. Qed.
Lemma D_156e4 : decode_any W_156e4 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156ec : bv 32 := 0x01813083.
Lemma F_156ec : fetch_word Ubsan.M.loaded_segments (0x157f0 : word) = Some W_156ec.
Proof. vm_refl. Qed.
Lemma D_156ec : decode_any W_156ec = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156f0 : bv 32 := 0x01013403.
Lemma F_156f0 : fetch_word Ubsan.M.loaded_segments (0x157f4 : word) = Some W_156f0.
Proof. vm_refl. Qed.
Lemma D_156f0 : decode_any W_156f0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156f4 : bv 32 := 0x00813483.
Lemma F_156f4 : fetch_word Ubsan.M.loaded_segments (0x157f8 : word) = Some W_156f4.
Proof. vm_refl. Qed.
Lemma D_156f4 : decode_any W_156f4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156f8 : bv 32 := 0x02010113.
Lemma F_156f8 : fetch_word Ubsan.M.loaded_segments (0x157fc : word) = Some W_156f8.
Proof. vm_refl. Qed.
Lemma D_156f8 : decode_any W_156f8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156fc : bv 32 := 0x00008067.
Lemma F_156fc : fetch_word Ubsan.M.loaded_segments (0x15800 : word) = Some W_156fc.
Proof. vm_refl. Qed.
Lemma D_156fc : decode_any W_156fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
