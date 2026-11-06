(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.H Require GcFlushU14.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_15380 : bv 32 := 0xff010113.
Lemma F_15380 : fetch_word Ubsan.M.loaded_segments (0x1547c : word) = Some W_15380.
Proof. vm_refl. Qed.
Lemma D_15380 : decode_any W_15380 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15384 : bv 32 := 0x00113423.
Lemma F_15384 : fetch_word Ubsan.M.loaded_segments (0x15480 : word) = Some W_15384.
Proof. vm_refl. Qed.
Lemma D_15384 : decode_any W_15384 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15388 : bv 32 := 0x00813023.
Lemma F_15388 : fetch_word Ubsan.M.loaded_segments (0x15484 : word) = Some W_15388.
Proof. vm_refl. Qed.
Lemma D_15388 : decode_any W_15388 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1538c : bv 32 := 0x00060413.
Lemma F_1538c : fetch_word Ubsan.M.loaded_segments (0x15488 : word) = Some W_1538c.
Proof. vm_refl. Qed.
Lemma D_1538c : decode_any W_1538c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15390 : bv 32 := 0x00050613.
Lemma F_15390 : fetch_word Ubsan.M.loaded_segments (0x1548c : word) = Some W_15390.
Proof. vm_refl. Qed.
Lemma D_15390 : decode_any W_15390 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15394 : bv 32 := 0xffffc517.
Lemma F_15394 : fetch_word Ubsan.M.loaded_segments (0x15490 : word) = Some W_15394.
Proof. vm_refl. Qed.
Lemma D_15394 : decode_any W_15394 = Some (Auipc 10 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15398 : bv 32 := 0xf1350513.
Lemma F_15398 : fetch_word Ubsan.M.loaded_segments (0x15494 : word) = Some W_15398.
Proof. vm_refl. Qed.
Lemma D_15398 : decode_any W_15398 = Some (OpImm ALU_ADD 10 10 3859, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1539c : bv 32 := 0x018000ef.
Lemma F_1539c : fetch_word Ubsan.M.loaded_segments (0x15498 : word) = Some W_1539c.
Proof. vm_refl. Qed.
Lemma D_1539c : decode_any W_1539c = Some (Jal 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153a0 : bv 32 := 0x00040513.
Lemma F_153a0 : fetch_word Ubsan.M.loaded_segments (0x1549c : word) = Some W_153a0.
Proof. vm_refl. Qed.
Lemma D_153a0 : decode_any W_153a0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153a4 : bv 32 := 0x00813083.
Lemma F_153a4 : fetch_word Ubsan.M.loaded_segments (0x154a0 : word) = Some W_153a4.
Proof. vm_refl. Qed.
Lemma D_153a4 : decode_any W_153a4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153a8 : bv 32 := 0x00013403.
Lemma F_153a8 : fetch_word Ubsan.M.loaded_segments (0x154a4 : word) = Some W_153a8.
Proof. vm_refl. Qed.
Lemma D_153a8 : decode_any W_153a8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153ac : bv 32 := 0x01010113.
Lemma F_153ac : fetch_word Ubsan.M.loaded_segments (0x154a8 : word) = Some W_153ac.
Proof. vm_refl. Qed.
Lemma D_153ac : decode_any W_153ac = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153b0 : bv 32 := 0x00008067.
Lemma F_153b0 : fetch_word Ubsan.M.loaded_segments (0x154ac : word) = Some W_153b0.
Proof. vm_refl. Qed.
Lemma D_153b0 : decode_any W_153b0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15450 : bv 32 := 0xff010113.
Lemma F_15450 : fetch_word Ubsan.M.loaded_segments (0x1554c : word) = Some W_15450.
Proof. vm_refl. Qed.
Lemma D_15450 : decode_any W_15450 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15454 : bv 32 := 0x00113423.
Lemma F_15454 : fetch_word Ubsan.M.loaded_segments (0x15550 : word) = Some W_15454.
Proof. vm_refl. Qed.
Lemma D_15454 : decode_any W_15454 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15458 : bv 32 := 0x00813023.
Lemma F_15458 : fetch_word Ubsan.M.loaded_segments (0x15554 : word) = Some W_15458.
Proof. vm_refl. Qed.
Lemma D_15458 : decode_any W_15458 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1545c : bv 32 := 0x00060413.
Lemma F_1545c : fetch_word Ubsan.M.loaded_segments (0x15558 : word) = Some W_1545c.
Proof. vm_refl. Qed.
Lemma D_1545c : decode_any W_1545c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15460 : bv 32 := 0x00050613.
Lemma F_15460 : fetch_word Ubsan.M.loaded_segments (0x1555c : word) = Some W_15460.
Proof. vm_refl. Qed.
Lemma D_15460 : decode_any W_15460 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15464 : bv 32 := 0xffffc517.
Lemma F_15464 : fetch_word Ubsan.M.loaded_segments (0x15560 : word) = Some W_15464.
Proof. vm_refl. Qed.
Lemma D_15464 : decode_any W_15464 = Some (Auipc 10 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15468 : bv 32 := 0xe4350513.
Lemma F_15468 : fetch_word Ubsan.M.loaded_segments (0x15564 : word) = Some W_15468.
Proof. vm_refl. Qed.
Lemma D_15468 : decode_any W_15468 = Some (OpImm ALU_ADD 10 10 3651, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1546c : bv 32 := 0xf49ff0ef.
Lemma F_1546c : fetch_word Ubsan.M.loaded_segments (0x15568 : word) = Some W_1546c.
Proof. vm_refl. Qed.
Lemma D_1546c : decode_any W_1546c = Some (Jal 1 2096968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15470 : bv 32 := 0x00040513.
Lemma F_15470 : fetch_word Ubsan.M.loaded_segments (0x1556c : word) = Some W_15470.
Proof. vm_refl. Qed.
Lemma D_15470 : decode_any W_15470 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15474 : bv 32 := 0x00813083.
Lemma F_15474 : fetch_word Ubsan.M.loaded_segments (0x15570 : word) = Some W_15474.
Proof. vm_refl. Qed.
Lemma D_15474 : decode_any W_15474 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15478 : bv 32 := 0x00013403.
Lemma F_15478 : fetch_word Ubsan.M.loaded_segments (0x15574 : word) = Some W_15478.
Proof. vm_refl. Qed.
Lemma D_15478 : decode_any W_15478 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1547c : bv 32 := 0x01010113.
Lemma F_1547c : fetch_word Ubsan.M.loaded_segments (0x15578 : word) = Some W_1547c.
Proof. vm_refl. Qed.
Lemma D_1547c : decode_any W_1547c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15480 : bv 32 := 0x00008067.
Lemma F_15480 : fetch_word Ubsan.M.loaded_segments (0x1557c : word) = Some W_15480.
Proof. vm_refl. Qed.
Lemma D_15480 : decode_any W_15480 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155f0 : bv 32 := 0xfe010113.
Lemma F_155f0 : fetch_word Ubsan.M.loaded_segments (0x156ec : word) = Some W_155f0.
Proof. vm_refl. Qed.
Lemma D_155f0 : decode_any W_155f0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155f4 : bv 32 := 0x00113c23.
Lemma F_155f4 : fetch_word Ubsan.M.loaded_segments (0x156f0 : word) = Some W_155f4.
Proof. vm_refl. Qed.
Lemma D_155f4 : decode_any W_155f4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155f8 : bv 32 := 0x00813823.
Lemma F_155f8 : fetch_word Ubsan.M.loaded_segments (0x156f4 : word) = Some W_155f8.
Proof. vm_refl. Qed.
Lemma D_155f8 : decode_any W_155f8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155fc : bv 32 := 0x00913423.
Lemma F_155fc : fetch_word Ubsan.M.loaded_segments (0x156f8 : word) = Some W_155fc.
Proof. vm_refl. Qed.
Lemma D_155fc : decode_any W_155fc = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15600 : bv 32 := 0x02050a63.
Lemma F_15600 : fetch_word Ubsan.M.loaded_segments (0x156fc : word) = Some W_15600.
Proof. vm_refl. Qed.
Lemma D_15600 : decode_any W_15600 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15604 : bv 32 := 0x00050413.
Lemma F_15604 : fetch_word Ubsan.M.loaded_segments (0x15700 : word) = Some W_15604.
Proof. vm_refl. Qed.
Lemma D_15604 : decode_any W_15604 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15608 : bv 32 := 0x00757513.
Lemma F_15608 : fetch_word Ubsan.M.loaded_segments (0x15704 : word) = Some W_15608.
Proof. vm_refl. Qed.
Lemma D_15608 : decode_any W_15608 = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1560c : bv 32 := 0x08051663.
Lemma F_1560c : fetch_word Ubsan.M.loaded_segments (0x15708 : word) = Some W_1560c.
Proof. vm_refl. Qed.
Lemma D_1560c : decode_any W_1560c = Some (Branch BC_NE 10 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15610 : bv 32 := 0x00058493.
Lemma F_15610 : fetch_word Ubsan.M.loaded_segments (0x1570c : word) = Some W_15610.
Proof. vm_refl. Qed.
Lemma D_15610 : decode_any W_15610 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15614 : bv 32 := 0x00043503.
Lemma F_15614 : fetch_word Ubsan.M.loaded_segments (0x15710 : word) = Some W_15614.
Proof. vm_refl. Qed.
Lemma D_15614 : decode_any W_15614 = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15618 : bv 32 := 0x00050463.
Lemma F_15618 : fetch_word Ubsan.M.loaded_segments (0x15714 : word) = Some W_15618.
Proof. vm_refl. Qed.
Lemma D_15618 : decode_any W_15618 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15620 : bv 32 := 0x04048863.
Lemma F_15620 : fetch_word Ubsan.M.loaded_segments (0x1571c : word) = Some W_15620.
Proof. vm_refl. Qed.
Lemma D_15620 : decode_any W_15620 = Some (Branch BC_EQ 9 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15670 : bv 32 := 0x00000593.
Lemma F_15670 : fetch_word Ubsan.M.loaded_segments (0x1576c : word) = Some W_15670.
Proof. vm_refl. Qed.
Lemma D_15670 : decode_any W_15670 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15674 : bv 32 := 0x00000513.
Lemma F_15674 : fetch_word Ubsan.M.loaded_segments (0x15770 : word) = Some W_15674.
Proof. vm_refl. Qed.
Lemma D_15674 : decode_any W_15674 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15678 : bv 32 := 0x00b43023.
Lemma F_15678 : fetch_word Ubsan.M.loaded_segments (0x15774 : word) = Some W_15678.
Proof. vm_refl. Qed.
Lemma D_15678 : decode_any W_15678 = Some (Store SZ8 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1567c : bv 32 := 0x0080006f.
Lemma F_1567c : fetch_word Ubsan.M.loaded_segments (0x15778 : word) = Some W_1567c.
Proof. vm_refl. Qed.
Lemma D_1567c : decode_any W_1567c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15684 : bv 32 := 0x01813083.
Lemma F_15684 : fetch_word Ubsan.M.loaded_segments (0x15780 : word) = Some W_15684.
Proof. vm_refl. Qed.
Lemma D_15684 : decode_any W_15684 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15688 : bv 32 := 0x01013403.
Lemma F_15688 : fetch_word Ubsan.M.loaded_segments (0x15784 : word) = Some W_15688.
Proof. vm_refl. Qed.
Lemma D_15688 : decode_any W_15688 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1568c : bv 32 := 0x00813483.
Lemma F_1568c : fetch_word Ubsan.M.loaded_segments (0x15788 : word) = Some W_1568c.
Proof. vm_refl. Qed.
Lemma D_1568c : decode_any W_1568c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15690 : bv 32 := 0x02010113.
Lemma F_15690 : fetch_word Ubsan.M.loaded_segments (0x1578c : word) = Some W_15690.
Proof. vm_refl. Qed.
Lemma D_15690 : decode_any W_15690 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15694 : bv 32 := 0x00008067.
Lemma F_15694 : fetch_word Ubsan.M.loaded_segments (0x15790 : word) = Some W_15694.
Proof. vm_refl. Qed.
Lemma D_15694 : decode_any W_15694 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1569c : bv 32 := 0xff010113.
Lemma F_1569c : fetch_word Ubsan.M.loaded_segments (0x15798 : word) = Some W_1569c.
Proof. vm_refl. Qed.
Lemma D_1569c : decode_any W_1569c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156a0 : bv 32 := 0x00113423.
Lemma F_156a0 : fetch_word Ubsan.M.loaded_segments (0x1579c : word) = Some W_156a0.
Proof. vm_refl. Qed.
Lemma D_156a0 : decode_any W_156a0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156a4 : bv 32 := 0x00813023.
Lemma F_156a4 : fetch_word Ubsan.M.loaded_segments (0x157a0 : word) = Some W_156a4.
Proof. vm_refl. Qed.
Lemma D_156a4 : decode_any W_156a4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156a8 : bv 32 := 0x098000ef.
Lemma F_156a8 : fetch_word Ubsan.M.loaded_segments (0x157a4 : word) = Some W_156a8.
Proof. vm_refl. Qed.
Lemma D_156a8 : decode_any W_156a8 = Some (Jal 1 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156ac : bv 32 := 0x04050263.
Lemma F_156ac : fetch_word Ubsan.M.loaded_segments (0x157a8 : word) = Some W_156ac.
Proof. vm_refl. Qed.
Lemma D_156ac : decode_any W_156ac = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156b0 : bv 32 := 0x00757593.
Lemma F_156b0 : fetch_word Ubsan.M.loaded_segments (0x157ac : word) = Some W_156b0.
Proof. vm_refl. Qed.
Lemma D_156b0 : decode_any W_156b0 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156b4 : bv 32 := 0x08059463.
Lemma F_156b4 : fetch_word Ubsan.M.loaded_segments (0x157b0 : word) = Some W_156b4.
Proof. vm_refl. Qed.
Lemma D_156b4 : decode_any W_156b4 = Some (Branch BC_NE 11 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156b8 : bv 32 := 0x01056583.
Lemma F_156b8 : fetch_word Ubsan.M.loaded_segments (0x157b4 : word) = Some W_156b8.
Proof. vm_refl. Qed.
Lemma D_156b8 : decode_any W_156b8 = Some (Load SZ4 false 11 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156bc : bv 32 := 0x00456603.
Lemma F_156bc : fetch_word Ubsan.M.loaded_segments (0x157b8 : word) = Some W_156bc.
Proof. vm_refl. Qed.
Lemma D_156bc : decode_any W_156bc = Some (Load SZ4 false 12 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156c0 : bv 32 := 0x00259593.
Lemma F_156c0 : fetch_word Ubsan.M.loaded_segments (0x157bc : word) = Some W_156c0.
Proof. vm_refl. Qed.
Lemma D_156c0 : decode_any W_156c0 = Some (ShiftImm ALU_SLL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156c4 : bv 32 := 0x02c596b3.
Lemma F_156c4 : fetch_word Ubsan.M.loaded_segments (0x157c0 : word) = Some W_156c4.
Proof. vm_refl. Qed.
Lemma D_156c4 : decode_any W_156c4 = Some (Mul M_MULH 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156c8 : bv 32 := 0x02c58633.
Lemma F_156c8 : fetch_word Ubsan.M.loaded_segments (0x157c4 : word) = Some W_156c8.
Proof. vm_refl. Qed.
Lemma D_156c8 : decode_any W_156c8 = Some (Mul M_MUL 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156cc : bv 32 := 0x43f65593.
Lemma F_156cc : fetch_word Ubsan.M.loaded_segments (0x157c8 : word) = Some W_156cc.
Proof. vm_refl. Qed.
Lemma D_156cc : decode_any W_156cc = Some (ShiftImm ALU_SRA 11 12 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156d0 : bv 32 := 0x06b69663.
Lemma F_156d0 : fetch_word Ubsan.M.loaded_segments (0x157cc : word) = Some W_156d0.
Proof. vm_refl. Qed.
Lemma D_156d0 : decode_any W_156d0 = Some (Branch BC_NE 13 11 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156d4 : bv 32 := 0x03853583.
Lemma F_156d4 : fetch_word Ubsan.M.loaded_segments (0x157d0 : word) = Some W_156d4.
Proof. vm_refl. Qed.
Lemma D_156d4 : decode_any W_156d4 = Some (Load SZ8 true 11 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156d8 : bv 32 := 0x00050413.
Lemma F_156d8 : fetch_word Ubsan.M.loaded_segments (0x157d4 : word) = Some W_156d8.
Proof. vm_refl. Qed.
Lemma D_156d8 : decode_any W_156d8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156dc : bv 32 := 0x00058513.
Lemma F_156dc : fetch_word Ubsan.M.loaded_segments (0x157d8 : word) = Some W_156dc.
Proof. vm_refl. Qed.
Lemma D_156dc : decode_any W_156dc = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156e0 : bv 32 := 0x00000593.
Lemma F_156e0 : fetch_word Ubsan.M.loaded_segments (0x157dc : word) = Some W_156e0.
Proof. vm_refl. Qed.
Lemma D_156e0 : decode_any W_156e0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156e4 : bv 32 := 0x7791b0ef.
Lemma F_156e4 : fetch_word Ubsan.M.loaded_segments (0x157e0 : word) = Some W_156e4.
Proof. vm_refl. Qed.
Lemma D_156e4 : decode_any W_156e4 = Some (Jal 1 114552, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156e8 : bv 32 := 0x00040513.
Lemma F_156e8 : fetch_word Ubsan.M.loaded_segments (0x157e4 : word) = Some W_156e8.
Proof. vm_refl. Qed.
Lemma D_156e8 : decode_any W_156e8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156ec : bv 32 := 0x0400006f.
Lemma F_156ec : fetch_word Ubsan.M.loaded_segments (0x157e8 : word) = Some W_156ec.
Proof. vm_refl. Qed.
Lemma D_156ec : decode_any W_156ec = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156f0 : bv 32 := 0x0001d517.
Lemma F_156f0 : fetch_word Ubsan.M.loaded_segments (0x157ec : word) = Some W_156f0.
Proof. vm_refl. Qed.
Lemma D_156f0 : decode_any W_156f0 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156f4 : bv 32 := 0x58453503.
Lemma F_156f4 : fetch_word Ubsan.M.loaded_segments (0x157f0 : word) = Some W_156f4.
Proof. vm_refl. Qed.
Lemma D_156f4 : decode_any W_156f4 = Some (Load SZ8 true 10 10 1412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156f8 : bv 32 := 0x00052503.
Lemma F_156f8 : fetch_word Ubsan.M.loaded_segments (0x157f4 : word) = Some W_156f8.
Proof. vm_refl. Qed.
Lemma D_156f8 : decode_any W_156f8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156fc : bv 32 := 0x00500593.
Lemma F_156fc : fetch_word Ubsan.M.loaded_segments (0x157f8 : word) = Some W_156fc.
Proof. vm_refl. Qed.
Lemma D_156fc : decode_any W_156fc = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15700 : bv 32 := 0x02a5c463.
Lemma F_15700 : fetch_word Ubsan.M.loaded_segments (0x157fc : word) = Some W_15700.
Proof. vm_refl. Qed.
Lemma D_15700 : decode_any W_15700 = Some (Branch BC_LT 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15704 : bv 32 := 0xffffb517.
Lemma F_15704 : fetch_word Ubsan.M.loaded_segments (0x15800 : word) = Some W_15704.
Proof. vm_refl. Qed.
Lemma D_15704 : decode_any W_15704 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15708 : bv 32 := 0xffffb597.
Lemma F_15708 : fetch_word Ubsan.M.loaded_segments (0x15804 : word) = Some W_15708.
Proof. vm_refl. Qed.
Lemma D_15708 : decode_any W_15708 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1570c : bv 32 := 0xcbd50513.
Lemma F_1570c : fetch_word Ubsan.M.loaded_segments (0x15808 : word) = Some W_1570c.
Proof. vm_refl. Qed.
Lemma D_1570c : decode_any W_1570c = Some (OpImm ALU_ADD 10 10 3261, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15710 : bv 32 := 0x0a558593.
Lemma F_15710 : fetch_word Ubsan.M.loaded_segments (0x1580c : word) = Some W_15710.
Proof. vm_refl. Qed.
Lemma D_15710 : decode_any W_15710 = Some (OpImm ALU_ADD 11 11 165, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15714 : bv 32 := 0x00000613.
Lemma F_15714 : fetch_word Ubsan.M.loaded_segments (0x15810 : word) = Some W_15714.
Proof. vm_refl. Qed.
Lemma D_15714 : decode_any W_15714 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15718 : bv 32 := 0x00813083.
Lemma F_15718 : fetch_word Ubsan.M.loaded_segments (0x15814 : word) = Some W_15718.
Proof. vm_refl. Qed.
Lemma D_15718 : decode_any W_15718 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1571c : bv 32 := 0x00013403.
Lemma F_1571c : fetch_word Ubsan.M.loaded_segments (0x15818 : word) = Some W_1571c.
Proof. vm_refl. Qed.
Lemma D_1571c : decode_any W_1571c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15720 : bv 32 := 0x01010113.
Lemma F_15720 : fetch_word Ubsan.M.loaded_segments (0x1581c : word) = Some W_15720.
Proof. vm_refl. Qed.
Lemma D_15720 : decode_any W_15720 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15724 : bv 32 := 0xd2dff06f.
Lemma F_15724 : fetch_word Ubsan.M.loaded_segments (0x15820 : word) = Some W_15724.
Proof. vm_refl. Qed.
Lemma D_15724 : decode_any W_15724 = Some (Jal 0 2096428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1572c : bv 32 := 0x00813083.
Lemma F_1572c : fetch_word Ubsan.M.loaded_segments (0x15828 : word) = Some W_1572c.
Proof. vm_refl. Qed.
Lemma D_1572c : decode_any W_1572c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15730 : bv 32 := 0x00013403.
Lemma F_15730 : fetch_word Ubsan.M.loaded_segments (0x1582c : word) = Some W_15730.
Proof. vm_refl. Qed.
Lemma D_15730 : decode_any W_15730 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15734 : bv 32 := 0x01010113.
Lemma F_15734 : fetch_word Ubsan.M.loaded_segments (0x15830 : word) = Some W_15734.
Proof. vm_refl. Qed.
Lemma D_15734 : decode_any W_15734 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15738 : bv 32 := 0x00008067.
Lemma F_15738 : fetch_word Ubsan.M.loaded_segments (0x15834 : word) = Some W_15738.
Proof. vm_refl. Qed.
Lemma D_15738 : decode_any W_15738 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15740 : bv 32 := 0xfe010113.
Lemma F_15740 : fetch_word Ubsan.M.loaded_segments (0x1583c : word) = Some W_15740.
Proof. vm_refl. Qed.
Lemma D_15740 : decode_any W_15740 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15744 : bv 32 := 0x00113c23.
Lemma F_15744 : fetch_word Ubsan.M.loaded_segments (0x15840 : word) = Some W_15744.
Proof. vm_refl. Qed.
Lemma D_15744 : decode_any W_15744 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15748 : bv 32 := 0x00813823.
Lemma F_15748 : fetch_word Ubsan.M.loaded_segments (0x15844 : word) = Some W_15748.
Proof. vm_refl. Qed.
Lemma D_15748 : decode_any W_15748 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1574c : bv 32 := 0x00913423.
Lemma F_1574c : fetch_word Ubsan.M.loaded_segments (0x15848 : word) = Some W_1574c.
Proof. vm_refl. Qed.
Lemma D_1574c : decode_any W_1574c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15750 : bv 32 := 0x00058493.
Lemma F_15750 : fetch_word Ubsan.M.loaded_segments (0x1584c : word) = Some W_15750.
Proof. vm_refl. Qed.
Lemma D_15750 : decode_any W_15750 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15754 : bv 32 := 0x134000ef.
Lemma F_15754 : fetch_word Ubsan.M.loaded_segments (0x15850 : word) = Some W_15754.
Proof. vm_refl. Qed.
Lemma D_15754 : decode_any W_15754 = Some (Jal 1 308, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15758 : bv 32 := 0x04050863.
Lemma F_15758 : fetch_word Ubsan.M.loaded_segments (0x15854 : word) = Some W_15758.
Proof. vm_refl. Qed.
Lemma D_15758 : decode_any W_15758 = Some (Branch BC_EQ 10 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1575c : bv 32 := 0x00050413.
Lemma F_1575c : fetch_word Ubsan.M.loaded_segments (0x15858 : word) = Some W_1575c.
Proof. vm_refl. Qed.
Lemma D_1575c : decode_any W_1575c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15760 : bv 32 := 0x00757513.
Lemma F_15760 : fetch_word Ubsan.M.loaded_segments (0x1585c : word) = Some W_15760.
Proof. vm_refl. Qed.
Lemma D_15760 : decode_any W_15760 = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15764 : bv 32 := 0x12051063.
Lemma F_15764 : fetch_word Ubsan.M.loaded_segments (0x15860 : word) = Some W_15764.
Proof. vm_refl. Qed.
Lemma D_15764 : decode_any W_15764 = Some (Branch BC_NE 10 0 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15768 : bv 32 := 0x01042503.
Lemma F_15768 : fetch_word Ubsan.M.loaded_segments (0x15864 : word) = Some W_15768.
Proof. vm_refl. Qed.
Lemma D_15768 : decode_any W_15768 = Some (Load SZ4 true 10 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1576c : bv 32 := 0x00251513.
Lemma F_1576c : fetch_word Ubsan.M.loaded_segments (0x15868 : word) = Some W_1576c.
Proof. vm_refl. Qed.
Lemma D_1576c : decode_any W_1576c = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15770 : bv 32 := 0x029515b3.
Lemma F_15770 : fetch_word Ubsan.M.loaded_segments (0x1586c : word) = Some W_15770.
Proof. vm_refl. Qed.
Lemma D_15770 : decode_any W_15770 = Some (Mul M_MULH 11 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15774 : bv 32 := 0x02950533.
Lemma F_15774 : fetch_word Ubsan.M.loaded_segments (0x15870 : word) = Some W_15774.
Proof. vm_refl. Qed.
Lemma D_15774 : decode_any W_15774 = Some (Mul M_MUL 10 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15778 : bv 32 := 0x43f55613.
Lemma F_15778 : fetch_word Ubsan.M.loaded_segments (0x15874 : word) = Some W_15778.
Proof. vm_refl. Qed.
Lemma D_15778 : decode_any W_15778 = Some (ShiftImm ALU_SRA 12 10 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1577c : bv 32 := 0x10c59463.
Lemma F_1577c : fetch_word Ubsan.M.loaded_segments (0x15878 : word) = Some W_1577c.
Proof. vm_refl. Qed.
Lemma D_1577c : decode_any W_1577c = Some (Branch BC_NE 11 12 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15780 : bv 32 := 0x0001e597.
Lemma F_15780 : fetch_word Ubsan.M.loaded_segments (0x1587c : word) = Some W_15780.
Proof. vm_refl. Qed.
Lemma D_15780 : decode_any W_15780 = Some (Auipc 11 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15784 : bv 32 := 0x57458493.
Lemma F_15784 : fetch_word Ubsan.M.loaded_segments (0x15880 : word) = Some W_15784.
Proof. vm_refl. Qed.
Lemma D_15784 : decode_any W_15784 = Some (OpImm ALU_ADD 9 11 1396, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15788 : bv 32 := 0x0004b583.
Lemma F_15788 : fetch_word Ubsan.M.loaded_segments (0x15884 : word) = Some W_15788.
Proof. vm_refl. Qed.
Lemma D_15788 : decode_any W_15788 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1578c : bv 32 := 0x000580e7.
Lemma F_1578c : fetch_word Ubsan.M.loaded_segments (0x15888 : word) = Some W_1578c.
Proof. vm_refl. Qed.
Lemma D_1578c : decode_any W_1578c = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15790 : bv 32 := 0x04050a63.
Lemma F_15790 : fetch_word Ubsan.M.loaded_segments (0x1588c : word) = Some W_15790.
Proof. vm_refl. Qed.
Lemma D_15790 : decode_any W_15790 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15794 : bv 32 := 0x02a43c23.
Lemma F_15794 : fetch_word Ubsan.M.loaded_segments (0x15890 : word) = Some W_15794.
Proof. vm_refl. Qed.
Lemma D_15794 : decode_any W_15794 = Some (Store SZ8 8 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15798 : bv 32 := 0x00040513.
Lemma F_15798 : fetch_word Ubsan.M.loaded_segments (0x15894 : word) = Some W_15798.
Proof. vm_refl. Qed.
Lemma D_15798 : decode_any W_15798 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1579c : bv 32 := 0x00000593.
Lemma F_1579c : fetch_word Ubsan.M.loaded_segments (0x15898 : word) = Some W_1579c.
Proof. vm_refl. Qed.
Lemma D_1579c : decode_any W_1579c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157a0 : bv 32 := 0x070020ef.
Lemma F_157a0 : fetch_word Ubsan.M.loaded_segments (0x1589c : word) = Some W_157a0.
Proof. vm_refl. Qed.
Lemma D_157a0 : decode_any W_157a0 = Some (Jal 1 8304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157a4 : bv 32 := 0x0c80006f.
Lemma F_157a4 : fetch_word Ubsan.M.loaded_segments (0x158a0 : word) = Some W_157a4.
Proof. vm_refl. Qed.
Lemma D_157a4 : decode_any W_157a4 = Some (Jal 0 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157a8 : bv 32 := 0x0001d517.
Lemma F_157a8 : fetch_word Ubsan.M.loaded_segments (0x158a4 : word) = Some W_157a8.
Proof. vm_refl. Qed.
Lemma D_157a8 : decode_any W_157a8 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157ac : bv 32 := 0x4cc53503.
Lemma F_157ac : fetch_word Ubsan.M.loaded_segments (0x158a8 : word) = Some W_157ac.
Proof. vm_refl. Qed.
Lemma D_157ac : decode_any W_157ac = Some (Load SZ8 true 10 10 1228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157b0 : bv 32 := 0x00052503.
Lemma F_157b0 : fetch_word Ubsan.M.loaded_segments (0x158ac : word) = Some W_157b0.
Proof. vm_refl. Qed.
Lemma D_157b0 : decode_any W_157b0 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157b4 : bv 32 := 0x00500593.
Lemma F_157b4 : fetch_word Ubsan.M.loaded_segments (0x158b0 : word) = Some W_157b4.
Proof. vm_refl. Qed.
Lemma D_157b4 : decode_any W_157b4 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157b8 : bv 32 := 0x0aa5c863.
Lemma F_157b8 : fetch_word Ubsan.M.loaded_segments (0x158b4 : word) = Some W_157b8.
Proof. vm_refl. Qed.
Lemma D_157b8 : decode_any W_157b8 = Some (Branch BC_LT 11 10 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157bc : bv 32 := 0xffffb517.
Lemma F_157bc : fetch_word Ubsan.M.loaded_segments (0x158b8 : word) = Some W_157bc.
Proof. vm_refl. Qed.
Lemma D_157bc : decode_any W_157bc = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157c0 : bv 32 := 0xffffb597.
Lemma F_157c0 : fetch_word Ubsan.M.loaded_segments (0x158bc : word) = Some W_157c0.
Proof. vm_refl. Qed.
Lemma D_157c0 : decode_any W_157c0 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157c4 : bv 32 := 0xc0550513.
Lemma F_157c4 : fetch_word Ubsan.M.loaded_segments (0x158c0 : word) = Some W_157c4.
Proof. vm_refl. Qed.
Lemma D_157c4 : decode_any W_157c4 = Some (OpImm ALU_ADD 10 10 3077, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157c8 : bv 32 := 0xdb558593.
Lemma F_157c8 : fetch_word Ubsan.M.loaded_segments (0x158c4 : word) = Some W_157c8.
Proof. vm_refl. Qed.
Lemma D_157c8 : decode_any W_157c8 = Some (OpImm ALU_ADD 11 11 3509, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157cc : bv 32 := 0x00000613.
Lemma F_157cc : fetch_word Ubsan.M.loaded_segments (0x158c8 : word) = Some W_157cc.
Proof. vm_refl. Qed.
Lemma D_157cc : decode_any W_157cc = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157d0 : bv 32 := 0x01813083.
Lemma F_157d0 : fetch_word Ubsan.M.loaded_segments (0x158cc : word) = Some W_157d0.
Proof. vm_refl. Qed.
Lemma D_157d0 : decode_any W_157d0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157d4 : bv 32 := 0x01013403.
Lemma F_157d4 : fetch_word Ubsan.M.loaded_segments (0x158d0 : word) = Some W_157d4.
Proof. vm_refl. Qed.
Lemma D_157d4 : decode_any W_157d4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157d8 : bv 32 := 0x00813483.
Lemma F_157d8 : fetch_word Ubsan.M.loaded_segments (0x158d4 : word) = Some W_157d8.
Proof. vm_refl. Qed.
Lemma D_157d8 : decode_any W_157d8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157dc : bv 32 := 0x02010113.
Lemma F_157dc : fetch_word Ubsan.M.loaded_segments (0x158d8 : word) = Some W_157dc.
Proof. vm_refl. Qed.
Lemma D_157dc : decode_any W_157dc = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157e0 : bv 32 := 0xc71ff06f.
Lemma F_157e0 : fetch_word Ubsan.M.loaded_segments (0x158dc : word) = Some W_157e0.
Proof. vm_refl. Qed.
Lemma D_157e0 : decode_any W_157e0 = Some (Jal 0 2096240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157e4 : bv 32 := 0x01440513.
Lemma F_157e4 : fetch_word Ubsan.M.loaded_segments (0x158e0 : word) = Some W_157e4.
Proof. vm_refl. Qed.
Lemma D_157e4 : decode_any W_157e4 = Some (OpImm ALU_ADD 10 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157e8 : bv 32 := 0xfff00593.
Lemma F_157e8 : fetch_word Ubsan.M.loaded_segments (0x158e4 : word) = Some W_157e8.
Proof. vm_refl. Qed.
Lemma D_157e8 : decode_any W_157e8 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157ec : bv 32 := 0x06b5252f.
Lemma F_157ec : fetch_word Ubsan.M.loaded_segments (0x158e8 : word) = Some W_157ec.
Proof. vm_refl. Qed.
Lemma D_157ec : decode_any W_157ec = Some (Amo AMO_ADD AW true true 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157f0 : bv 32 := 0x00100593.
Lemma F_157f0 : fetch_word Ubsan.M.loaded_segments (0x158ec : word) = Some W_157f0.
Proof. vm_refl. Qed.
Lemma D_157f0 : decode_any W_157f0 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157f4 : bv 32 := 0x04b51063.
Lemma F_157f4 : fetch_word Ubsan.M.loaded_segments (0x158f0 : word) = Some W_157f4.
Proof. vm_refl. Qed.
Lemma D_157f4 : decode_any W_157f4 = Some (Branch BC_NE 10 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157f8 : bv 32 := 0x03843503.
Lemma F_157f8 : fetch_word Ubsan.M.loaded_segments (0x158f4 : word) = Some W_157f8.
Proof. vm_refl. Qed.
Lemma D_157f8 : decode_any W_157f8 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157fc : bv 32 := 0x00050663.
Lemma F_157fc : fetch_word Ubsan.M.loaded_segments (0x158f8 : word) = Some W_157fc.
Proof. vm_refl. Qed.
Lemma D_157fc : decode_any W_157fc = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15808 : bv 32 := 0x02843503.
Lemma F_15808 : fetch_word Ubsan.M.loaded_segments (0x15904 : word) = Some W_15808.
Proof. vm_refl. Qed.
Lemma D_15808 : decode_any W_15808 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1580c : bv 32 := 0x00050463.
Lemma F_1580c : fetch_word Ubsan.M.loaded_segments (0x15908 : word) = Some W_1580c.
Proof. vm_refl. Qed.
Lemma D_1580c : decode_any W_1580c = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15814 : bv 32 := 0x03043503.
Lemma F_15814 : fetch_word Ubsan.M.loaded_segments (0x15910 : word) = Some W_15814.
Proof. vm_refl. Qed.
Lemma D_15814 : decode_any W_15814 = Some (Load SZ8 true 10 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15818 : bv 32 := 0x00a13023.
Lemma F_15818 : fetch_word Ubsan.M.loaded_segments (0x15914 : word) = Some W_15818.
Proof. vm_refl. Qed.
Lemma D_15818 : decode_any W_15818 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1581c : bv 32 := 0x00050863.
Lemma F_1581c : fetch_word Ubsan.M.loaded_segments (0x15918 : word) = Some W_1581c.
Proof. vm_refl. Qed.
Lemma D_1581c : decode_any W_1581c = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1582c : bv 32 := 0x00040513.
Lemma F_1582c : fetch_word Ubsan.M.loaded_segments (0x15928 : word) = Some W_1582c.
Proof. vm_refl. Qed.
Lemma D_1582c : decode_any W_1582c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15830 : bv 32 := 0x0f5140ef.
Lemma F_15830 : fetch_word Ubsan.M.loaded_segments (0x1592c : word) = Some W_15830.
Proof. vm_refl. Qed.
Lemma D_15830 : decode_any W_15830 = Some (Jal 1 84212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15834 : bv 32 := 0x0001d517.
Lemma F_15834 : fetch_word Ubsan.M.loaded_segments (0x15930 : word) = Some W_15834.
Proof. vm_refl. Qed.
Lemma D_15834 : decode_any W_15834 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15838 : bv 32 := 0x44053503.
Lemma F_15838 : fetch_word Ubsan.M.loaded_segments (0x15934 : word) = Some W_15838.
Proof. vm_refl. Qed.
Lemma D_15838 : decode_any W_15838 = Some (Load SZ8 true 10 10 1088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1583c : bv 32 := 0x00052503.
Lemma F_1583c : fetch_word Ubsan.M.loaded_segments (0x15938 : word) = Some W_1583c.
Proof. vm_refl. Qed.
Lemma D_1583c : decode_any W_1583c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15840 : bv 32 := 0x00500593.
Lemma F_15840 : fetch_word Ubsan.M.loaded_segments (0x1593c : word) = Some W_15840.
Proof. vm_refl. Qed.
Lemma D_15840 : decode_any W_15840 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15844 : bv 32 := 0x02a5c263.
Lemma F_15844 : fetch_word Ubsan.M.loaded_segments (0x15940 : word) = Some W_15844.
Proof. vm_refl. Qed.
Lemma D_15844 : decode_any W_15844 = Some (Branch BC_LT 11 10 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15848 : bv 32 := 0xffffb517.
Lemma F_15848 : fetch_word Ubsan.M.loaded_segments (0x15944 : word) = Some W_15848.
Proof. vm_refl. Qed.
Lemma D_15848 : decode_any W_15848 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1584c : bv 32 := 0xffffb597.
Lemma F_1584c : fetch_word Ubsan.M.loaded_segments (0x15948 : word) = Some W_1584c.
Proof. vm_refl. Qed.
Lemma D_1584c : decode_any W_1584c = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15850 : bv 32 := 0x71550513.
Lemma F_15850 : fetch_word Ubsan.M.loaded_segments (0x1594c : word) = Some W_15850.
Proof. vm_refl. Qed.
Lemma D_15850 : decode_any W_15850 = Some (OpImm ALU_ADD 10 10 1813, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15854 : bv 32 := 0xd2958593.
Lemma F_15854 : fetch_word Ubsan.M.loaded_segments (0x15950 : word) = Some W_15854.
Proof. vm_refl. Qed.
Lemma D_15854 : decode_any W_15854 = Some (OpImm ALU_ADD 11 11 3369, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15858 : bv 32 := 0x00000613.
Lemma F_15858 : fetch_word Ubsan.M.loaded_segments (0x15954 : word) = Some W_15858.
Proof. vm_refl. Qed.
Lemma D_15858 : decode_any W_15858 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1585c : bv 32 := 0xbf5ff0ef.
Lemma F_1585c : fetch_word Ubsan.M.loaded_segments (0x15958 : word) = Some W_1585c.
Proof. vm_refl. Qed.
Lemma D_1585c : decode_any W_1585c = Some (Jal 1 2096116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15860 : bv 32 := 0x00050413.
Lemma F_15860 : fetch_word Ubsan.M.loaded_segments (0x1595c : word) = Some W_15860.
Proof. vm_refl. Qed.
Lemma D_15860 : decode_any W_15860 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15864 : bv 32 := 0x0080006f.
Lemma F_15864 : fetch_word Ubsan.M.loaded_segments (0x15960 : word) = Some W_15864.
Proof. vm_refl. Qed.
Lemma D_15864 : decode_any W_15864 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1586c : bv 32 := 0x00040513.
Lemma F_1586c : fetch_word Ubsan.M.loaded_segments (0x15968 : word) = Some W_1586c.
Proof. vm_refl. Qed.
Lemma D_1586c : decode_any W_1586c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15870 : bv 32 := 0x01813083.
Lemma F_15870 : fetch_word Ubsan.M.loaded_segments (0x1596c : word) = Some W_15870.
Proof. vm_refl. Qed.
Lemma D_15870 : decode_any W_15870 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15874 : bv 32 := 0x01013403.
Lemma F_15874 : fetch_word Ubsan.M.loaded_segments (0x15970 : word) = Some W_15874.
Proof. vm_refl. Qed.
Lemma D_15874 : decode_any W_15874 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15878 : bv 32 := 0x00813483.
Lemma F_15878 : fetch_word Ubsan.M.loaded_segments (0x15974 : word) = Some W_15878.
Proof. vm_refl. Qed.
Lemma D_15878 : decode_any W_15878 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1587c : bv 32 := 0x02010113.
Lemma F_1587c : fetch_word Ubsan.M.loaded_segments (0x15978 : word) = Some W_1587c.
Proof. vm_refl. Qed.
Lemma D_1587c : decode_any W_1587c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15880 : bv 32 := 0x00008067.
Lemma F_15880 : fetch_word Ubsan.M.loaded_segments (0x1597c : word) = Some W_15880.
Proof. vm_refl. Qed.
Lemma D_15880 : decode_any W_15880 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15888 : bv 32 := 0xfd010113.
Lemma F_15888 : fetch_word Ubsan.M.loaded_segments (0x15984 : word) = Some W_15888.
Proof. vm_refl. Qed.
Lemma D_15888 : decode_any W_15888 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1588c : bv 32 := 0x02113423.
Lemma F_1588c : fetch_word Ubsan.M.loaded_segments (0x15988 : word) = Some W_1588c.
Proof. vm_refl. Qed.
Lemma D_1588c : decode_any W_1588c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15890 : bv 32 := 0x02813023.
Lemma F_15890 : fetch_word Ubsan.M.loaded_segments (0x1598c : word) = Some W_15890.
Proof. vm_refl. Qed.
Lemma D_15890 : decode_any W_15890 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15894 : bv 32 := 0x00913c23.
Lemma F_15894 : fetch_word Ubsan.M.loaded_segments (0x15990 : word) = Some W_15894.
Proof. vm_refl. Qed.
Lemma D_15894 : decode_any W_15894 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15898 : bv 32 := 0x01213823.
Lemma F_15898 : fetch_word Ubsan.M.loaded_segments (0x15994 : word) = Some W_15898.
Proof. vm_refl. Qed.
Lemma D_15898 : decode_any W_15898 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1589c : bv 32 := 0x01313423.
Lemma F_1589c : fetch_word Ubsan.M.loaded_segments (0x15998 : word) = Some W_1589c.
Proof. vm_refl. Qed.
Lemma D_1589c : decode_any W_1589c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158a0 : bv 32 := 0x01413023.
Lemma F_158a0 : fetch_word Ubsan.M.loaded_segments (0x1599c : word) = Some W_158a0.
Proof. vm_refl. Qed.
Lemma D_158a0 : decode_any W_158a0 = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158a4 : bv 32 := 0x02000693.
Lemma F_158a4 : fetch_word Ubsan.M.loaded_segments (0x159a0 : word) = Some W_158a4.
Proof. vm_refl. Qed.
Lemma D_158a4 : decode_any W_158a4 = Some (OpImm ALU_ADD 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158a8 : bv 32 := 0x14c6ea63.
Lemma F_158a8 : fetch_word Ubsan.M.loaded_segments (0x159a4 : word) = Some W_158a8.
Proof. vm_refl. Qed.
Lemma D_158a8 : decode_any W_158a8 = Some (Branch BC_LTU 13 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158ac : bv 32 := 0x101016b7.
Lemma F_158ac : fetch_word Ubsan.M.loaded_segments (0x159a8 : word) = Some W_158ac.
Proof. vm_refl. Qed.
Lemma D_158ac : decode_any W_158ac = Some (Lui 13 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158b0 : bv 32 := 0x00469693.
Lemma F_158b0 : fetch_word Ubsan.M.loaded_segments (0x159ac : word) = Some W_158b0.
Proof. vm_refl. Qed.
Lemma D_158b0 : decode_any W_158b0 = Some (ShiftImm ALU_SLL 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158b4 : bv 32 := 0x11668693.
Lemma F_158b4 : fetch_word Ubsan.M.loaded_segments (0x159b0 : word) = Some W_158b4.
Proof. vm_refl. Qed.
Lemma D_158b4 : decode_any W_158b4 = Some (OpImm ALU_ADD 13 13 278, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158b8 : bv 32 := 0x00c6d6b3.
Lemma F_158b8 : fetch_word Ubsan.M.loaded_segments (0x159b4 : word) = Some W_158b8.
Proof. vm_refl. Qed.
Lemma D_158b8 : decode_any W_158b8 = Some (Op ALU_SRL 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158bc : bv 32 := 0x0016f693.
Lemma F_158bc : fetch_word Ubsan.M.loaded_segments (0x159b8 : word) = Some W_158bc.
Proof. vm_refl. Qed.
Lemma D_158bc : decode_any W_158bc = Some (OpImm ALU_AND 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158c0 : bv 32 := 0x12068e63.
Lemma F_158c0 : fetch_word Ubsan.M.loaded_segments (0x159bc : word) = Some W_158c0.
Proof. vm_refl. Qed.
Lemma D_158c0 : decode_any W_158c0 = Some (Branch BC_EQ 13 0 316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158c4 : bv 32 := 0x06a05a63.
Lemma F_158c4 : fetch_word Ubsan.M.loaded_segments (0x159c0 : word) = Some W_158c4.
Proof. vm_refl. Qed.
Lemma D_158c4 : decode_any W_158c4 = Some (Branch BC_GE 0 10 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158c8 : bv 32 := 0x08b05c63.
Lemma F_158c8 : fetch_word Ubsan.M.loaded_segments (0x159c4 : word) = Some W_158c8.
Proof. vm_refl. Qed.
Lemma D_158c8 : decode_any W_158c8 = Some (Branch BC_GE 0 11 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158cc : bv 32 := 0x02a606b3.
Lemma F_158cc : fetch_word Ubsan.M.loaded_segments (0x159c8 : word) = Some W_158cc.
Proof. vm_refl. Qed.
Lemma D_158cc : decode_any W_158cc = Some (Mul M_MUL 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158d0 : bv 32 := 0x20000737.
Lemma F_158d0 : fetch_word Ubsan.M.loaded_segments (0x159cc : word) = Some W_158d0.
Proof. vm_refl. Qed.
Lemma D_158d0 : decode_any W_158d0 = Some (Lui 14 131072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158d4 : bv 32 := 0xfe17071b.
Lemma F_158d4 : fetch_word Ubsan.M.loaded_segments (0x159d0 : word) = Some W_158d4.
Proof. vm_refl. Qed.
Lemma D_158d4 : decode_any W_158d4 = Some (OpImm32 14 14 4065, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158d8 : bv 32 := 0x0ae6e863.
Lemma F_158d8 : fetch_word Ubsan.M.loaded_segments (0x159d4 : word) = Some W_158d8.
Proof. vm_refl. Qed.
Lemma D_158d8 : decode_any W_158d8 = Some (Branch BC_LTU 13 14 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15988 : bv 32 := 0x01f68693.
Lemma F_15988 : fetch_word Ubsan.M.loaded_segments (0x15a84 : word) = Some W_15988.
Proof. vm_refl. Qed.
Lemma D_15988 : decode_any W_15988 = Some (OpImm ALU_ADD 13 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1598c : bv 32 := 0x0056da13.
Lemma F_1598c : fetch_word Ubsan.M.loaded_segments (0x15a88 : word) = Some W_1598c.
Proof. vm_refl. Qed.
Lemma D_1598c : decode_any W_1598c = Some (ShiftImm ALU_SRL 20 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15990 : bv 32 := 0x02ba06b3.
Lemma F_15990 : fetch_word Ubsan.M.loaded_segments (0x15a8c : word) = Some W_15990.
Proof. vm_refl. Qed.
Lemma D_15990 : decode_any W_15990 = Some (Mul M_MUL 13 20 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15994 : bv 32 := 0x00269693.
Lemma F_15994 : fetch_word Ubsan.M.loaded_segments (0x15a90 : word) = Some W_15994.
Proof. vm_refl. Qed.
Lemma D_15994 : decode_any W_15994 = Some (ShiftImm ALU_SLL 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15998 : bv 32 := 0x01f6d713.
Lemma F_15998 : fetch_word Ubsan.M.loaded_segments (0x15a94 : word) = Some W_15998.
Proof. vm_refl. Qed.
Lemma D_15998 : decode_any W_15998 = Some (ShiftImm ALU_SRL 14 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1599c : bv 32 := 0x0a070463.
Lemma F_1599c : fetch_word Ubsan.M.loaded_segments (0x15a98 : word) = Some W_1599c.
Proof. vm_refl. Qed.
Lemma D_1599c : decode_any W_1599c = Some (Branch BC_EQ 14 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159fc : bv 32 := 0x0001d517.
Lemma F_159fc : fetch_word Ubsan.M.loaded_segments (0x15af8 : word) = Some W_159fc.
Proof. vm_refl. Qed.
Lemma D_159fc : decode_any W_159fc = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a00 : bv 32 := 0x27853503.
Lemma F_15a00 : fetch_word Ubsan.M.loaded_segments (0x15afc : word) = Some W_15a00.
Proof. vm_refl. Qed.
Lemma D_15a00 : decode_any W_15a00 = Some (Load SZ8 true 10 10 632, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a04 : bv 32 := 0x00052503.
Lemma F_15a04 : fetch_word Ubsan.M.loaded_segments (0x15b00 : word) = Some W_15a04.
Proof. vm_refl. Qed.
Lemma D_15a04 : decode_any W_15a04 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a08 : bv 32 := 0x00500593.
Lemma F_15a08 : fetch_word Ubsan.M.loaded_segments (0x15b04 : word) = Some W_15a08.
Proof. vm_refl. Qed.
Lemma D_15a08 : decode_any W_15a08 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a0c : bv 32 := 0x0ca5c663.
Lemma F_15a0c : fetch_word Ubsan.M.loaded_segments (0x15b08 : word) = Some W_15a0c.
Proof. vm_refl. Qed.
Lemma D_15a0c : decode_any W_15a0c = Some (Branch BC_LT 11 10 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a10 : bv 32 := 0xffffb517.
Lemma F_15a10 : fetch_word Ubsan.M.loaded_segments (0x15b0c : word) = Some W_15a10.
Proof. vm_refl. Qed.
Lemma D_15a10 : decode_any W_15a10 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a14 : bv 32 := 0xffffb597.
Lemma F_15a14 : fetch_word Ubsan.M.loaded_segments (0x15b10 : word) = Some W_15a14.
Proof. vm_refl. Qed.
Lemma D_15a14 : decode_any W_15a14 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a18 : bv 32 := 0xa5a50513.
Lemma F_15a18 : fetch_word Ubsan.M.loaded_segments (0x15b14 : word) = Some W_15a18.
Proof. vm_refl. Qed.
Lemma D_15a18 : decode_any W_15a18 = Some (OpImm ALU_ADD 10 10 2650, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a1c : bv 32 := 0xe5a58593.
Lemma F_15a1c : fetch_word Ubsan.M.loaded_segments (0x15b18 : word) = Some W_15a1c.
Proof. vm_refl. Qed.
Lemma D_15a1c : decode_any W_15a1c = Some (OpImm ALU_ADD 11 11 3674, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a20 : bv 32 := 0x00000613.
Lemma F_15a20 : fetch_word Ubsan.M.loaded_segments (0x15b1c : word) = Some W_15a20.
Proof. vm_refl. Qed.
Lemma D_15a20 : decode_any W_15a20 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a24 : bv 32 := 0x02813083.
Lemma F_15a24 : fetch_word Ubsan.M.loaded_segments (0x15b20 : word) = Some W_15a24.
Proof. vm_refl. Qed.
Lemma D_15a24 : decode_any W_15a24 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a28 : bv 32 := 0x02013403.
Lemma F_15a28 : fetch_word Ubsan.M.loaded_segments (0x15b24 : word) = Some W_15a28.
Proof. vm_refl. Qed.
Lemma D_15a28 : decode_any W_15a28 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a2c : bv 32 := 0x01813483.
Lemma F_15a2c : fetch_word Ubsan.M.loaded_segments (0x15b28 : word) = Some W_15a2c.
Proof. vm_refl. Qed.
Lemma D_15a2c : decode_any W_15a2c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a30 : bv 32 := 0x01013903.
Lemma F_15a30 : fetch_word Ubsan.M.loaded_segments (0x15b2c : word) = Some W_15a30.
Proof. vm_refl. Qed.
Lemma D_15a30 : decode_any W_15a30 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a34 : bv 32 := 0x00813983.
Lemma F_15a34 : fetch_word Ubsan.M.loaded_segments (0x15b30 : word) = Some W_15a34.
Proof. vm_refl. Qed.
Lemma D_15a34 : decode_any W_15a34 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a38 : bv 32 := 0x00013a03.
Lemma F_15a38 : fetch_word Ubsan.M.loaded_segments (0x15b34 : word) = Some W_15a38.
Proof. vm_refl. Qed.
Lemma D_15a38 : decode_any W_15a38 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a3c : bv 32 := 0x03010113.
Lemma F_15a3c : fetch_word Ubsan.M.loaded_segments (0x15b38 : word) = Some W_15a3c.
Proof. vm_refl. Qed.
Lemma D_15a3c : decode_any W_15a3c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a40 : bv 32 := 0xa11ff06f.
Lemma F_15a40 : fetch_word Ubsan.M.loaded_segments (0x15b3c : word) = Some W_15a40.
Proof. vm_refl. Qed.
Lemma D_15a40 : decode_any W_15a40 = Some (Jal 0 2095632, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a44 : bv 32 := 0x04000737.
Lemma F_15a44 : fetch_word Ubsan.M.loaded_segments (0x15b40 : word) = Some W_15a44.
Proof. vm_refl. Qed.
Lemma D_15a44 : decode_any W_15a44 = Some (Lui 14 16384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a48 : bv 32 := 0x0017071b.
Lemma F_15a48 : fetch_word Ubsan.M.loaded_segments (0x15b44 : word) = Some W_15a48.
Proof. vm_refl. Qed.
Lemma D_15a48 : decode_any W_15a48 = Some (OpImm32 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a4c : bv 32 := 0x02e6e663.
Lemma F_15a4c : fetch_word Ubsan.M.loaded_segments (0x15b48 : word) = Some W_15a4c.
Proof. vm_refl. Qed.
Lemma D_15a4c : decode_any W_15a4c = Some (Branch BC_LTU 13 14 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a50 : bv 32 := 0x0001d517.
Lemma F_15a50 : fetch_word Ubsan.M.loaded_segments (0x15b4c : word) = Some W_15a50.
Proof. vm_refl. Qed.
Lemma D_15a50 : decode_any W_15a50 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a54 : bv 32 := 0x22453503.
Lemma F_15a54 : fetch_word Ubsan.M.loaded_segments (0x15b50 : word) = Some W_15a54.
Proof. vm_refl. Qed.
Lemma D_15a54 : decode_any W_15a54 = Some (Load SZ8 true 10 10 548, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a58 : bv 32 := 0x00052503.
Lemma F_15a58 : fetch_word Ubsan.M.loaded_segments (0x15b54 : word) = Some W_15a58.
Proof. vm_refl. Qed.
Lemma D_15a58 : decode_any W_15a58 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a5c : bv 32 := 0x00500593.
Lemma F_15a5c : fetch_word Ubsan.M.loaded_segments (0x15b58 : word) = Some W_15a5c.
Proof. vm_refl. Qed.
Lemma D_15a5c : decode_any W_15a5c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a60 : bv 32 := 0x06a5cc63.
Lemma F_15a60 : fetch_word Ubsan.M.loaded_segments (0x15b5c : word) = Some W_15a60.
Proof. vm_refl. Qed.
Lemma D_15a60 : decode_any W_15a60 = Some (Branch BC_LT 11 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a64 : bv 32 := 0xffffb517.
Lemma F_15a64 : fetch_word Ubsan.M.loaded_segments (0x15b60 : word) = Some W_15a64.
Proof. vm_refl. Qed.
Lemma D_15a64 : decode_any W_15a64 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a68 : bv 32 := 0xffffb597.
Lemma F_15a68 : fetch_word Ubsan.M.loaded_segments (0x15b64 : word) = Some W_15a68.
Proof. vm_refl. Qed.
Lemma D_15a68 : decode_any W_15a68 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a6c : bv 32 := 0x8be50513.
Lemma F_15a6c : fetch_word Ubsan.M.loaded_segments (0x15b68 : word) = Some W_15a6c.
Proof. vm_refl. Qed.
Lemma D_15a6c : decode_any W_15a6c = Some (OpImm ALU_ADD 10 10 2238, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a70 : bv 32 := 0xe0658593.
Lemma F_15a70 : fetch_word Ubsan.M.loaded_segments (0x15b6c : word) = Some W_15a70.
Proof. vm_refl. Qed.
Lemma D_15a70 : decode_any W_15a70 = Some (OpImm ALU_ADD 11 11 3590, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a74 : bv 32 := 0x0600006f.
Lemma F_15a74 : fetch_word Ubsan.M.loaded_segments (0x15b70 : word) = Some W_15a74.
Proof. vm_refl. Qed.
Lemma D_15a74 : decode_any W_15a74 = Some (Jal 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a78 : bv 32 := 0x000056b7.
Lemma F_15a78 : fetch_word Ubsan.M.loaded_segments (0x15b74 : word) = Some W_15a78.
Proof. vm_refl. Qed.
Lemma D_15a78 : decode_any W_15a78 = Some (Lui 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a7c : bv 32 := 0xe216869b.
Lemma F_15a7c : fetch_word Ubsan.M.loaded_segments (0x15b78 : word) = Some W_15a7c.
Proof. vm_refl. Qed.
Lemma D_15a7c : decode_any W_15a7c = Some (OpImm32 13 13 3617, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a80 : bv 32 := 0x02d56663.
Lemma F_15a80 : fetch_word Ubsan.M.loaded_segments (0x15b7c : word) = Some W_15a80.
Proof. vm_refl. Qed.
Lemma D_15a80 : decode_any W_15a80 = Some (Branch BC_LTU 10 13 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a84 : bv 32 := 0x0001d517.
Lemma F_15a84 : fetch_word Ubsan.M.loaded_segments (0x15b80 : word) = Some W_15a84.
Proof. vm_refl. Qed.
Lemma D_15a84 : decode_any W_15a84 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a88 : bv 32 := 0x1f053503.
Lemma F_15a88 : fetch_word Ubsan.M.loaded_segments (0x15b84 : word) = Some W_15a88.
Proof. vm_refl. Qed.
Lemma D_15a88 : decode_any W_15a88 = Some (Load SZ8 true 10 10 496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a8c : bv 32 := 0x00052503.
Lemma F_15a8c : fetch_word Ubsan.M.loaded_segments (0x15b88 : word) = Some W_15a8c.
Proof. vm_refl. Qed.
Lemma D_15a8c : decode_any W_15a8c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a90 : bv 32 := 0x00500593.
Lemma F_15a90 : fetch_word Ubsan.M.loaded_segments (0x15b8c : word) = Some W_15a90.
Proof. vm_refl. Qed.
Lemma D_15a90 : decode_any W_15a90 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a94 : bv 32 := 0x04a5c263.
Lemma F_15a94 : fetch_word Ubsan.M.loaded_segments (0x15b90 : word) = Some W_15a94.
Proof. vm_refl. Qed.
Lemma D_15a94 : decode_any W_15a94 = Some (Branch BC_LT 11 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a98 : bv 32 := 0xffffb517.
Lemma F_15a98 : fetch_word Ubsan.M.loaded_segments (0x15b94 : word) = Some W_15a98.
Proof. vm_refl. Qed.
Lemma D_15a98 : decode_any W_15a98 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a9c : bv 32 := 0xffffb597.
Lemma F_15a9c : fetch_word Ubsan.M.loaded_segments (0x15b98 : word) = Some W_15a9c.
Proof. vm_refl. Qed.
Lemma D_15a9c : decode_any W_15a9c = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15aa0 : bv 32 := 0x61750513.
Lemma F_15aa0 : fetch_word Ubsan.M.loaded_segments (0x15b9c : word) = Some W_15aa0.
Proof. vm_refl. Qed.
Lemma D_15aa0 : decode_any W_15aa0 = Some (OpImm ALU_ADD 10 10 1559, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15aa4 : bv 32 := 0xdd258593.
Lemma F_15aa4 : fetch_word Ubsan.M.loaded_segments (0x15ba0 : word) = Some W_15aa4.
Proof. vm_refl. Qed.
Lemma D_15aa4 : decode_any W_15aa4 = Some (OpImm ALU_ADD 11 11 3538, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15aa8 : bv 32 := 0x02c0006f.
Lemma F_15aa8 : fetch_word Ubsan.M.loaded_segments (0x15ba4 : word) = Some W_15aa8.
Proof. vm_refl. Qed.
Lemma D_15aa8 : decode_any W_15aa8 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15aac : bv 32 := 0x04d5e863.
Lemma F_15aac : fetch_word Ubsan.M.loaded_segments (0x15ba8 : word) = Some W_15aac.
Proof. vm_refl. Qed.
Lemma D_15aac : decode_any W_15aac = Some (Branch BC_LTU 11 13 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ab0 : bv 32 := 0x0001d517.
Lemma F_15ab0 : fetch_word Ubsan.M.loaded_segments (0x15bac : word) = Some W_15ab0.
Proof. vm_refl. Qed.
Lemma D_15ab0 : decode_any W_15ab0 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ab4 : bv 32 := 0x1c453503.
Lemma F_15ab4 : fetch_word Ubsan.M.loaded_segments (0x15bb0 : word) = Some W_15ab4.
Proof. vm_refl. Qed.
Lemma D_15ab4 : decode_any W_15ab4 = Some (Load SZ8 true 10 10 452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ab8 : bv 32 := 0x00052503.
Lemma F_15ab8 : fetch_word Ubsan.M.loaded_segments (0x15bb4 : word) = Some W_15ab8.
Proof. vm_refl. Qed.
Lemma D_15ab8 : decode_any W_15ab8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15abc : bv 32 := 0x00500593.
Lemma F_15abc : fetch_word Ubsan.M.loaded_segments (0x15bb8 : word) = Some W_15abc.
Proof. vm_refl. Qed.
Lemma D_15abc : decode_any W_15abc = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ac0 : bv 32 := 0x00a5cc63.
Lemma F_15ac0 : fetch_word Ubsan.M.loaded_segments (0x15bbc : word) = Some W_15ac0.
Proof. vm_refl. Qed.
Lemma D_15ac0 : decode_any W_15ac0 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ac4 : bv 32 := 0xffffb517.
Lemma F_15ac4 : fetch_word Ubsan.M.loaded_segments (0x15bc0 : word) = Some W_15ac4.
Proof. vm_refl. Qed.
Lemma D_15ac4 : decode_any W_15ac4 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ac8 : bv 32 := 0xffffb597.
Lemma F_15ac8 : fetch_word Ubsan.M.loaded_segments (0x15bc4 : word) = Some W_15ac8.
Proof. vm_refl. Qed.
Lemma D_15ac8 : decode_any W_15ac8 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15acc : bv 32 := 0x16c50513.
Lemma F_15acc : fetch_word Ubsan.M.loaded_segments (0x15bc8 : word) = Some W_15acc.
Proof. vm_refl. Qed.
Lemma D_15acc : decode_any W_15acc = Some (OpImm ALU_ADD 10 10 364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ad0 : bv 32 := 0xda658593.
Lemma F_15ad0 : fetch_word Ubsan.M.loaded_segments (0x15bcc : word) = Some W_15ad0.
Proof. vm_refl. Qed.
Lemma D_15ad0 : decode_any W_15ad0 = Some (OpImm ALU_ADD 11 11 3494, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ad4 : bv 32 := 0x8e1ff0ef.
Lemma F_15ad4 : fetch_word Ubsan.M.loaded_segments (0x15bd0 : word) = Some W_15ad4.
Proof. vm_refl. Qed.
Lemma D_15ad4 : decode_any W_15ad4 = Some (Jal 1 2095328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ad8 : bv 32 := 0x00000513.
Lemma F_15ad8 : fetch_word Ubsan.M.loaded_segments (0x15bd4 : word) = Some W_15ad8.
Proof. vm_refl. Qed.
Lemma D_15ad8 : decode_any W_15ad8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15adc : bv 32 := 0x02813083.
Lemma F_15adc : fetch_word Ubsan.M.loaded_segments (0x15bd8 : word) = Some W_15adc.
Proof. vm_refl. Qed.
Lemma D_15adc : decode_any W_15adc = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ae0 : bv 32 := 0x02013403.
Lemma F_15ae0 : fetch_word Ubsan.M.loaded_segments (0x15bdc : word) = Some W_15ae0.
Proof. vm_refl. Qed.
Lemma D_15ae0 : decode_any W_15ae0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ae4 : bv 32 := 0x01813483.
Lemma F_15ae4 : fetch_word Ubsan.M.loaded_segments (0x15be0 : word) = Some W_15ae4.
Proof. vm_refl. Qed.
Lemma D_15ae4 : decode_any W_15ae4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ae8 : bv 32 := 0x01013903.
Lemma F_15ae8 : fetch_word Ubsan.M.loaded_segments (0x15be4 : word) = Some W_15ae8.
Proof. vm_refl. Qed.
Lemma D_15ae8 : decode_any W_15ae8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15aec : bv 32 := 0x00813983.
Lemma F_15aec : fetch_word Ubsan.M.loaded_segments (0x15be8 : word) = Some W_15aec.
Proof. vm_refl. Qed.
Lemma D_15aec : decode_any W_15aec = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15af0 : bv 32 := 0x00013a03.
Lemma F_15af0 : fetch_word Ubsan.M.loaded_segments (0x15bec : word) = Some W_15af0.
Proof. vm_refl. Qed.
Lemma D_15af0 : decode_any W_15af0 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15af4 : bv 32 := 0x03010113.
Lemma F_15af4 : fetch_word Ubsan.M.loaded_segments (0x15bf0 : word) = Some W_15af4.
Proof. vm_refl. Qed.
Lemma D_15af4 : decode_any W_15af4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15af8 : bv 32 := 0x00008067.
Lemma F_15af8 : fetch_word Ubsan.M.loaded_segments (0x15bf4 : word) = Some W_15af8.
Proof. vm_refl. Qed.
Lemma D_15af8 : decode_any W_15af8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15afc : bv 32 := 0x00050993.
Lemma F_15afc : fetch_word Ubsan.M.loaded_segments (0x15bf8 : word) = Some W_15afc.
Proof. vm_refl. Qed.
Lemma D_15afc : decode_any W_15afc = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b00 : bv 32 := 0x00058493.
Lemma F_15b00 : fetch_word Ubsan.M.loaded_segments (0x15bfc : word) = Some W_15b00.
Proof. vm_refl. Qed.
Lemma D_15b00 : decode_any W_15b00 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b04 : bv 32 := 0x00060413.
Lemma F_15b04 : fetch_word Ubsan.M.loaded_segments (0x15c00 : word) = Some W_15b04.
Proof. vm_refl. Qed.
Lemma D_15b04 : decode_any W_15b04 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b08 : bv 32 := 0x00100513.
Lemma F_15b08 : fetch_word Ubsan.M.loaded_segments (0x15c04 : word) = Some W_15b08.
Proof. vm_refl. Qed.
Lemma D_15b08 : decode_any W_15b08 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b0c : bv 32 := 0x04000593.
Lemma F_15b0c : fetch_word Ubsan.M.loaded_segments (0x15c08 : word) = Some W_15b0c.
Proof. vm_refl. Qed.
Lemma D_15b0c : decode_any W_15b0c = Some (OpImm ALU_ADD 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b10 : bv 32 := 0x4dc140ef.
Lemma F_15b10 : fetch_word Ubsan.M.loaded_segments (0x15c0c : word) = Some W_15b10.
Proof. vm_refl. Qed.
Lemma D_15b10 : decode_any W_15b10 = Some (Jal 1 83164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b14 : bv 32 := 0x04050863.
Lemma F_15b14 : fetch_word Ubsan.M.loaded_segments (0x15c10 : word) = Some W_15b14.
Proof. vm_refl. Qed.
Lemma D_15b14 : decode_any W_15b14 = Some (Branch BC_EQ 10 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b18 : bv 32 := 0x00050913.
Lemma F_15b18 : fetch_word Ubsan.M.loaded_segments (0x15c14 : word) = Some W_15b18.
Proof. vm_refl. Qed.
Lemma D_15b18 : decode_any W_15b18 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b1c : bv 32 := 0x00098593.
Lemma F_15b1c : fetch_word Ubsan.M.loaded_segments (0x15c18 : word) = Some W_15b1c.
Proof. vm_refl. Qed.
Lemma D_15b1c : decode_any W_15b1c = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b20 : bv 32 := 0x18d000ef.
Lemma F_15b20 : fetch_word Ubsan.M.loaded_segments (0x15c1c : word) = Some W_15b20.
Proof. vm_refl. Qed.
Lemma D_15b20 : decode_any W_15b20 = Some (Jal 1 2444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b24 : bv 32 := 0x00090513.
Lemma F_15b24 : fetch_word Ubsan.M.loaded_segments (0x15c20 : word) = Some W_15b24.
Proof. vm_refl. Qed.
Lemma D_15b24 : decode_any W_15b24 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b28 : bv 32 := 0x00048593.
Lemma F_15b28 : fetch_word Ubsan.M.loaded_segments (0x15c24 : word) = Some W_15b28.
Proof. vm_refl. Qed.
Lemma D_15b28 : decode_any W_15b28 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b2c : bv 32 := 0x209000ef.
Lemma F_15b2c : fetch_word Ubsan.M.loaded_segments (0x15c28 : word) = Some W_15b2c.
Proof. vm_refl. Qed.
Lemma D_15b2c : decode_any W_15b2c = Some (Jal 1 2568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b30 : bv 32 := 0x00090513.
Lemma F_15b30 : fetch_word Ubsan.M.loaded_segments (0x15c2c : word) = Some W_15b30.
Proof. vm_refl. Qed.
Lemma D_15b30 : decode_any W_15b30 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b34 : bv 32 := 0x00040593.
Lemma F_15b34 : fetch_word Ubsan.M.loaded_segments (0x15c30 : word) = Some W_15b34.
Proof. vm_refl. Qed.
Lemma D_15b34 : decode_any W_15b34 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b38 : bv 32 := 0x285000ef.
Lemma F_15b38 : fetch_word Ubsan.M.loaded_segments (0x15c34 : word) = Some W_15b38.
Proof. vm_refl. Qed.
Lemma D_15b38 : decode_any W_15b38 = Some (Jal 1 2692, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b3c : bv 32 := 0x00797593.
Lemma F_15b3c : fetch_word Ubsan.M.loaded_segments (0x15c38 : word) = Some W_15b3c.
Proof. vm_refl. Qed.
Lemma D_15b3c : decode_any W_15b3c = Some (OpImm ALU_AND 11 18 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b40 : bv 32 := 0x06059463.
Lemma F_15b40 : fetch_word Ubsan.M.loaded_segments (0x15c3c : word) = Some W_15b40.
Proof. vm_refl. Qed.
Lemma D_15b40 : decode_any W_15b40 = Some (Branch BC_NE 11 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b44 : bv 32 := 0x00090513.
Lemma F_15b44 : fetch_word Ubsan.M.loaded_segments (0x15c40 : word) = Some W_15b44.
Proof. vm_refl. Qed.
Lemma D_15b44 : decode_any W_15b44 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b48 : bv 32 := 0x01492823.
Lemma F_15b48 : fetch_word Ubsan.M.loaded_segments (0x15c44 : word) = Some W_15b48.
Proof. vm_refl. Qed.
Lemma D_15b48 : decode_any W_15b48 = Some (Store SZ4 18 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b4c : bv 32 := 0xfe84041b.
Lemma F_15b4c : fetch_word Ubsan.M.loaded_segments (0x15c48 : word) = Some W_15b4c.
Proof. vm_refl. Qed.
Lemma D_15b4c : decode_any W_15b4c = Some (OpImm32 8 8 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b50 : bv 32 := 0xff747413.
Lemma F_15b50 : fetch_word Ubsan.M.loaded_segments (0x15c4c : word) = Some W_15b50.
Proof. vm_refl. Qed.
Lemma D_15b50 : decode_any W_15b50 = Some (OpImm ALU_AND 8 8 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b54 : bv 32 := 0x00100593.
Lemma F_15b54 : fetch_word Ubsan.M.loaded_segments (0x15c50 : word) = Some W_15b54.
Proof. vm_refl. Qed.
Lemma D_15b54 : decode_any W_15b54 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b58 : bv 32 := 0x02040a63.
Lemma F_15b58 : fetch_word Ubsan.M.loaded_segments (0x15c54 : word) = Some W_15b58.
Proof. vm_refl. Qed.
Lemma D_15b58 : decode_any W_15b58 = Some (Branch BC_EQ 8 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b5c : bv 32 := 0x00100613.
Lemma F_15b5c : fetch_word Ubsan.M.loaded_segments (0x15c58 : word) = Some W_15b5c.
Proof. vm_refl. Qed.
Lemma D_15b5c : decode_any W_15b5c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b60 : bv 32 := 0x0300006f.
Lemma F_15b60 : fetch_word Ubsan.M.loaded_segments (0x15c5c : word) = Some W_15b60.
Proof. vm_refl. Qed.
Lemma D_15b60 : decode_any W_15b60 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b64 : bv 32 := 0x0001d517.
Lemma F_15b64 : fetch_word Ubsan.M.loaded_segments (0x15c60 : word) = Some W_15b64.
Proof. vm_refl. Qed.
Lemma D_15b64 : decode_any W_15b64 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b68 : bv 32 := 0x11053503.
Lemma F_15b68 : fetch_word Ubsan.M.loaded_segments (0x15c64 : word) = Some W_15b68.
Proof. vm_refl. Qed.
Lemma D_15b68 : decode_any W_15b68 = Some (Load SZ8 true 10 10 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b6c : bv 32 := 0x00052503.
Lemma F_15b6c : fetch_word Ubsan.M.loaded_segments (0x15c68 : word) = Some W_15b6c.
Proof. vm_refl. Qed.
Lemma D_15b6c : decode_any W_15b6c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b70 : bv 32 := 0x00500593.
Lemma F_15b70 : fetch_word Ubsan.M.loaded_segments (0x15c6c : word) = Some W_15b70.
Proof. vm_refl. Qed.
Lemma D_15b70 : decode_any W_15b70 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b74 : bv 32 := 0xf6a5c2e3.
Lemma F_15b74 : fetch_word Ubsan.M.loaded_segments (0x15c70 : word) = Some W_15b74.
Proof. vm_refl. Qed.
Lemma D_15b74 : decode_any W_15b74 = Some (Branch BC_LT 11 10 8036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b78 : bv 32 := 0xffffb517.
Lemma F_15b78 : fetch_word Ubsan.M.loaded_segments (0x15c74 : word) = Some W_15b78.
Proof. vm_refl. Qed.
Lemma D_15b78 : decode_any W_15b78 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b7c : bv 32 := 0xffffb597.
Lemma F_15b7c : fetch_word Ubsan.M.loaded_segments (0x15c78 : word) = Some W_15b7c.
Proof. vm_refl. Qed.
Lemma D_15b7c : decode_any W_15b7c = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b80 : bv 32 := 0x84950513.
Lemma F_15b80 : fetch_word Ubsan.M.loaded_segments (0x15c7c : word) = Some W_15b80.
Proof. vm_refl. Qed.
Lemma D_15b80 : decode_any W_15b80 = Some (OpImm ALU_ADD 10 10 2121, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b84 : bv 32 := 0xcf258593.
Lemma F_15b84 : fetch_word Ubsan.M.loaded_segments (0x15c80 : word) = Some W_15b84.
Proof. vm_refl. Qed.
Lemma D_15b84 : decode_any W_15b84 = Some (OpImm ALU_ADD 11 11 3314, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b88 : bv 32 := 0xe99ff06f.
Lemma F_15b88 : fetch_word Ubsan.M.loaded_segments (0x15c84 : word) = Some W_15b88.
Proof. vm_refl. Qed.
Lemma D_15b88 : decode_any W_15b88 = Some (Jal 0 2096792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b8c : bv 32 := 0x00300613.
Lemma F_15b8c : fetch_word Ubsan.M.loaded_segments (0x15c88 : word) = Some W_15b8c.
Proof. vm_refl. Qed.
Lemma D_15b8c : decode_any W_15b8c = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b90 : bv 32 := 0x00c52623.
Lemma F_15b90 : fetch_word Ubsan.M.loaded_segments (0x15c8c : word) = Some W_15b90.
Proof. vm_refl. Qed.
Lemma D_15b90 : decode_any W_15b90 = Some (Store SZ4 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b94 : bv 32 := 0x0310000f.
Lemma F_15b94 : fetch_word Ubsan.M.loaded_segments (0x15c90 : word) = Some W_15b94.
Proof. vm_refl. Qed.
Lemma D_15b94 : decode_any W_15b94 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b98 : bv 32 := 0x00b52a23.
Lemma F_15b98 : fetch_word Ubsan.M.loaded_segments (0x15c94 : word) = Some W_15b98.
Proof. vm_refl. Qed.
Lemma D_15b98 : decode_any W_15b98 = Some (Store SZ4 10 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b9c : bv 32 := 0x0330000f.
Lemma F_15b9c : fetch_word Ubsan.M.loaded_segments (0x15c98 : word) = Some W_15b9c.
Proof. vm_refl. Qed.
Lemma D_15b9c : decode_any W_15b9c = Some (Fence 0 3 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ba0 : bv 32 := 0x02052023.
Lemma F_15ba0 : fetch_word Ubsan.M.loaded_segments (0x15c9c : word) = Some W_15ba0.
Proof. vm_refl. Qed.
Lemma D_15ba0 : decode_any W_15ba0 = Some (Store SZ4 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ba4 : bv 32 := 0xf39ff06f.
Lemma F_15ba4 : fetch_word Ubsan.M.loaded_segments (0x15ca0 : word) = Some W_15ba4.
Proof. vm_refl. Qed.
Lemma D_15ba4 : decode_any W_15ba4 = Some (Jal 0 2096952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bac : bv 32 := 0x00050a63.
Lemma F_15bac : fetch_word Ubsan.M.loaded_segments (0x15ca8 : word) = Some W_15bac.
Proof. vm_refl. Qed.
Lemma D_15bac : decode_any W_15bac = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bb0 : bv 32 := 0x00757593.
Lemma F_15bb0 : fetch_word Ubsan.M.loaded_segments (0x15cac : word) = Some W_15bb0.
Proof. vm_refl. Qed.
Lemma D_15bb0 : decode_any W_15bb0 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bb4 : bv 32 := 0x04059063.
Lemma F_15bb4 : fetch_word Ubsan.M.loaded_segments (0x15cb0 : word) = Some W_15bb4.
Proof. vm_refl. Qed.
Lemma D_15bb4 : decode_any W_15bb4 = Some (Branch BC_NE 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bb8 : bv 32 := 0x01052503.
Lemma F_15bb8 : fetch_word Ubsan.M.loaded_segments (0x15cb4 : word) = Some W_15bb8.
Proof. vm_refl. Qed.
Lemma D_15bb8 : decode_any W_15bb8 = Some (Load SZ4 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bbc : bv 32 := 0x00008067.
Lemma F_15bbc : fetch_word Ubsan.M.loaded_segments (0x15cb8 : word) = Some W_15bbc.
Proof. vm_refl. Qed.
Lemma D_15bbc : decode_any W_15bbc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bf8 : bv 32 := 0xfe010113.
Lemma F_15bf8 : fetch_word Ubsan.M.loaded_segments (0x15cf4 : word) = Some W_15bf8.
Proof. vm_refl. Qed.
Lemma D_15bf8 : decode_any W_15bf8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bfc : bv 32 := 0x00113c23.
Lemma F_15bfc : fetch_word Ubsan.M.loaded_segments (0x15cf8 : word) = Some W_15bfc.
Proof. vm_refl. Qed.
Lemma D_15bfc : decode_any W_15bfc = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c00 : bv 32 := 0x00813823.
Lemma F_15c00 : fetch_word Ubsan.M.loaded_segments (0x15cfc : word) = Some W_15c00.
Proof. vm_refl. Qed.
Lemma D_15c00 : decode_any W_15c00 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c04 : bv 32 := 0x00913423.
Lemma F_15c04 : fetch_word Ubsan.M.loaded_segments (0x15d00 : word) = Some W_15c04.
Proof. vm_refl. Qed.
Lemma D_15c04 : decode_any W_15c04 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c08 : bv 32 := 0x08050063.
Lemma F_15c08 : fetch_word Ubsan.M.loaded_segments (0x15d04 : word) = Some W_15c08.
Proof. vm_refl. Qed.
Lemma D_15c08 : decode_any W_15c08 = Some (Branch BC_EQ 10 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c0c : bv 32 := 0x00757593.
Lemma F_15c0c : fetch_word Ubsan.M.loaded_segments (0x15d08 : word) = Some W_15c0c.
Proof. vm_refl. Qed.
Lemma D_15c0c : decode_any W_15c0c = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c10 : bv 32 := 0x0c059263.
Lemma F_15c10 : fetch_word Ubsan.M.loaded_segments (0x15d0c : word) = Some W_15c10.
Proof. vm_refl. Qed.
Lemma D_15c10 : decode_any W_15c10 = Some (Branch BC_NE 11 0 196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c14 : bv 32 := 0x00053403.
Lemma F_15c14 : fetch_word Ubsan.M.loaded_segments (0x15d10 : word) = Some W_15c14.
Proof. vm_refl. Qed.
Lemma D_15c14 : decode_any W_15c14 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c18 : bv 32 := 0x0a040463.
Lemma F_15c18 : fetch_word Ubsan.M.loaded_segments (0x15d14 : word) = Some W_15c18.
Proof. vm_refl. Qed.
Lemma D_15c18 : decode_any W_15c18 = Some (Branch BC_EQ 8 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c1c : bv 32 := 0x00747593.
Lemma F_15c1c : fetch_word Ubsan.M.loaded_segments (0x15d18 : word) = Some W_15c1c.
Proof. vm_refl. Qed.
Lemma D_15c1c : decode_any W_15c1c = Some (OpImm ALU_AND 11 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c20 : bv 32 := 0x0a059a63.
Lemma F_15c20 : fetch_word Ubsan.M.loaded_segments (0x15d1c : word) = Some W_15c20.
Proof. vm_refl. Qed.
Lemma D_15c20 : decode_any W_15c20 = Some (Branch BC_NE 11 0 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c24 : bv 32 := 0x01440593.
Lemma F_15c24 : fetch_word Ubsan.M.loaded_segments (0x15d20 : word) = Some W_15c24.
Proof. vm_refl. Qed.
Lemma D_15c24 : decode_any W_15c24 = Some (OpImm ALU_ADD 11 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c28 : bv 32 := 0xfff00613.
Lemma F_15c28 : fetch_word Ubsan.M.loaded_segments (0x15d24 : word) = Some W_15c28.
Proof. vm_refl. Qed.
Lemma D_15c28 : decode_any W_15c28 = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c2c : bv 32 := 0x06c5a5af.
Lemma F_15c2c : fetch_word Ubsan.M.loaded_segments (0x15d28 : word) = Some W_15c2c.
Proof. vm_refl. Qed.
Lemma D_15c2c : decode_any W_15c2c = Some (Amo AMO_ADD AW true true 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c30 : bv 32 := 0x00100613.
Lemma F_15c30 : fetch_word Ubsan.M.loaded_segments (0x15d2c : word) = Some W_15c30.
Proof. vm_refl. Qed.
Lemma D_15c30 : decode_any W_15c30 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c34 : bv 32 := 0x04c59663.
Lemma F_15c34 : fetch_word Ubsan.M.loaded_segments (0x15d30 : word) = Some W_15c34.
Proof. vm_refl. Qed.
Lemma D_15c34 : decode_any W_15c34 = Some (Branch BC_NE 11 12 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c38 : bv 32 := 0x00050493.
Lemma F_15c38 : fetch_word Ubsan.M.loaded_segments (0x15d34 : word) = Some W_15c38.
Proof. vm_refl. Qed.
Lemma D_15c38 : decode_any W_15c38 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c3c : bv 32 := 0x03843503.
Lemma F_15c3c : fetch_word Ubsan.M.loaded_segments (0x15d38 : word) = Some W_15c3c.
Proof. vm_refl. Qed.
Lemma D_15c3c : decode_any W_15c3c = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c40 : bv 32 := 0x00050863.
Lemma F_15c40 : fetch_word Ubsan.M.loaded_segments (0x15d3c : word) = Some W_15c40.
Proof. vm_refl. Qed.
Lemma D_15c40 : decode_any W_15c40 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c44 : bv 32 := 0x0001e597.
Lemma F_15c44 : fetch_word Ubsan.M.loaded_segments (0x15d40 : word) = Some W_15c44.
Proof. vm_refl. Qed.
Lemma D_15c44 : decode_any W_15c44 = Some (Auipc 11 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c48 : bv 32 := 0x0b85b583.
Lemma F_15c48 : fetch_word Ubsan.M.loaded_segments (0x15d44 : word) = Some W_15c48.
Proof. vm_refl. Qed.
Lemma D_15c48 : decode_any W_15c48 = Some (Load SZ8 true 11 11 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c4c : bv 32 := 0x000580e7.
Lemma F_15c4c : fetch_word Ubsan.M.loaded_segments (0x15d48 : word) = Some W_15c4c.
Proof. vm_refl. Qed.
Lemma D_15c4c : decode_any W_15c4c = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c50 : bv 32 := 0x02843503.
Lemma F_15c50 : fetch_word Ubsan.M.loaded_segments (0x15d4c : word) = Some W_15c50.
Proof. vm_refl. Qed.
Lemma D_15c50 : decode_any W_15c50 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c54 : bv 32 := 0x00050463.
Lemma F_15c54 : fetch_word Ubsan.M.loaded_segments (0x15d50 : word) = Some W_15c54.
Proof. vm_refl. Qed.
Lemma D_15c54 : decode_any W_15c54 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c5c : bv 32 := 0x03043503.
Lemma F_15c5c : fetch_word Ubsan.M.loaded_segments (0x15d58 : word) = Some W_15c5c.
Proof. vm_refl. Qed.
Lemma D_15c5c : decode_any W_15c5c = Some (Load SZ8 true 10 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c60 : bv 32 := 0x00a13023.
Lemma F_15c60 : fetch_word Ubsan.M.loaded_segments (0x15d5c : word) = Some W_15c60.
Proof. vm_refl. Qed.
Lemma D_15c60 : decode_any W_15c60 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c64 : bv 32 := 0x00050863.
Lemma F_15c64 : fetch_word Ubsan.M.loaded_segments (0x15d60 : word) = Some W_15c64.
Proof. vm_refl. Qed.
Lemma D_15c64 : decode_any W_15c64 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c68 : bv 32 := 0x00010513.
Lemma F_15c68 : fetch_word Ubsan.M.loaded_segments (0x15d64 : word) = Some W_15c68.
Proof. vm_refl. Qed.
Lemma D_15c68 : decode_any W_15c68 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c6c : bv 32 := 0x6fd030ef.
Lemma F_15c6c : fetch_word Ubsan.M.loaded_segments (0x15d68 : word) = Some W_15c6c.
Proof. vm_refl. Qed.
Lemma D_15c6c : decode_any W_15c6c = Some (Jal 1 16124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c70 : bv 32 := 0x02043823.
Lemma F_15c70 : fetch_word Ubsan.M.loaded_segments (0x15d6c : word) = Some W_15c70.
Proof. vm_refl. Qed.
Lemma D_15c70 : decode_any W_15c70 = Some (Store SZ8 8 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c74 : bv 32 := 0x00040513.
Lemma F_15c74 : fetch_word Ubsan.M.loaded_segments (0x15d70 : word) = Some W_15c74.
Proof. vm_refl. Qed.
Lemma D_15c74 : decode_any W_15c74 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c78 : bv 32 := 0x4ac140ef.
Lemma F_15c78 : fetch_word Ubsan.M.loaded_segments (0x15d74 : word) = Some W_15c78.
Proof. vm_refl. Qed.
Lemma D_15c78 : decode_any W_15c78 = Some (Jal 1 83116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c7c : bv 32 := 0x00048513.
Lemma F_15c7c : fetch_word Ubsan.M.loaded_segments (0x15d78 : word) = Some W_15c7c.
Proof. vm_refl. Qed.
Lemma D_15c7c : decode_any W_15c7c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c80 : bv 32 := 0x00053023.
Lemma F_15c80 : fetch_word Ubsan.M.loaded_segments (0x15d7c : word) = Some W_15c80.
Proof. vm_refl. Qed.
Lemma D_15c80 : decode_any W_15c80 = Some (Store SZ8 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c84 : bv 32 := 0x03c0006f.
Lemma F_15c84 : fetch_word Ubsan.M.loaded_segments (0x15d80 : word) = Some W_15c84.
Proof. vm_refl. Qed.
Lemma D_15c84 : decode_any W_15c84 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15cc0 : bv 32 := 0x01813083.
Lemma F_15cc0 : fetch_word Ubsan.M.loaded_segments (0x15dbc : word) = Some W_15cc0.
Proof. vm_refl. Qed.
Lemma D_15cc0 : decode_any W_15cc0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15cc4 : bv 32 := 0x01013403.
Lemma F_15cc4 : fetch_word Ubsan.M.loaded_segments (0x15dc0 : word) = Some W_15cc4.
Proof. vm_refl. Qed.
Lemma D_15cc4 : decode_any W_15cc4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15cc8 : bv 32 := 0x00813483.
Lemma F_15cc8 : fetch_word Ubsan.M.loaded_segments (0x15dc4 : word) = Some W_15cc8.
Proof. vm_refl. Qed.
Lemma D_15cc8 : decode_any W_15cc8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ccc : bv 32 := 0x02010113.
Lemma F_15ccc : fetch_word Ubsan.M.loaded_segments (0x15dc8 : word) = Some W_15ccc.
Proof. vm_refl. Qed.
Lemma D_15ccc : decode_any W_15ccc = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15cd0 : bv 32 := 0x00008067.
Lemma F_15cd0 : fetch_word Ubsan.M.loaded_segments (0x15dcc : word) = Some W_15cd0.
Proof. vm_refl. Qed.
Lemma D_15cd0 : decode_any W_15cd0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15da8 : bv 32 := 0xfe010113.
Lemma F_15da8 : fetch_word Ubsan.M.loaded_segments (0x15ea4 : word) = Some W_15da8.
Proof. vm_refl. Qed.
Lemma D_15da8 : decode_any W_15da8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15dac : bv 32 := 0x00113c23.
Lemma F_15dac : fetch_word Ubsan.M.loaded_segments (0x15ea8 : word) = Some W_15dac.
Proof. vm_refl. Qed.
Lemma D_15dac : decode_any W_15dac = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15db0 : bv 32 := 0x00813823.
Lemma F_15db0 : fetch_word Ubsan.M.loaded_segments (0x15eac : word) = Some W_15db0.
Proof. vm_refl. Qed.
Lemma D_15db0 : decode_any W_15db0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15db4 : bv 32 := 0x00913423.
Lemma F_15db4 : fetch_word Ubsan.M.loaded_segments (0x15eb0 : word) = Some W_15db4.
Proof. vm_refl. Qed.
Lemma D_15db4 : decode_any W_15db4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15db8 : bv 32 := 0x01213023.
Lemma F_15db8 : fetch_word Ubsan.M.loaded_segments (0x15eb4 : word) = Some W_15db8.
Proof. vm_refl. Qed.
Lemma D_15db8 : decode_any W_15db8 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15dbc : bv 32 := 0x04050263.
Lemma F_15dbc : fetch_word Ubsan.M.loaded_segments (0x15eb8 : word) = Some W_15dbc.
Proof. vm_refl. Qed.
Lemma D_15dbc : decode_any W_15dbc = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15dc0 : bv 32 := 0x00050493.
Lemma F_15dc0 : fetch_word Ubsan.M.loaded_segments (0x15ebc : word) = Some W_15dc0.
Proof. vm_refl. Qed.
Lemma D_15dc0 : decode_any W_15dc0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15dc4 : bv 32 := 0x00757513.
Lemma F_15dc4 : fetch_word Ubsan.M.loaded_segments (0x15ec0 : word) = Some W_15dc4.
Proof. vm_refl. Qed.
Lemma D_15dc4 : decode_any W_15dc4 = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15dc8 : bv 32 := 0x12051c63.
Lemma F_15dc8 : fetch_word Ubsan.M.loaded_segments (0x15ec4 : word) = Some W_15dc8.
Proof. vm_refl. Qed.
Lemma D_15dc8 : decode_any W_15dc8 = Some (Branch BC_NE 10 0 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15dcc : bv 32 := 0x0004a503.
Lemma F_15dcc : fetch_word Ubsan.M.loaded_segments (0x15ec8 : word) = Some W_15dcc.
Proof. vm_refl. Qed.
Lemma D_15dcc : decode_any W_15dcc = Some (Load SZ4 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15dd0 : bv 32 := 0x0044a583.
Lemma F_15dd0 : fetch_word Ubsan.M.loaded_segments (0x15ecc : word) = Some W_15dd0.
Proof. vm_refl. Qed.
Lemma D_15dd0 : decode_any W_15dd0 = Some (Load SZ4 true 11 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15dd4 : bv 32 := 0x0084a603.
Lemma F_15dd4 : fetch_word Ubsan.M.loaded_segments (0x15ed0 : word) = Some W_15dd4.
Proof. vm_refl. Qed.
Lemma D_15dd4 : decode_any W_15dd4 = Some (Load SZ4 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15dd8 : bv 32 := 0x969ff0ef.
Lemma F_15dd8 : fetch_word Ubsan.M.loaded_segments (0x15ed4 : word) = Some W_15dd8.
Proof. vm_refl. Qed.
Lemma D_15dd8 : decode_any W_15dd8 = Some (Jal 1 2095464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ddc : bv 32 := 0x04050663.
Lemma F_15ddc : fetch_word Ubsan.M.loaded_segments (0x15ed8 : word) = Some W_15ddc.
Proof. vm_refl. Qed.
Lemma D_15ddc : decode_any W_15ddc = Some (Branch BC_EQ 10 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15de0 : bv 32 := 0x00050413.
Lemma F_15de0 : fetch_word Ubsan.M.loaded_segments (0x15edc : word) = Some W_15de0.
Proof. vm_refl. Qed.
Lemma D_15de0 : decode_any W_15de0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15de4 : bv 32 := 0x08a48663.
Lemma F_15de4 : fetch_word Ubsan.M.loaded_segments (0x15ee0 : word) = Some W_15de4.
Proof. vm_refl. Qed.
Lemma D_15de4 : decode_any W_15de4 = Some (Branch BC_EQ 9 10 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15de8 : bv 32 := 0x00c4a503.
Lemma F_15de8 : fetch_word Ubsan.M.loaded_segments (0x15ee4 : word) = Some W_15de8.
Proof. vm_refl. Qed.
Lemma D_15de8 : decode_any W_15de8 = Some (Load SZ4 true 10 9 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15dec : bv 32 := 0x00747913.
Lemma F_15dec : fetch_word Ubsan.M.loaded_segments (0x15ee8 : word) = Some W_15dec.
Proof. vm_refl. Qed.
Lemma D_15dec : decode_any W_15dec = Some (OpImm ALU_AND 18 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15df0 : bv 32 := 0x08a05863.
Lemma F_15df0 : fetch_word Ubsan.M.loaded_segments (0x15eec : word) = Some W_15df0.
Proof. vm_refl. Qed.
Lemma D_15df0 : decode_any W_15df0 = Some (Branch BC_GE 0 10 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15df4 : bv 32 := 0x10091663.
Lemma F_15df4 : fetch_word Ubsan.M.loaded_segments (0x15ef0 : word) = Some W_15df4.
Proof. vm_refl. Qed.
Lemma D_15df4 : decode_any W_15df4 = Some (Branch BC_NE 18 0 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15df8 : bv 32 := 0x00a42623.
Lemma F_15df8 : fetch_word Ubsan.M.loaded_segments (0x15ef4 : word) = Some W_15df8.
Proof. vm_refl. Qed.
Lemma D_15df8 : decode_any W_15df8 = Some (Store SZ4 8 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15dfc : bv 32 := 0x0b00006f.
Lemma F_15dfc : fetch_word Ubsan.M.loaded_segments (0x15ef8 : word) = Some W_15dfc.
Proof. vm_refl. Qed.
Lemma D_15dfc : decode_any W_15dfc = Some (Jal 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e28 : bv 32 := 0x0001d517.
Lemma F_15e28 : fetch_word Ubsan.M.loaded_segments (0x15f24 : word) = Some W_15e28.
Proof. vm_refl. Qed.
Lemma D_15e28 : decode_any W_15e28 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e2c : bv 32 := 0xe4c53503.
Lemma F_15e2c : fetch_word Ubsan.M.loaded_segments (0x15f28 : word) = Some W_15e2c.
Proof. vm_refl. Qed.
Lemma D_15e2c : decode_any W_15e2c = Some (Load SZ8 true 10 10 3660, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e30 : bv 32 := 0x00052503.
Lemma F_15e30 : fetch_word Ubsan.M.loaded_segments (0x15f2c : word) = Some W_15e30.
Proof. vm_refl. Qed.
Lemma D_15e30 : decode_any W_15e30 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e34 : bv 32 := 0x00500593.
Lemma F_15e34 : fetch_word Ubsan.M.loaded_segments (0x15f30 : word) = Some W_15e34.
Proof. vm_refl. Qed.
Lemma D_15e34 : decode_any W_15e34 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e38 : bv 32 := 0x02a5c863.
Lemma F_15e38 : fetch_word Ubsan.M.loaded_segments (0x15f34 : word) = Some W_15e38.
Proof. vm_refl. Qed.
Lemma D_15e38 : decode_any W_15e38 = Some (Branch BC_LT 11 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e3c : bv 32 := 0xffffa517.
Lemma F_15e3c : fetch_word Ubsan.M.loaded_segments (0x15f38 : word) = Some W_15e3c.
Proof. vm_refl. Qed.
Lemma D_15e3c : decode_any W_15e3c = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e40 : bv 32 := 0xffffb597.
Lemma F_15e40 : fetch_word Ubsan.M.loaded_segments (0x15f3c : word) = Some W_15e40.
Proof. vm_refl. Qed.
Lemma D_15e40 : decode_any W_15e40 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e44 : bv 32 := 0x58550513.
Lemma F_15e44 : fetch_word Ubsan.M.loaded_segments (0x15f40 : word) = Some W_15e44.
Proof. vm_refl. Qed.
Lemma D_15e44 : decode_any W_15e44 = Some (OpImm ALU_ADD 10 10 1413, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e48 : bv 32 := 0x13a58593.
Lemma F_15e48 : fetch_word Ubsan.M.loaded_segments (0x15f44 : word) = Some W_15e48.
Proof. vm_refl. Qed.
Lemma D_15e48 : decode_any W_15e48 = Some (OpImm ALU_ADD 11 11 314, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e4c : bv 32 := 0x00000613.
Lemma F_15e4c : fetch_word Ubsan.M.loaded_segments (0x15f48 : word) = Some W_15e4c.
Proof. vm_refl. Qed.
Lemma D_15e4c : decode_any W_15e4c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e50 : bv 32 := 0x01813083.
Lemma F_15e50 : fetch_word Ubsan.M.loaded_segments (0x15f4c : word) = Some W_15e50.
Proof. vm_refl. Qed.
Lemma D_15e50 : decode_any W_15e50 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e54 : bv 32 := 0x01013403.
Lemma F_15e54 : fetch_word Ubsan.M.loaded_segments (0x15f50 : word) = Some W_15e54.
Proof. vm_refl. Qed.
Lemma D_15e54 : decode_any W_15e54 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e58 : bv 32 := 0x00813483.
Lemma F_15e58 : fetch_word Ubsan.M.loaded_segments (0x15f54 : word) = Some W_15e58.
Proof. vm_refl. Qed.
Lemma D_15e58 : decode_any W_15e58 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e5c : bv 32 := 0x00013903.
Lemma F_15e5c : fetch_word Ubsan.M.loaded_segments (0x15f58 : word) = Some W_15e5c.
Proof. vm_refl. Qed.
Lemma D_15e5c : decode_any W_15e5c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e60 : bv 32 := 0x02010113.
Lemma F_15e60 : fetch_word Ubsan.M.loaded_segments (0x15f5c : word) = Some W_15e60.
Proof. vm_refl. Qed.
Lemma D_15e60 : decode_any W_15e60 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e64 : bv 32 := 0xdecff06f.
Lemma F_15e64 : fetch_word Ubsan.M.loaded_segments (0x15f60 : word) = Some W_15e64.
Proof. vm_refl. Qed.
Lemma D_15e64 : decode_any W_15e64 = Some (Jal 0 2094572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15eac : bv 32 := 0x04091a63.
Lemma F_15eac : fetch_word Ubsan.M.loaded_segments (0x15fa8 : word) = Some W_15eac.
Proof. vm_refl. Qed.
Lemma D_15eac : decode_any W_15eac = Some (Branch BC_NE 18 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15eb0 : bv 32 := 0x0184b503.
Lemma F_15eb0 : fetch_word Ubsan.M.loaded_segments (0x15fac : word) = Some W_15eb0.
Proof. vm_refl. Qed.
Lemma D_15eb0 : decode_any W_15eb0 = Some (Load SZ8 true 10 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15eb4 : bv 32 := 0x00a43c23.
Lemma F_15eb4 : fetch_word Ubsan.M.loaded_segments (0x15fb0 : word) = Some W_15eb4.
Proof. vm_refl. Qed.
Lemma D_15eb4 : decode_any W_15eb4 = Some (Store SZ8 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15eb8 : bv 32 := 0x00040513.
Lemma F_15eb8 : fetch_word Ubsan.M.loaded_segments (0x15fb4 : word) = Some W_15eb8.
Proof. vm_refl. Qed.
Lemma D_15eb8 : decode_any W_15eb8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ebc : bv 32 := 0x00048593.
Lemma F_15ebc : fetch_word Ubsan.M.loaded_segments (0x15fb8 : word) = Some W_15ebc.
Proof. vm_refl. Qed.
Lemma D_15ebc : decode_any W_15ebc = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ec0 : bv 32 := 0x26c000ef.
Lemma F_15ec0 : fetch_word Ubsan.M.loaded_segments (0x15fbc : word) = Some W_15ec0.
Proof. vm_refl. Qed.
Lemma D_15ec0 : decode_any W_15ec0 = Some (Jal 1 620, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ec4 : bv 32 := 0x0284b583.
Lemma F_15ec4 : fetch_word Ubsan.M.loaded_segments (0x15fc0 : word) = Some W_15ec4.
Proof. vm_refl. Qed.
Lemma D_15ec4 : decode_any W_15ec4 = Some (Load SZ8 true 11 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ec8 : bv 32 := 0x02840513.
Lemma F_15ec8 : fetch_word Ubsan.M.loaded_segments (0x15fc4 : word) = Some W_15ec8.
Proof. vm_refl. Qed.
Lemma D_15ec8 : decode_any W_15ec8 = Some (OpImm ALU_ADD 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ecc : bv 32 := 0xf24ff0ef.
Lemma F_15ecc : fetch_word Ubsan.M.loaded_segments (0x15fc8 : word) = Some W_15ecc.
Proof. vm_refl. Qed.
Lemma D_15ecc : decode_any W_15ecc = Some (Jal 1 2094884, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ed0 : bv 32 := 0x0204a503.
Lemma F_15ed0 : fetch_word Ubsan.M.loaded_segments (0x15fcc : word) = Some W_15ed0.
Proof. vm_refl. Qed.
Lemma D_15ed0 : decode_any W_15ed0 = Some (Load SZ4 true 10 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ed4 : bv 32 := 0x02a42023.
Lemma F_15ed4 : fetch_word Ubsan.M.loaded_segments (0x15fd0 : word) = Some W_15ed4.
Proof. vm_refl. Qed.
Lemma D_15ed4 : decode_any W_15ed4 = Some (Store SZ4 8 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ed8 : bv 32 := 0x00040513.
Lemma F_15ed8 : fetch_word Ubsan.M.loaded_segments (0x15fd4 : word) = Some W_15ed8.
Proof. vm_refl. Qed.
Lemma D_15ed8 : decode_any W_15ed8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15edc : bv 32 := 0x00000593.
Lemma F_15edc : fetch_word Ubsan.M.loaded_segments (0x15fd8 : word) = Some W_15edc.
Proof. vm_refl. Qed.
Lemma D_15edc : decode_any W_15edc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ee0 : bv 32 := 0x131010ef.
Lemma F_15ee0 : fetch_word Ubsan.M.loaded_segments (0x15fdc : word) = Some W_15ee0.
Proof. vm_refl. Qed.
Lemma D_15ee0 : decode_any W_15ee0 = Some (Jal 1 6448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ee4 : bv 32 := 0x00040513.
Lemma F_15ee4 : fetch_word Ubsan.M.loaded_segments (0x15fe0 : word) = Some W_15ee4.
Proof. vm_refl. Qed.
Lemma D_15ee4 : decode_any W_15ee4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ee8 : bv 32 := 0x01813083.
Lemma F_15ee8 : fetch_word Ubsan.M.loaded_segments (0x15fe4 : word) = Some W_15ee8.
Proof. vm_refl. Qed.
Lemma D_15ee8 : decode_any W_15ee8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15eec : bv 32 := 0x01013403.
Lemma F_15eec : fetch_word Ubsan.M.loaded_segments (0x15fe8 : word) = Some W_15eec.
Proof. vm_refl. Qed.
Lemma D_15eec : decode_any W_15eec = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ef0 : bv 32 := 0x00813483.
Lemma F_15ef0 : fetch_word Ubsan.M.loaded_segments (0x15fec : word) = Some W_15ef0.
Proof. vm_refl. Qed.
Lemma D_15ef0 : decode_any W_15ef0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ef4 : bv 32 := 0x00013903.
Lemma F_15ef4 : fetch_word Ubsan.M.loaded_segments (0x15ff0 : word) = Some W_15ef4.
Proof. vm_refl. Qed.
Lemma D_15ef4 : decode_any W_15ef4 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ef8 : bv 32 := 0x02010113.
Lemma F_15ef8 : fetch_word Ubsan.M.loaded_segments (0x15ff4 : word) = Some W_15ef8.
Proof. vm_refl. Qed.
Lemma D_15ef8 : decode_any W_15ef8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15efc : bv 32 := 0x00008067.
Lemma F_15efc : fetch_word Ubsan.M.loaded_segments (0x15ff8 : word) = Some W_15efc.
Proof. vm_refl. Qed.
Lemma D_15efc : decode_any W_15efc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f04 : bv 32 := 0x0035f713.
Lemma F_15f04 : fetch_word Ubsan.M.loaded_segments (0x16000 : word) = Some W_15f04.
Proof. vm_refl. Qed.
Lemma D_15f04 : decode_any W_15f04 = Some (OpImm ALU_AND 14 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f08 : bv 32 := 0x00058663.
Lemma F_15f08 : fetch_word Ubsan.M.loaded_segments (0x16004 : word) = Some W_15f08.
Proof. vm_refl. Qed.
Lemma D_15f08 : decode_any W_15f08 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f0c : bv 32 := 0x0a071863.
Lemma F_15f0c : fetch_word Ubsan.M.loaded_segments (0x16008 : word) = Some W_15f0c.
Proof. vm_refl. Qed.
Lemma D_15f0c : decode_any W_15f0c = Some (Branch BC_NE 14 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f10 : bv 32 := 0x0005a023.
Lemma F_15f10 : fetch_word Ubsan.M.loaded_segments (0x1600c : word) = Some W_15f10.
Proof. vm_refl. Qed.
Lemma D_15f10 : decode_any W_15f10 = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f14 : bv 32 := 0x00367793.
Lemma F_15f14 : fetch_word Ubsan.M.loaded_segments (0x16010 : word) = Some W_15f14.
Proof. vm_refl. Qed.
Lemma D_15f14 : decode_any W_15f14 = Some (OpImm ALU_AND 15 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f18 : bv 32 := 0x00060663.
Lemma F_15f18 : fetch_word Ubsan.M.loaded_segments (0x16014 : word) = Some W_15f18.
Proof. vm_refl. Qed.
Lemma D_15f18 : decode_any W_15f18 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f1c : bv 32 := 0x0a079063.
Lemma F_15f1c : fetch_word Ubsan.M.loaded_segments (0x16018 : word) = Some W_15f1c.
Proof. vm_refl. Qed.
Lemma D_15f1c : decode_any W_15f1c = Some (Branch BC_NE 15 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f20 : bv 32 := 0x00062023.
Lemma F_15f20 : fetch_word Ubsan.M.loaded_segments (0x1601c : word) = Some W_15f20.
Proof. vm_refl. Qed.
Lemma D_15f20 : decode_any W_15f20 = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f24 : bv 32 := 0x0036f813.
Lemma F_15f24 : fetch_word Ubsan.M.loaded_segments (0x16020 : word) = Some W_15f24.
Proof. vm_refl. Qed.
Lemma D_15f24 : decode_any W_15f24 = Some (OpImm ALU_AND 16 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f28 : bv 32 := 0x00068663.
Lemma F_15f28 : fetch_word Ubsan.M.loaded_segments (0x16024 : word) = Some W_15f28.
Proof. vm_refl. Qed.
Lemma D_15f28 : decode_any W_15f28 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f2c : bv 32 := 0x08081863.
Lemma F_15f2c : fetch_word Ubsan.M.loaded_segments (0x16028 : word) = Some W_15f2c.
Proof. vm_refl. Qed.
Lemma D_15f2c : decode_any W_15f2c = Some (Branch BC_NE 16 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f30 : bv 32 := 0x0006a023.
Lemma F_15f30 : fetch_word Ubsan.M.loaded_segments (0x1602c : word) = Some W_15f30.
Proof. vm_refl. Qed.
Lemma D_15f30 : decode_any W_15f30 = Some (Store SZ4 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f34 : bv 32 := 0x04050663.
Lemma F_15f34 : fetch_word Ubsan.M.loaded_segments (0x16030 : word) = Some W_15f34.
Proof. vm_refl. Qed.
Lemma D_15f34 : decode_any W_15f34 = Some (Branch BC_EQ 10 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f38 : bv 32 := 0x00757893.
Lemma F_15f38 : fetch_word Ubsan.M.loaded_segments (0x16034 : word) = Some W_15f38.
Proof. vm_refl. Qed.
Lemma D_15f38 : decode_any W_15f38 = Some (OpImm ALU_AND 17 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f3c : bv 32 := 0x00058a63.
Lemma F_15f3c : fetch_word Ubsan.M.loaded_segments (0x16038 : word) = Some W_15f3c.
Proof. vm_refl. Qed.
Lemma D_15f3c : decode_any W_15f3c = Some (Branch BC_EQ 11 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f40 : bv 32 := 0x00e8e733.
Lemma F_15f40 : fetch_word Ubsan.M.loaded_segments (0x1603c : word) = Some W_15f40.
Proof. vm_refl. Qed.
Lemma D_15f40 : decode_any W_15f40 = Some (Op ALU_OR 14 17 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f44 : bv 32 := 0x06071c63.
Lemma F_15f44 : fetch_word Ubsan.M.loaded_segments (0x16040 : word) = Some W_15f44.
Proof. vm_refl. Qed.
Lemma D_15f44 : decode_any W_15f44 = Some (Branch BC_NE 14 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f48 : bv 32 := 0x00052703.
Lemma F_15f48 : fetch_word Ubsan.M.loaded_segments (0x16044 : word) = Some W_15f48.
Proof. vm_refl. Qed.
Lemma D_15f48 : decode_any W_15f48 = Some (Load SZ4 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f4c : bv 32 := 0x00e5a023.
Lemma F_15f4c : fetch_word Ubsan.M.loaded_segments (0x16048 : word) = Some W_15f4c.
Proof. vm_refl. Qed.
Lemma D_15f4c : decode_any W_15f4c = Some (Store SZ4 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f50 : bv 32 := 0x00060a63.
Lemma F_15f50 : fetch_word Ubsan.M.loaded_segments (0x1604c : word) = Some W_15f50.
Proof. vm_refl. Qed.
Lemma D_15f50 : decode_any W_15f50 = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f54 : bv 32 := 0x00f8e5b3.
Lemma F_15f54 : fetch_word Ubsan.M.loaded_segments (0x16050 : word) = Some W_15f54.
Proof. vm_refl. Qed.
Lemma D_15f54 : decode_any W_15f54 = Some (Op ALU_OR 11 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f58 : bv 32 := 0x06059263.
Lemma F_15f58 : fetch_word Ubsan.M.loaded_segments (0x16054 : word) = Some W_15f58.
Proof. vm_refl. Qed.
Lemma D_15f58 : decode_any W_15f58 = Some (Branch BC_NE 11 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f5c : bv 32 := 0x00452583.
Lemma F_15f5c : fetch_word Ubsan.M.loaded_segments (0x16058 : word) = Some W_15f5c.
Proof. vm_refl. Qed.
Lemma D_15f5c : decode_any W_15f5c = Some (Load SZ4 true 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f60 : bv 32 := 0x00b62023.
Lemma F_15f60 : fetch_word Ubsan.M.loaded_segments (0x1605c : word) = Some W_15f60.
Proof. vm_refl. Qed.
Lemma D_15f60 : decode_any W_15f60 = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f64 : bv 32 := 0x04068463.
Lemma F_15f64 : fetch_word Ubsan.M.loaded_segments (0x16060 : word) = Some W_15f64.
Proof. vm_refl. Qed.
Lemma D_15f64 : decode_any W_15f64 = Some (Branch BC_EQ 13 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f68 : bv 32 := 0x0108e5b3.
Lemma F_15f68 : fetch_word Ubsan.M.loaded_segments (0x16064 : word) = Some W_15f68.
Proof. vm_refl. Qed.
Lemma D_15f68 : decode_any W_15f68 = Some (Op ALU_OR 11 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f6c : bv 32 := 0x04059863.
Lemma F_15f6c : fetch_word Ubsan.M.loaded_segments (0x16068 : word) = Some W_15f6c.
Proof. vm_refl. Qed.
Lemma D_15f6c : decode_any W_15f6c = Some (Branch BC_NE 11 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f70 : bv 32 := 0x00852503.
Lemma F_15f70 : fetch_word Ubsan.M.loaded_segments (0x1606c : word) = Some W_15f70.
Proof. vm_refl. Qed.
Lemma D_15f70 : decode_any W_15f70 = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f74 : bv 32 := 0x00a6a023.
Lemma F_15f74 : fetch_word Ubsan.M.loaded_segments (0x16070 : word) = Some W_15f74.
Proof. vm_refl. Qed.
Lemma D_15f74 : decode_any W_15f74 = Some (Store SZ4 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f78 : bv 32 := 0x00058513.
Lemma F_15f78 : fetch_word Ubsan.M.loaded_segments (0x16074 : word) = Some W_15f78.
Proof. vm_refl. Qed.
Lemma D_15f78 : decode_any W_15f78 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f7c : bv 32 := 0x00008067.
Lemma F_15f7c : fetch_word Ubsan.M.loaded_segments (0x16078 : word) = Some W_15f7c.
Proof. vm_refl. Qed.
Lemma D_15f7c : decode_any W_15f7c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
