(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.H Require GcFlushU8.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.colorfill_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_153f8 : bv 32 := 0xfe010113.
Lemma F_153f8 : fetch_word Ubsan.M.loaded_segments (0x154fc : word) = Some W_153f8.
Proof. vm_refl. Qed.
Lemma D_153f8 : decode_any W_153f8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153fc : bv 32 := 0x00113c23.
Lemma F_153fc : fetch_word Ubsan.M.loaded_segments (0x15500 : word) = Some W_153fc.
Proof. vm_refl. Qed.
Lemma D_153fc : decode_any W_153fc = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15400 : bv 32 := 0x00813823.
Lemma F_15400 : fetch_word Ubsan.M.loaded_segments (0x15504 : word) = Some W_15400.
Proof. vm_refl. Qed.
Lemma D_15400 : decode_any W_15400 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15404 : bv 32 := 0x00913423.
Lemma F_15404 : fetch_word Ubsan.M.loaded_segments (0x15508 : word) = Some W_15404.
Proof. vm_refl. Qed.
Lemma D_15404 : decode_any W_15404 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15408 : bv 32 := 0x08050063.
Lemma F_15408 : fetch_word Ubsan.M.loaded_segments (0x1550c : word) = Some W_15408.
Proof. vm_refl. Qed.
Lemma D_15408 : decode_any W_15408 = Some (Branch BC_EQ 10 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1540c : bv 32 := 0x00757593.
Lemma F_1540c : fetch_word Ubsan.M.loaded_segments (0x15510 : word) = Some W_1540c.
Proof. vm_refl. Qed.
Lemma D_1540c : decode_any W_1540c = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15410 : bv 32 := 0x0c059263.
Lemma F_15410 : fetch_word Ubsan.M.loaded_segments (0x15514 : word) = Some W_15410.
Proof. vm_refl. Qed.
Lemma D_15410 : decode_any W_15410 = Some (Branch BC_NE 11 0 196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15414 : bv 32 := 0x00053403.
Lemma F_15414 : fetch_word Ubsan.M.loaded_segments (0x15518 : word) = Some W_15414.
Proof. vm_refl. Qed.
Lemma D_15414 : decode_any W_15414 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15418 : bv 32 := 0x0a040463.
Lemma F_15418 : fetch_word Ubsan.M.loaded_segments (0x1551c : word) = Some W_15418.
Proof. vm_refl. Qed.
Lemma D_15418 : decode_any W_15418 = Some (Branch BC_EQ 8 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1541c : bv 32 := 0x00747593.
Lemma F_1541c : fetch_word Ubsan.M.loaded_segments (0x15520 : word) = Some W_1541c.
Proof. vm_refl. Qed.
Lemma D_1541c : decode_any W_1541c = Some (OpImm ALU_AND 11 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15420 : bv 32 := 0x0a059a63.
Lemma F_15420 : fetch_word Ubsan.M.loaded_segments (0x15524 : word) = Some W_15420.
Proof. vm_refl. Qed.
Lemma D_15420 : decode_any W_15420 = Some (Branch BC_NE 11 0 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15424 : bv 32 := 0x01440593.
Lemma F_15424 : fetch_word Ubsan.M.loaded_segments (0x15528 : word) = Some W_15424.
Proof. vm_refl. Qed.
Lemma D_15424 : decode_any W_15424 = Some (OpImm ALU_ADD 11 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15428 : bv 32 := 0xfff00613.
Lemma F_15428 : fetch_word Ubsan.M.loaded_segments (0x1552c : word) = Some W_15428.
Proof. vm_refl. Qed.
Lemma D_15428 : decode_any W_15428 = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1542c : bv 32 := 0x06c5a5af.
Lemma F_1542c : fetch_word Ubsan.M.loaded_segments (0x15530 : word) = Some W_1542c.
Proof. vm_refl. Qed.
Lemma D_1542c : decode_any W_1542c = Some (Amo AMO_ADD AW true true 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15430 : bv 32 := 0x00100613.
Lemma F_15430 : fetch_word Ubsan.M.loaded_segments (0x15534 : word) = Some W_15430.
Proof. vm_refl. Qed.
Lemma D_15430 : decode_any W_15430 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15434 : bv 32 := 0x04c59663.
Lemma F_15434 : fetch_word Ubsan.M.loaded_segments (0x15538 : word) = Some W_15434.
Proof. vm_refl. Qed.
Lemma D_15434 : decode_any W_15434 = Some (Branch BC_NE 11 12 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15480 : bv 32 := 0x00053023.
Lemma F_15480 : fetch_word Ubsan.M.loaded_segments (0x15584 : word) = Some W_15480.
Proof. vm_refl. Qed.
Lemma D_15480 : decode_any W_15480 = Some (Store SZ8 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15484 : bv 32 := 0x03c0006f.
Lemma F_15484 : fetch_word Ubsan.M.loaded_segments (0x15588 : word) = Some W_15484.
Proof. vm_refl. Qed.
Lemma D_15484 : decode_any W_15484 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154c0 : bv 32 := 0x01813083.
Lemma F_154c0 : fetch_word Ubsan.M.loaded_segments (0x155c4 : word) = Some W_154c0.
Proof. vm_refl. Qed.
Lemma D_154c0 : decode_any W_154c0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154c4 : bv 32 := 0x01013403.
Lemma F_154c4 : fetch_word Ubsan.M.loaded_segments (0x155c8 : word) = Some W_154c4.
Proof. vm_refl. Qed.
Lemma D_154c4 : decode_any W_154c4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154c8 : bv 32 := 0x00813483.
Lemma F_154c8 : fetch_word Ubsan.M.loaded_segments (0x155cc : word) = Some W_154c8.
Proof. vm_refl. Qed.
Lemma D_154c8 : decode_any W_154c8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154cc : bv 32 := 0x02010113.
Lemma F_154cc : fetch_word Ubsan.M.loaded_segments (0x155d0 : word) = Some W_154cc.
Proof. vm_refl. Qed.
Lemma D_154cc : decode_any W_154cc = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154d0 : bv 32 := 0x00008067.
Lemma F_154d0 : fetch_word Ubsan.M.loaded_segments (0x155d4 : word) = Some W_154d0.
Proof. vm_refl. Qed.
Lemma D_154d0 : decode_any W_154d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154d8 : bv 32 := 0x0035f713.
Lemma F_154d8 : fetch_word Ubsan.M.loaded_segments (0x155dc : word) = Some W_154d8.
Proof. vm_refl. Qed.
Lemma D_154d8 : decode_any W_154d8 = Some (OpImm ALU_AND 14 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154dc : bv 32 := 0x00058663.
Lemma F_154dc : fetch_word Ubsan.M.loaded_segments (0x155e0 : word) = Some W_154dc.
Proof. vm_refl. Qed.
Lemma D_154dc : decode_any W_154dc = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154e0 : bv 32 := 0x0a071863.
Lemma F_154e0 : fetch_word Ubsan.M.loaded_segments (0x155e4 : word) = Some W_154e0.
Proof. vm_refl. Qed.
Lemma D_154e0 : decode_any W_154e0 = Some (Branch BC_NE 14 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154e4 : bv 32 := 0x0005a023.
Lemma F_154e4 : fetch_word Ubsan.M.loaded_segments (0x155e8 : word) = Some W_154e4.
Proof. vm_refl. Qed.
Lemma D_154e4 : decode_any W_154e4 = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154e8 : bv 32 := 0x00367793.
Lemma F_154e8 : fetch_word Ubsan.M.loaded_segments (0x155ec : word) = Some W_154e8.
Proof. vm_refl. Qed.
Lemma D_154e8 : decode_any W_154e8 = Some (OpImm ALU_AND 15 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154ec : bv 32 := 0x00060663.
Lemma F_154ec : fetch_word Ubsan.M.loaded_segments (0x155f0 : word) = Some W_154ec.
Proof. vm_refl. Qed.
Lemma D_154ec : decode_any W_154ec = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154f0 : bv 32 := 0x0a079063.
Lemma F_154f0 : fetch_word Ubsan.M.loaded_segments (0x155f4 : word) = Some W_154f0.
Proof. vm_refl. Qed.
Lemma D_154f0 : decode_any W_154f0 = Some (Branch BC_NE 15 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154f4 : bv 32 := 0x00062023.
Lemma F_154f4 : fetch_word Ubsan.M.loaded_segments (0x155f8 : word) = Some W_154f4.
Proof. vm_refl. Qed.
Lemma D_154f4 : decode_any W_154f4 = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154f8 : bv 32 := 0x0036f813.
Lemma F_154f8 : fetch_word Ubsan.M.loaded_segments (0x155fc : word) = Some W_154f8.
Proof. vm_refl. Qed.
Lemma D_154f8 : decode_any W_154f8 = Some (OpImm ALU_AND 16 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154fc : bv 32 := 0x00068663.
Lemma F_154fc : fetch_word Ubsan.M.loaded_segments (0x15600 : word) = Some W_154fc.
Proof. vm_refl. Qed.
Lemma D_154fc : decode_any W_154fc = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15508 : bv 32 := 0x04050663.
Lemma F_15508 : fetch_word Ubsan.M.loaded_segments (0x1560c : word) = Some W_15508.
Proof. vm_refl. Qed.
Lemma D_15508 : decode_any W_15508 = Some (Branch BC_EQ 10 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1550c : bv 32 := 0x00757893.
Lemma F_1550c : fetch_word Ubsan.M.loaded_segments (0x15610 : word) = Some W_1550c.
Proof. vm_refl. Qed.
Lemma D_1550c : decode_any W_1550c = Some (OpImm ALU_AND 17 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15510 : bv 32 := 0x00058a63.
Lemma F_15510 : fetch_word Ubsan.M.loaded_segments (0x15614 : word) = Some W_15510.
Proof. vm_refl. Qed.
Lemma D_15510 : decode_any W_15510 = Some (Branch BC_EQ 11 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15514 : bv 32 := 0x00e8e733.
Lemma F_15514 : fetch_word Ubsan.M.loaded_segments (0x15618 : word) = Some W_15514.
Proof. vm_refl. Qed.
Lemma D_15514 : decode_any W_15514 = Some (Op ALU_OR 14 17 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15518 : bv 32 := 0x06071c63.
Lemma F_15518 : fetch_word Ubsan.M.loaded_segments (0x1561c : word) = Some W_15518.
Proof. vm_refl. Qed.
Lemma D_15518 : decode_any W_15518 = Some (Branch BC_NE 14 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1551c : bv 32 := 0x00052703.
Lemma F_1551c : fetch_word Ubsan.M.loaded_segments (0x15620 : word) = Some W_1551c.
Proof. vm_refl. Qed.
Lemma D_1551c : decode_any W_1551c = Some (Load SZ4 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15520 : bv 32 := 0x00e5a023.
Lemma F_15520 : fetch_word Ubsan.M.loaded_segments (0x15624 : word) = Some W_15520.
Proof. vm_refl. Qed.
Lemma D_15520 : decode_any W_15520 = Some (Store SZ4 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15524 : bv 32 := 0x00060a63.
Lemma F_15524 : fetch_word Ubsan.M.loaded_segments (0x15628 : word) = Some W_15524.
Proof. vm_refl. Qed.
Lemma D_15524 : decode_any W_15524 = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15528 : bv 32 := 0x00f8e5b3.
Lemma F_15528 : fetch_word Ubsan.M.loaded_segments (0x1562c : word) = Some W_15528.
Proof. vm_refl. Qed.
Lemma D_15528 : decode_any W_15528 = Some (Op ALU_OR 11 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1552c : bv 32 := 0x06059263.
Lemma F_1552c : fetch_word Ubsan.M.loaded_segments (0x15630 : word) = Some W_1552c.
Proof. vm_refl. Qed.
Lemma D_1552c : decode_any W_1552c = Some (Branch BC_NE 11 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15530 : bv 32 := 0x00452583.
Lemma F_15530 : fetch_word Ubsan.M.loaded_segments (0x15634 : word) = Some W_15530.
Proof. vm_refl. Qed.
Lemma D_15530 : decode_any W_15530 = Some (Load SZ4 true 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15534 : bv 32 := 0x00b62023.
Lemma F_15534 : fetch_word Ubsan.M.loaded_segments (0x15638 : word) = Some W_15534.
Proof. vm_refl. Qed.
Lemma D_15534 : decode_any W_15534 = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15538 : bv 32 := 0x04068463.
Lemma F_15538 : fetch_word Ubsan.M.loaded_segments (0x1563c : word) = Some W_15538.
Proof. vm_refl. Qed.
Lemma D_15538 : decode_any W_15538 = Some (Branch BC_EQ 13 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15580 : bv 32 := 0x00000513.
Lemma F_15580 : fetch_word Ubsan.M.loaded_segments (0x15684 : word) = Some W_15580.
Proof. vm_refl. Qed.
Lemma D_15580 : decode_any W_15580 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15584 : bv 32 := 0x00008067.
Lemma F_15584 : fetch_word Ubsan.M.loaded_segments (0x15688 : word) = Some W_15584.
Proof. vm_refl. Qed.
Lemma D_15584 : decode_any W_15584 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15814 : bv 32 := 0x00050e63.
Lemma F_15814 : fetch_word Ubsan.M.loaded_segments (0x15918 : word) = Some W_15814.
Proof. vm_refl. Qed.
Lemma D_15814 : decode_any W_15814 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15818 : bv 32 := 0x00757593.
Lemma F_15818 : fetch_word Ubsan.M.loaded_segments (0x1591c : word) = Some W_15818.
Proof. vm_refl. Qed.
Lemma D_15818 : decode_any W_15818 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1581c : bv 32 := 0x04059463.
Lemma F_1581c : fetch_word Ubsan.M.loaded_segments (0x15920 : word) = Some W_1581c.
Proof. vm_refl. Qed.
Lemma D_1581c : decode_any W_1581c = Some (Branch BC_NE 11 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15820 : bv 32 := 0x01450593.
Lemma F_15820 : fetch_word Ubsan.M.loaded_segments (0x15924 : word) = Some W_15820.
Proof. vm_refl. Qed.
Lemma D_15820 : decode_any W_15820 = Some (OpImm ALU_ADD 11 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15824 : bv 32 := 0x00100613.
Lemma F_15824 : fetch_word Ubsan.M.loaded_segments (0x15928 : word) = Some W_15824.
Proof. vm_refl. Qed.
Lemma D_15824 : decode_any W_15824 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15828 : bv 32 := 0x06c5a02f.
Lemma F_15828 : fetch_word Ubsan.M.loaded_segments (0x1592c : word) = Some W_15828.
Proof. vm_refl. Qed.
Lemma D_15828 : decode_any W_15828 = Some (Amo AMO_ADD AW true true 0 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1582c : bv 32 := 0x00008067.
Lemma F_1582c : fetch_word Ubsan.M.loaded_segments (0x15930 : word) = Some W_1582c.
Proof. vm_refl. Qed.
Lemma D_1582c : decode_any W_1582c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158b4 : bv 32 := 0x00050a63.
Lemma F_158b4 : fetch_word Ubsan.M.loaded_segments (0x159b8 : word) = Some W_158b4.
Proof. vm_refl. Qed.
Lemma D_158b4 : decode_any W_158b4 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158b8 : bv 32 := 0x00757593.
Lemma F_158b8 : fetch_word Ubsan.M.loaded_segments (0x159bc : word) = Some W_158b8.
Proof. vm_refl. Qed.
Lemma D_158b8 : decode_any W_158b8 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158bc : bv 32 := 0x04059063.
Lemma F_158bc : fetch_word Ubsan.M.loaded_segments (0x159c0 : word) = Some W_158bc.
Proof. vm_refl. Qed.
Lemma D_158bc : decode_any W_158bc = Some (Branch BC_NE 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158c0 : bv 32 := 0x00852503.
Lemma F_158c0 : fetch_word Ubsan.M.loaded_segments (0x159c4 : word) = Some W_158c0.
Proof. vm_refl. Qed.
Lemma D_158c0 : decode_any W_158c0 = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158c4 : bv 32 := 0x00008067.
Lemma F_158c4 : fetch_word Ubsan.M.loaded_segments (0x159c8 : word) = Some W_158c4.
Proof. vm_refl. Qed.
Lemma D_158c4 : decode_any W_158c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
