(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.H Require GcFlushS14.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_15270 : bv 32 := 0xff010113.
Lemma F_15270 : fetch_word Plain.M.loaded_segments (0x1536c : word) = Some W_15270.
Proof. vm_refl. Qed.
Lemma D_15270 : decode_any W_15270 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15274 : bv 32 := 0x00113423.
Lemma F_15274 : fetch_word Plain.M.loaded_segments (0x15370 : word) = Some W_15274.
Proof. vm_refl. Qed.
Lemma D_15274 : decode_any W_15274 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15278 : bv 32 := 0x00813023.
Lemma F_15278 : fetch_word Plain.M.loaded_segments (0x15374 : word) = Some W_15278.
Proof. vm_refl. Qed.
Lemma D_15278 : decode_any W_15278 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1527c : bv 32 := 0x00060413.
Lemma F_1527c : fetch_word Plain.M.loaded_segments (0x15378 : word) = Some W_1527c.
Proof. vm_refl. Qed.
Lemma D_1527c : decode_any W_1527c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15280 : bv 32 := 0x00050613.
Lemma F_15280 : fetch_word Plain.M.loaded_segments (0x1537c : word) = Some W_15280.
Proof. vm_refl. Qed.
Lemma D_15280 : decode_any W_15280 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15284 : bv 32 := 0xffffc517.
Lemma F_15284 : fetch_word Plain.M.loaded_segments (0x15380 : word) = Some W_15284.
Proof. vm_refl. Qed.
Lemma D_15284 : decode_any W_15284 = Some (Auipc 10 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15288 : bv 32 := 0x02350513.
Lemma F_15288 : fetch_word Plain.M.loaded_segments (0x15384 : word) = Some W_15288.
Proof. vm_refl. Qed.
Lemma D_15288 : decode_any W_15288 = Some (OpImm ALU_ADD 10 10 35, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1528c : bv 32 := 0x018000ef.
Lemma F_1528c : fetch_word Plain.M.loaded_segments (0x15388 : word) = Some W_1528c.
Proof. vm_refl. Qed.
Lemma D_1528c : decode_any W_1528c = Some (Jal 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15290 : bv 32 := 0x00040513.
Lemma F_15290 : fetch_word Plain.M.loaded_segments (0x1538c : word) = Some W_15290.
Proof. vm_refl. Qed.
Lemma D_15290 : decode_any W_15290 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15294 : bv 32 := 0x00813083.
Lemma F_15294 : fetch_word Plain.M.loaded_segments (0x15390 : word) = Some W_15294.
Proof. vm_refl. Qed.
Lemma D_15294 : decode_any W_15294 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15298 : bv 32 := 0x00013403.
Lemma F_15298 : fetch_word Plain.M.loaded_segments (0x15394 : word) = Some W_15298.
Proof. vm_refl. Qed.
Lemma D_15298 : decode_any W_15298 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1529c : bv 32 := 0x01010113.
Lemma F_1529c : fetch_word Plain.M.loaded_segments (0x15398 : word) = Some W_1529c.
Proof. vm_refl. Qed.
Lemma D_1529c : decode_any W_1529c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a0 : bv 32 := 0x00008067.
Lemma F_152a0 : fetch_word Plain.M.loaded_segments (0x1539c : word) = Some W_152a0.
Proof. vm_refl. Qed.
Lemma D_152a0 : decode_any W_152a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15340 : bv 32 := 0xff010113.
Lemma F_15340 : fetch_word Plain.M.loaded_segments (0x1543c : word) = Some W_15340.
Proof. vm_refl. Qed.
Lemma D_15340 : decode_any W_15340 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15344 : bv 32 := 0x00113423.
Lemma F_15344 : fetch_word Plain.M.loaded_segments (0x15440 : word) = Some W_15344.
Proof. vm_refl. Qed.
Lemma D_15344 : decode_any W_15344 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15348 : bv 32 := 0x00813023.
Lemma F_15348 : fetch_word Plain.M.loaded_segments (0x15444 : word) = Some W_15348.
Proof. vm_refl. Qed.
Lemma D_15348 : decode_any W_15348 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1534c : bv 32 := 0x00060413.
Lemma F_1534c : fetch_word Plain.M.loaded_segments (0x15448 : word) = Some W_1534c.
Proof. vm_refl. Qed.
Lemma D_1534c : decode_any W_1534c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15350 : bv 32 := 0x00050613.
Lemma F_15350 : fetch_word Plain.M.loaded_segments (0x1544c : word) = Some W_15350.
Proof. vm_refl. Qed.
Lemma D_15350 : decode_any W_15350 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15354 : bv 32 := 0xffffc517.
Lemma F_15354 : fetch_word Plain.M.loaded_segments (0x15450 : word) = Some W_15354.
Proof. vm_refl. Qed.
Lemma D_15354 : decode_any W_15354 = Some (Auipc 10 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15358 : bv 32 := 0xf5350513.
Lemma F_15358 : fetch_word Plain.M.loaded_segments (0x15454 : word) = Some W_15358.
Proof. vm_refl. Qed.
Lemma D_15358 : decode_any W_15358 = Some (OpImm ALU_ADD 10 10 3923, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1535c : bv 32 := 0xf49ff0ef.
Lemma F_1535c : fetch_word Plain.M.loaded_segments (0x15458 : word) = Some W_1535c.
Proof. vm_refl. Qed.
Lemma D_1535c : decode_any W_1535c = Some (Jal 1 2096968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15360 : bv 32 := 0x00040513.
Lemma F_15360 : fetch_word Plain.M.loaded_segments (0x1545c : word) = Some W_15360.
Proof. vm_refl. Qed.
Lemma D_15360 : decode_any W_15360 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15364 : bv 32 := 0x00813083.
Lemma F_15364 : fetch_word Plain.M.loaded_segments (0x15460 : word) = Some W_15364.
Proof. vm_refl. Qed.
Lemma D_15364 : decode_any W_15364 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15368 : bv 32 := 0x00013403.
Lemma F_15368 : fetch_word Plain.M.loaded_segments (0x15464 : word) = Some W_15368.
Proof. vm_refl. Qed.
Lemma D_15368 : decode_any W_15368 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1536c : bv 32 := 0x01010113.
Lemma F_1536c : fetch_word Plain.M.loaded_segments (0x15468 : word) = Some W_1536c.
Proof. vm_refl. Qed.
Lemma D_1536c : decode_any W_1536c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15370 : bv 32 := 0x00008067.
Lemma F_15370 : fetch_word Plain.M.loaded_segments (0x1546c : word) = Some W_15370.
Proof. vm_refl. Qed.
Lemma D_15370 : decode_any W_15370 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154e8 : bv 32 := 0x02050e63.
Lemma F_154e8 : fetch_word Plain.M.loaded_segments (0x155e4 : word) = Some W_154e8.
Proof. vm_refl. Qed.
Lemma D_154e8 : decode_any W_154e8 = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154ec : bv 32 := 0xfe010113.
Lemma F_154ec : fetch_word Plain.M.loaded_segments (0x155e8 : word) = Some W_154ec.
Proof. vm_refl. Qed.
Lemma D_154ec : decode_any W_154ec = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154f0 : bv 32 := 0x00113c23.
Lemma F_154f0 : fetch_word Plain.M.loaded_segments (0x155ec : word) = Some W_154f0.
Proof. vm_refl. Qed.
Lemma D_154f0 : decode_any W_154f0 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154f4 : bv 32 := 0x00813823.
Lemma F_154f4 : fetch_word Plain.M.loaded_segments (0x155f0 : word) = Some W_154f4.
Proof. vm_refl. Qed.
Lemma D_154f4 : decode_any W_154f4 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154f8 : bv 32 := 0x00913423.
Lemma F_154f8 : fetch_word Plain.M.loaded_segments (0x155f4 : word) = Some W_154f8.
Proof. vm_refl. Qed.
Lemma D_154f8 : decode_any W_154f8 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_154fc : bv 32 := 0x00058493.
Lemma F_154fc : fetch_word Plain.M.loaded_segments (0x155f8 : word) = Some W_154fc.
Proof. vm_refl. Qed.
Lemma D_154fc : decode_any W_154fc = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15500 : bv 32 := 0x00050413.
Lemma F_15500 : fetch_word Plain.M.loaded_segments (0x155fc : word) = Some W_15500.
Proof. vm_refl. Qed.
Lemma D_15500 : decode_any W_15500 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15504 : bv 32 := 0x00053503.
Lemma F_15504 : fetch_word Plain.M.loaded_segments (0x15600 : word) = Some W_15504.
Proof. vm_refl. Qed.
Lemma D_15504 : decode_any W_15504 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15508 : bv 32 := 0x00050463.
Lemma F_15508 : fetch_word Plain.M.loaded_segments (0x15604 : word) = Some W_15508.
Proof. vm_refl. Qed.
Lemma D_15508 : decode_any W_15508 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15510 : bv 32 := 0x04048063.
Lemma F_15510 : fetch_word Plain.M.loaded_segments (0x1560c : word) = Some W_15510.
Proof. vm_refl. Qed.
Lemma D_15510 : decode_any W_15510 = Some (Branch BC_EQ 9 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15550 : bv 32 := 0x00000593.
Lemma F_15550 : fetch_word Plain.M.loaded_segments (0x1564c : word) = Some W_15550.
Proof. vm_refl. Qed.
Lemma D_15550 : decode_any W_15550 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15554 : bv 32 := 0x00000513.
Lemma F_15554 : fetch_word Plain.M.loaded_segments (0x15650 : word) = Some W_15554.
Proof. vm_refl. Qed.
Lemma D_15554 : decode_any W_15554 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15558 : bv 32 := 0x00b43023.
Lemma F_15558 : fetch_word Plain.M.loaded_segments (0x15654 : word) = Some W_15558.
Proof. vm_refl. Qed.
Lemma D_15558 : decode_any W_15558 = Some (Store SZ8 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1555c : bv 32 := 0x01813083.
Lemma F_1555c : fetch_word Plain.M.loaded_segments (0x15658 : word) = Some W_1555c.
Proof. vm_refl. Qed.
Lemma D_1555c : decode_any W_1555c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15560 : bv 32 := 0x01013403.
Lemma F_15560 : fetch_word Plain.M.loaded_segments (0x1565c : word) = Some W_15560.
Proof. vm_refl. Qed.
Lemma D_15560 : decode_any W_15560 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15564 : bv 32 := 0x00813483.
Lemma F_15564 : fetch_word Plain.M.loaded_segments (0x15660 : word) = Some W_15564.
Proof. vm_refl. Qed.
Lemma D_15564 : decode_any W_15564 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15568 : bv 32 := 0x02010113.
Lemma F_15568 : fetch_word Plain.M.loaded_segments (0x15664 : word) = Some W_15568.
Proof. vm_refl. Qed.
Lemma D_15568 : decode_any W_15568 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1556c : bv 32 := 0x00008067.
Lemma F_1556c : fetch_word Plain.M.loaded_segments (0x15668 : word) = Some W_1556c.
Proof. vm_refl. Qed.
Lemma D_1556c : decode_any W_1556c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15578 : bv 32 := 0xff010113.
Lemma F_15578 : fetch_word Plain.M.loaded_segments (0x15674 : word) = Some W_15578.
Proof. vm_refl. Qed.
Lemma D_15578 : decode_any W_15578 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1557c : bv 32 := 0x00113423.
Lemma F_1557c : fetch_word Plain.M.loaded_segments (0x15678 : word) = Some W_1557c.
Proof. vm_refl. Qed.
Lemma D_1557c : decode_any W_1557c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15580 : bv 32 := 0x00813023.
Lemma F_15580 : fetch_word Plain.M.loaded_segments (0x1567c : word) = Some W_15580.
Proof. vm_refl. Qed.
Lemma D_15580 : decode_any W_15580 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15584 : bv 32 := 0x080000ef.
Lemma F_15584 : fetch_word Plain.M.loaded_segments (0x15680 : word) = Some W_15584.
Proof. vm_refl. Qed.
Lemma D_15584 : decode_any W_15584 = Some (Jal 1 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15588 : bv 32 := 0x02050863.
Lemma F_15588 : fetch_word Plain.M.loaded_segments (0x15684 : word) = Some W_15588.
Proof. vm_refl. Qed.
Lemma D_15588 : decode_any W_15588 = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1558c : bv 32 := 0x00456603.
Lemma F_1558c : fetch_word Plain.M.loaded_segments (0x15688 : word) = Some W_1558c.
Proof. vm_refl. Qed.
Lemma D_1558c : decode_any W_1558c = Some (Load SZ4 false 12 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15590 : bv 32 := 0x01056683.
Lemma F_15590 : fetch_word Plain.M.loaded_segments (0x1568c : word) = Some W_15590.
Proof. vm_refl. Qed.
Lemma D_15590 : decode_any W_15590 = Some (Load SZ4 false 13 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15594 : bv 32 := 0x03853583.
Lemma F_15594 : fetch_word Plain.M.loaded_segments (0x15690 : word) = Some W_15594.
Proof. vm_refl. Qed.
Lemma D_15594 : decode_any W_15594 = Some (Load SZ8 true 11 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15598 : bv 32 := 0x02c68633.
Lemma F_15598 : fetch_word Plain.M.loaded_segments (0x15694 : word) = Some W_15598.
Proof. vm_refl. Qed.
Lemma D_15598 : decode_any W_15598 = Some (Mul M_MUL 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1559c : bv 32 := 0x00261613.
Lemma F_1559c : fetch_word Plain.M.loaded_segments (0x15698 : word) = Some W_1559c.
Proof. vm_refl. Qed.
Lemma D_1559c : decode_any W_1559c = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155a0 : bv 32 := 0x00050413.
Lemma F_155a0 : fetch_word Plain.M.loaded_segments (0x1569c : word) = Some W_155a0.
Proof. vm_refl. Qed.
Lemma D_155a0 : decode_any W_155a0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155a4 : bv 32 := 0x00058513.
Lemma F_155a4 : fetch_word Plain.M.loaded_segments (0x156a0 : word) = Some W_155a4.
Proof. vm_refl. Qed.
Lemma D_155a4 : decode_any W_155a4 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155a8 : bv 32 := 0x00000593.
Lemma F_155a8 : fetch_word Plain.M.loaded_segments (0x156a4 : word) = Some W_155a8.
Proof. vm_refl. Qed.
Lemma D_155a8 : decode_any W_155a8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155ac : bv 32 := 0x585130ef.
Lemma F_155ac : fetch_word Plain.M.loaded_segments (0x156a8 : word) = Some W_155ac.
Proof. vm_refl. Qed.
Lemma D_155ac : decode_any W_155ac = Some (Jal 1 81284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155b0 : bv 32 := 0x00040513.
Lemma F_155b0 : fetch_word Plain.M.loaded_segments (0x156ac : word) = Some W_155b0.
Proof. vm_refl. Qed.
Lemma D_155b0 : decode_any W_155b0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155b4 : bv 32 := 0x0400006f.
Lemma F_155b4 : fetch_word Plain.M.loaded_segments (0x156b0 : word) = Some W_155b4.
Proof. vm_refl. Qed.
Lemma D_155b4 : decode_any W_155b4 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155b8 : bv 32 := 0x00015517.
Lemma F_155b8 : fetch_word Plain.M.loaded_segments (0x156b4 : word) = Some W_155b8.
Proof. vm_refl. Qed.
Lemma D_155b8 : decode_any W_155b8 = Some (Auipc 10 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155bc : bv 32 := 0x38c53503.
Lemma F_155bc : fetch_word Plain.M.loaded_segments (0x156b8 : word) = Some W_155bc.
Proof. vm_refl. Qed.
Lemma D_155bc : decode_any W_155bc = Some (Load SZ8 true 10 10 908, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155c0 : bv 32 := 0x00052503.
Lemma F_155c0 : fetch_word Plain.M.loaded_segments (0x156bc : word) = Some W_155c0.
Proof. vm_refl. Qed.
Lemma D_155c0 : decode_any W_155c0 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155c4 : bv 32 := 0x00500593.
Lemma F_155c4 : fetch_word Plain.M.loaded_segments (0x156c0 : word) = Some W_155c4.
Proof. vm_refl. Qed.
Lemma D_155c4 : decode_any W_155c4 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155c8 : bv 32 := 0x02a5c463.
Lemma F_155c8 : fetch_word Plain.M.loaded_segments (0x156c4 : word) = Some W_155c8.
Proof. vm_refl. Qed.
Lemma D_155c8 : decode_any W_155c8 = Some (Branch BC_LT 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155cc : bv 32 := 0xffffb517.
Lemma F_155cc : fetch_word Plain.M.loaded_segments (0x156c8 : word) = Some W_155cc.
Proof. vm_refl. Qed.
Lemma D_155cc : decode_any W_155cc = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155d0 : bv 32 := 0xffffb597.
Lemma F_155d0 : fetch_word Plain.M.loaded_segments (0x156cc : word) = Some W_155d0.
Proof. vm_refl. Qed.
Lemma D_155d0 : decode_any W_155d0 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155d4 : bv 32 := 0xdf550513.
Lemma F_155d4 : fetch_word Plain.M.loaded_segments (0x156d0 : word) = Some W_155d4.
Proof. vm_refl. Qed.
Lemma D_155d4 : decode_any W_155d4 = Some (OpImm ALU_ADD 10 10 3573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155d8 : bv 32 := 0x1dd58593.
Lemma F_155d8 : fetch_word Plain.M.loaded_segments (0x156d4 : word) = Some W_155d8.
Proof. vm_refl. Qed.
Lemma D_155d8 : decode_any W_155d8 = Some (OpImm ALU_ADD 11 11 477, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155dc : bv 32 := 0x00000613.
Lemma F_155dc : fetch_word Plain.M.loaded_segments (0x156d8 : word) = Some W_155dc.
Proof. vm_refl. Qed.
Lemma D_155dc : decode_any W_155dc = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155e0 : bv 32 := 0x00813083.
Lemma F_155e0 : fetch_word Plain.M.loaded_segments (0x156dc : word) = Some W_155e0.
Proof. vm_refl. Qed.
Lemma D_155e0 : decode_any W_155e0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155e4 : bv 32 := 0x00013403.
Lemma F_155e4 : fetch_word Plain.M.loaded_segments (0x156e0 : word) = Some W_155e4.
Proof. vm_refl. Qed.
Lemma D_155e4 : decode_any W_155e4 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155e8 : bv 32 := 0x01010113.
Lemma F_155e8 : fetch_word Plain.M.loaded_segments (0x156e4 : word) = Some W_155e8.
Proof. vm_refl. Qed.
Lemma D_155e8 : decode_any W_155e8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155ec : bv 32 := 0xd55ff06f.
Lemma F_155ec : fetch_word Plain.M.loaded_segments (0x156e8 : word) = Some W_155ec.
Proof. vm_refl. Qed.
Lemma D_155ec : decode_any W_155ec = Some (Jal 0 2096468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155f4 : bv 32 := 0x00813083.
Lemma F_155f4 : fetch_word Plain.M.loaded_segments (0x156f0 : word) = Some W_155f4.
Proof. vm_refl. Qed.
Lemma D_155f4 : decode_any W_155f4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155f8 : bv 32 := 0x00013403.
Lemma F_155f8 : fetch_word Plain.M.loaded_segments (0x156f4 : word) = Some W_155f8.
Proof. vm_refl. Qed.
Lemma D_155f8 : decode_any W_155f8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155fc : bv 32 := 0x01010113.
Lemma F_155fc : fetch_word Plain.M.loaded_segments (0x156f8 : word) = Some W_155fc.
Proof. vm_refl. Qed.
Lemma D_155fc : decode_any W_155fc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15600 : bv 32 := 0x00008067.
Lemma F_15600 : fetch_word Plain.M.loaded_segments (0x156fc : word) = Some W_15600.
Proof. vm_refl. Qed.
Lemma D_15600 : decode_any W_15600 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15604 : bv 32 := 0xfd010113.
Lemma F_15604 : fetch_word Plain.M.loaded_segments (0x15700 : word) = Some W_15604.
Proof. vm_refl. Qed.
Lemma D_15604 : decode_any W_15604 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15608 : bv 32 := 0x02113423.
Lemma F_15608 : fetch_word Plain.M.loaded_segments (0x15704 : word) = Some W_15608.
Proof. vm_refl. Qed.
Lemma D_15608 : decode_any W_15608 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1560c : bv 32 := 0x02813023.
Lemma F_1560c : fetch_word Plain.M.loaded_segments (0x15708 : word) = Some W_1560c.
Proof. vm_refl. Qed.
Lemma D_1560c : decode_any W_1560c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15610 : bv 32 := 0x00913c23.
Lemma F_15610 : fetch_word Plain.M.loaded_segments (0x1570c : word) = Some W_15610.
Proof. vm_refl. Qed.
Lemma D_15610 : decode_any W_15610 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15614 : bv 32 := 0x01213823.
Lemma F_15614 : fetch_word Plain.M.loaded_segments (0x15710 : word) = Some W_15614.
Proof. vm_refl. Qed.
Lemma D_15614 : decode_any W_15614 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15618 : bv 32 := 0x00058493.
Lemma F_15618 : fetch_word Plain.M.loaded_segments (0x15714 : word) = Some W_15618.
Proof. vm_refl. Qed.
Lemma D_15618 : decode_any W_15618 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1561c : bv 32 := 0x124000ef.
Lemma F_1561c : fetch_word Plain.M.loaded_segments (0x15718 : word) = Some W_1561c.
Proof. vm_refl. Qed.
Lemma D_1561c : decode_any W_1561c = Some (Jal 1 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15620 : bv 32 := 0x02050e63.
Lemma F_15620 : fetch_word Plain.M.loaded_segments (0x1571c : word) = Some W_15620.
Proof. vm_refl. Qed.
Lemma D_15620 : decode_any W_15620 = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15624 : bv 32 := 0x00050413.
Lemma F_15624 : fetch_word Plain.M.loaded_segments (0x15720 : word) = Some W_15624.
Proof. vm_refl. Qed.
Lemma D_15624 : decode_any W_15624 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15628 : bv 32 := 0x01052503.
Lemma F_15628 : fetch_word Plain.M.loaded_segments (0x15724 : word) = Some W_15628.
Proof. vm_refl. Qed.
Lemma D_15628 : decode_any W_15628 = Some (Load SZ4 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1562c : bv 32 := 0x00016597.
Lemma F_1562c : fetch_word Plain.M.loaded_segments (0x15728 : word) = Some W_1562c.
Proof. vm_refl. Qed.
Lemma D_1562c : decode_any W_1562c = Some (Auipc 11 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15630 : bv 32 := 0x39858913.
Lemma F_15630 : fetch_word Plain.M.loaded_segments (0x1572c : word) = Some W_15630.
Proof. vm_refl. Qed.
Lemma D_15630 : decode_any W_15630 = Some (OpImm ALU_ADD 18 11 920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15634 : bv 32 := 0x00093583.
Lemma F_15634 : fetch_word Plain.M.loaded_segments (0x15730 : word) = Some W_15634.
Proof. vm_refl. Qed.
Lemma D_15634 : decode_any W_15634 = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15638 : bv 32 := 0x02a48533.
Lemma F_15638 : fetch_word Plain.M.loaded_segments (0x15734 : word) = Some W_15638.
Proof. vm_refl. Qed.
Lemma D_15638 : decode_any W_15638 = Some (Mul M_MUL 10 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1563c : bv 32 := 0x00251513.
Lemma F_1563c : fetch_word Plain.M.loaded_segments (0x15738 : word) = Some W_1563c.
Proof. vm_refl. Qed.
Lemma D_1563c : decode_any W_1563c = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15640 : bv 32 := 0x000580e7.
Lemma F_15640 : fetch_word Plain.M.loaded_segments (0x1573c : word) = Some W_15640.
Proof. vm_refl. Qed.
Lemma D_15640 : decode_any W_15640 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15644 : bv 32 := 0x04050c63.
Lemma F_15644 : fetch_word Plain.M.loaded_segments (0x15740 : word) = Some W_15644.
Proof. vm_refl. Qed.
Lemma D_15644 : decode_any W_15644 = Some (Branch BC_EQ 10 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15648 : bv 32 := 0x02a43c23.
Lemma F_15648 : fetch_word Plain.M.loaded_segments (0x15744 : word) = Some W_15648.
Proof. vm_refl. Qed.
Lemma D_15648 : decode_any W_15648 = Some (Store SZ8 8 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1564c : bv 32 := 0x00040513.
Lemma F_1564c : fetch_word Plain.M.loaded_segments (0x15748 : word) = Some W_1564c.
Proof. vm_refl. Qed.
Lemma D_1564c : decode_any W_1564c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15650 : bv 32 := 0x00000593.
Lemma F_15650 : fetch_word Plain.M.loaded_segments (0x1574c : word) = Some W_15650.
Proof. vm_refl. Qed.
Lemma D_15650 : decode_any W_15650 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15654 : bv 32 := 0x279010ef.
Lemma F_15654 : fetch_word Plain.M.loaded_segments (0x15750 : word) = Some W_15654.
Proof. vm_refl. Qed.
Lemma D_15654 : decode_any W_15654 = Some (Jal 1 6776, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15658 : bv 32 := 0x0cc0006f.
Lemma F_15658 : fetch_word Plain.M.loaded_segments (0x15754 : word) = Some W_15658.
Proof. vm_refl. Qed.
Lemma D_15658 : decode_any W_15658 = Some (Jal 0 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1565c : bv 32 := 0x00015517.
Lemma F_1565c : fetch_word Plain.M.loaded_segments (0x15758 : word) = Some W_1565c.
Proof. vm_refl. Qed.
Lemma D_1565c : decode_any W_1565c = Some (Auipc 10 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15660 : bv 32 := 0x2e853503.
Lemma F_15660 : fetch_word Plain.M.loaded_segments (0x1575c : word) = Some W_15660.
Proof. vm_refl. Qed.
Lemma D_15660 : decode_any W_15660 = Some (Load SZ8 true 10 10 744, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15664 : bv 32 := 0x00052503.
Lemma F_15664 : fetch_word Plain.M.loaded_segments (0x15760 : word) = Some W_15664.
Proof. vm_refl. Qed.
Lemma D_15664 : decode_any W_15664 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15668 : bv 32 := 0x00500593.
Lemma F_15668 : fetch_word Plain.M.loaded_segments (0x15764 : word) = Some W_15668.
Proof. vm_refl. Qed.
Lemma D_15668 : decode_any W_15668 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1566c : bv 32 := 0x0aa5ca63.
Lemma F_1566c : fetch_word Plain.M.loaded_segments (0x15768 : word) = Some W_1566c.
Proof. vm_refl. Qed.
Lemma D_1566c : decode_any W_1566c = Some (Branch BC_LT 11 10 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15670 : bv 32 := 0xffffb517.
Lemma F_15670 : fetch_word Plain.M.loaded_segments (0x1576c : word) = Some W_15670.
Proof. vm_refl. Qed.
Lemma D_15670 : decode_any W_15670 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15674 : bv 32 := 0xffffb597.
Lemma F_15674 : fetch_word Plain.M.loaded_segments (0x15770 : word) = Some W_15674.
Proof. vm_refl. Qed.
Lemma D_15674 : decode_any W_15674 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15678 : bv 32 := 0xd5150513.
Lemma F_15678 : fetch_word Plain.M.loaded_segments (0x15774 : word) = Some W_15678.
Proof. vm_refl. Qed.
Lemma D_15678 : decode_any W_15678 = Some (OpImm ALU_ADD 10 10 3409, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1567c : bv 32 := 0xf0158593.
Lemma F_1567c : fetch_word Plain.M.loaded_segments (0x15778 : word) = Some W_1567c.
Proof. vm_refl. Qed.
Lemma D_1567c : decode_any W_1567c = Some (OpImm ALU_ADD 11 11 3841, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15680 : bv 32 := 0x00000613.
Lemma F_15680 : fetch_word Plain.M.loaded_segments (0x1577c : word) = Some W_15680.
Proof. vm_refl. Qed.
Lemma D_15680 : decode_any W_15680 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15684 : bv 32 := 0x02813083.
Lemma F_15684 : fetch_word Plain.M.loaded_segments (0x15780 : word) = Some W_15684.
Proof. vm_refl. Qed.
Lemma D_15684 : decode_any W_15684 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15688 : bv 32 := 0x02013403.
Lemma F_15688 : fetch_word Plain.M.loaded_segments (0x15784 : word) = Some W_15688.
Proof. vm_refl. Qed.
Lemma D_15688 : decode_any W_15688 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1568c : bv 32 := 0x01813483.
Lemma F_1568c : fetch_word Plain.M.loaded_segments (0x15788 : word) = Some W_1568c.
Proof. vm_refl. Qed.
Lemma D_1568c : decode_any W_1568c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15690 : bv 32 := 0x01013903.
Lemma F_15690 : fetch_word Plain.M.loaded_segments (0x1578c : word) = Some W_15690.
Proof. vm_refl. Qed.
Lemma D_15690 : decode_any W_15690 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15694 : bv 32 := 0x03010113.
Lemma F_15694 : fetch_word Plain.M.loaded_segments (0x15790 : word) = Some W_15694.
Proof. vm_refl. Qed.
Lemma D_15694 : decode_any W_15694 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15698 : bv 32 := 0xca9ff06f.
Lemma F_15698 : fetch_word Plain.M.loaded_segments (0x15794 : word) = Some W_15698.
Proof. vm_refl. Qed.
Lemma D_15698 : decode_any W_15698 = Some (Jal 0 2096296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1569c : bv 32 := 0x01440513.
Lemma F_1569c : fetch_word Plain.M.loaded_segments (0x15798 : word) = Some W_1569c.
Proof. vm_refl. Qed.
Lemma D_1569c : decode_any W_1569c = Some (OpImm ALU_ADD 10 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156a0 : bv 32 := 0xfff00593.
Lemma F_156a0 : fetch_word Plain.M.loaded_segments (0x1579c : word) = Some W_156a0.
Proof. vm_refl. Qed.
Lemma D_156a0 : decode_any W_156a0 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156a4 : bv 32 := 0x06b5252f.
Lemma F_156a4 : fetch_word Plain.M.loaded_segments (0x157a0 : word) = Some W_156a4.
Proof. vm_refl. Qed.
Lemma D_156a4 : decode_any W_156a4 = Some (Amo AMO_ADD AW true true 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156a8 : bv 32 := 0x00100593.
Lemma F_156a8 : fetch_word Plain.M.loaded_segments (0x157a4 : word) = Some W_156a8.
Proof. vm_refl. Qed.
Lemma D_156a8 : decode_any W_156a8 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156ac : bv 32 := 0x04b51063.
Lemma F_156ac : fetch_word Plain.M.loaded_segments (0x157a8 : word) = Some W_156ac.
Proof. vm_refl. Qed.
Lemma D_156ac : decode_any W_156ac = Some (Branch BC_NE 10 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156b0 : bv 32 := 0x03843503.
Lemma F_156b0 : fetch_word Plain.M.loaded_segments (0x157ac : word) = Some W_156b0.
Proof. vm_refl. Qed.
Lemma D_156b0 : decode_any W_156b0 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156b4 : bv 32 := 0x00050663.
Lemma F_156b4 : fetch_word Plain.M.loaded_segments (0x157b0 : word) = Some W_156b4.
Proof. vm_refl. Qed.
Lemma D_156b4 : decode_any W_156b4 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156c0 : bv 32 := 0x02843503.
Lemma F_156c0 : fetch_word Plain.M.loaded_segments (0x157bc : word) = Some W_156c0.
Proof. vm_refl. Qed.
Lemma D_156c0 : decode_any W_156c0 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156c4 : bv 32 := 0x00050463.
Lemma F_156c4 : fetch_word Plain.M.loaded_segments (0x157c0 : word) = Some W_156c4.
Proof. vm_refl. Qed.
Lemma D_156c4 : decode_any W_156c4 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156cc : bv 32 := 0x03043503.
Lemma F_156cc : fetch_word Plain.M.loaded_segments (0x157c8 : word) = Some W_156cc.
Proof. vm_refl. Qed.
Lemma D_156cc : decode_any W_156cc = Some (Load SZ8 true 10 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156d0 : bv 32 := 0x00a13423.
Lemma F_156d0 : fetch_word Plain.M.loaded_segments (0x157cc : word) = Some W_156d0.
Proof. vm_refl. Qed.
Lemma D_156d0 : decode_any W_156d0 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156d4 : bv 32 := 0x00050863.
Lemma F_156d4 : fetch_word Plain.M.loaded_segments (0x157d0 : word) = Some W_156d4.
Proof. vm_refl. Qed.
Lemma D_156d4 : decode_any W_156d4 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156e4 : bv 32 := 0x00040513.
Lemma F_156e4 : fetch_word Plain.M.loaded_segments (0x157e0 : word) = Some W_156e4.
Proof. vm_refl. Qed.
Lemma D_156e4 : decode_any W_156e4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156e8 : bv 32 := 0x7100c0ef.
Lemma F_156e8 : fetch_word Plain.M.loaded_segments (0x157e4 : word) = Some W_156e8.
Proof. vm_refl. Qed.
Lemma D_156e8 : decode_any W_156e8 = Some (Jal 1 50960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156ec : bv 32 := 0x00015517.
Lemma F_156ec : fetch_word Plain.M.loaded_segments (0x157e8 : word) = Some W_156ec.
Proof. vm_refl. Qed.
Lemma D_156ec : decode_any W_156ec = Some (Auipc 10 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156f0 : bv 32 := 0x25853503.
Lemma F_156f0 : fetch_word Plain.M.loaded_segments (0x157ec : word) = Some W_156f0.
Proof. vm_refl. Qed.
Lemma D_156f0 : decode_any W_156f0 = Some (Load SZ8 true 10 10 600, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156f4 : bv 32 := 0x00052503.
Lemma F_156f4 : fetch_word Plain.M.loaded_segments (0x157f0 : word) = Some W_156f4.
Proof. vm_refl. Qed.
Lemma D_156f4 : decode_any W_156f4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156f8 : bv 32 := 0x00500593.
Lemma F_156f8 : fetch_word Plain.M.loaded_segments (0x157f4 : word) = Some W_156f8.
Proof. vm_refl. Qed.
Lemma D_156f8 : decode_any W_156f8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156fc : bv 32 := 0x02a5c263.
Lemma F_156fc : fetch_word Plain.M.loaded_segments (0x157f8 : word) = Some W_156fc.
Proof. vm_refl. Qed.
Lemma D_156fc : decode_any W_156fc = Some (Branch BC_LT 11 10 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15700 : bv 32 := 0xffffc517.
Lemma F_15700 : fetch_word Plain.M.loaded_segments (0x157fc : word) = Some W_15700.
Proof. vm_refl. Qed.
Lemma D_15700 : decode_any W_15700 = Some (Auipc 10 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15704 : bv 32 := 0xffffb597.
Lemma F_15704 : fetch_word Plain.M.loaded_segments (0x15800 : word) = Some W_15704.
Proof. vm_refl. Qed.
Lemma D_15704 : decode_any W_15704 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15708 : bv 32 := 0x85d50513.
Lemma F_15708 : fetch_word Plain.M.loaded_segments (0x15804 : word) = Some W_15708.
Proof. vm_refl. Qed.
Lemma D_15708 : decode_any W_15708 = Some (OpImm ALU_ADD 10 10 2141, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1570c : bv 32 := 0xe7158593.
Lemma F_1570c : fetch_word Plain.M.loaded_segments (0x15808 : word) = Some W_1570c.
Proof. vm_refl. Qed.
Lemma D_1570c : decode_any W_1570c = Some (OpImm ALU_ADD 11 11 3697, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15710 : bv 32 := 0x00000613.
Lemma F_15710 : fetch_word Plain.M.loaded_segments (0x1580c : word) = Some W_15710.
Proof. vm_refl. Qed.
Lemma D_15710 : decode_any W_15710 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15714 : bv 32 := 0xc2dff0ef.
Lemma F_15714 : fetch_word Plain.M.loaded_segments (0x15810 : word) = Some W_15714.
Proof. vm_refl. Qed.
Lemma D_15714 : decode_any W_15714 = Some (Jal 1 2096172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15718 : bv 32 := 0x00050413.
Lemma F_15718 : fetch_word Plain.M.loaded_segments (0x15814 : word) = Some W_15718.
Proof. vm_refl. Qed.
Lemma D_15718 : decode_any W_15718 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1571c : bv 32 := 0x0080006f.
Lemma F_1571c : fetch_word Plain.M.loaded_segments (0x15818 : word) = Some W_1571c.
Proof. vm_refl. Qed.
Lemma D_1571c : decode_any W_1571c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15724 : bv 32 := 0x00040513.
Lemma F_15724 : fetch_word Plain.M.loaded_segments (0x15820 : word) = Some W_15724.
Proof. vm_refl. Qed.
Lemma D_15724 : decode_any W_15724 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15728 : bv 32 := 0x02813083.
Lemma F_15728 : fetch_word Plain.M.loaded_segments (0x15824 : word) = Some W_15728.
Proof. vm_refl. Qed.
Lemma D_15728 : decode_any W_15728 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1572c : bv 32 := 0x02013403.
Lemma F_1572c : fetch_word Plain.M.loaded_segments (0x15828 : word) = Some W_1572c.
Proof. vm_refl. Qed.
Lemma D_1572c : decode_any W_1572c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15730 : bv 32 := 0x01813483.
Lemma F_15730 : fetch_word Plain.M.loaded_segments (0x1582c : word) = Some W_15730.
Proof. vm_refl. Qed.
Lemma D_15730 : decode_any W_15730 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15734 : bv 32 := 0x01013903.
Lemma F_15734 : fetch_word Plain.M.loaded_segments (0x15830 : word) = Some W_15734.
Proof. vm_refl. Qed.
Lemma D_15734 : decode_any W_15734 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15738 : bv 32 := 0x03010113.
Lemma F_15738 : fetch_word Plain.M.loaded_segments (0x15834 : word) = Some W_15738.
Proof. vm_refl. Qed.
Lemma D_15738 : decode_any W_15738 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1573c : bv 32 := 0x00008067.
Lemma F_1573c : fetch_word Plain.M.loaded_segments (0x15838 : word) = Some W_1573c.
Proof. vm_refl. Qed.
Lemma D_1573c : decode_any W_1573c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15740 : bv 32 := 0xfd010113.
Lemma F_15740 : fetch_word Plain.M.loaded_segments (0x1583c : word) = Some W_15740.
Proof. vm_refl. Qed.
Lemma D_15740 : decode_any W_15740 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15744 : bv 32 := 0x02113423.
Lemma F_15744 : fetch_word Plain.M.loaded_segments (0x15840 : word) = Some W_15744.
Proof. vm_refl. Qed.
Lemma D_15744 : decode_any W_15744 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15748 : bv 32 := 0x02813023.
Lemma F_15748 : fetch_word Plain.M.loaded_segments (0x15844 : word) = Some W_15748.
Proof. vm_refl. Qed.
Lemma D_15748 : decode_any W_15748 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1574c : bv 32 := 0x00913c23.
Lemma F_1574c : fetch_word Plain.M.loaded_segments (0x15848 : word) = Some W_1574c.
Proof. vm_refl. Qed.
Lemma D_1574c : decode_any W_1574c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15750 : bv 32 := 0x01213823.
Lemma F_15750 : fetch_word Plain.M.loaded_segments (0x1584c : word) = Some W_15750.
Proof. vm_refl. Qed.
Lemma D_15750 : decode_any W_15750 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15754 : bv 32 := 0x01313423.
Lemma F_15754 : fetch_word Plain.M.loaded_segments (0x15850 : word) = Some W_15754.
Proof. vm_refl. Qed.
Lemma D_15754 : decode_any W_15754 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15758 : bv 32 := 0x01413023.
Lemma F_15758 : fetch_word Plain.M.loaded_segments (0x15854 : word) = Some W_15758.
Proof. vm_refl. Qed.
Lemma D_15758 : decode_any W_15758 = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1575c : bv 32 := 0x02000693.
Lemma F_1575c : fetch_word Plain.M.loaded_segments (0x15858 : word) = Some W_1575c.
Proof. vm_refl. Qed.
Lemma D_1575c : decode_any W_1575c = Some (OpImm ALU_ADD 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15760 : bv 32 := 0x14c6ea63.
Lemma F_15760 : fetch_word Plain.M.loaded_segments (0x1585c : word) = Some W_15760.
Proof. vm_refl. Qed.
Lemma D_15760 : decode_any W_15760 = Some (Branch BC_LTU 13 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15764 : bv 32 := 0x101016b7.
Lemma F_15764 : fetch_word Plain.M.loaded_segments (0x15860 : word) = Some W_15764.
Proof. vm_refl. Qed.
Lemma D_15764 : decode_any W_15764 = Some (Lui 13 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15768 : bv 32 := 0x00469693.
Lemma F_15768 : fetch_word Plain.M.loaded_segments (0x15864 : word) = Some W_15768.
Proof. vm_refl. Qed.
Lemma D_15768 : decode_any W_15768 = Some (ShiftImm ALU_SLL 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1576c : bv 32 := 0x11668693.
Lemma F_1576c : fetch_word Plain.M.loaded_segments (0x15868 : word) = Some W_1576c.
Proof. vm_refl. Qed.
Lemma D_1576c : decode_any W_1576c = Some (OpImm ALU_ADD 13 13 278, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15770 : bv 32 := 0x00c6d6b3.
Lemma F_15770 : fetch_word Plain.M.loaded_segments (0x1586c : word) = Some W_15770.
Proof. vm_refl. Qed.
Lemma D_15770 : decode_any W_15770 = Some (Op ALU_SRL 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15774 : bv 32 := 0x0016f693.
Lemma F_15774 : fetch_word Plain.M.loaded_segments (0x15870 : word) = Some W_15774.
Proof. vm_refl. Qed.
Lemma D_15774 : decode_any W_15774 = Some (OpImm ALU_AND 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15778 : bv 32 := 0x12068e63.
Lemma F_15778 : fetch_word Plain.M.loaded_segments (0x15874 : word) = Some W_15778.
Proof. vm_refl. Qed.
Lemma D_15778 : decode_any W_15778 = Some (Branch BC_EQ 13 0 316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1577c : bv 32 := 0x06a05a63.
Lemma F_1577c : fetch_word Plain.M.loaded_segments (0x15878 : word) = Some W_1577c.
Proof. vm_refl. Qed.
Lemma D_1577c : decode_any W_1577c = Some (Branch BC_GE 0 10 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15780 : bv 32 := 0x08b05c63.
Lemma F_15780 : fetch_word Plain.M.loaded_segments (0x1587c : word) = Some W_15780.
Proof. vm_refl. Qed.
Lemma D_15780 : decode_any W_15780 = Some (Branch BC_GE 0 11 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15784 : bv 32 := 0x02a606b3.
Lemma F_15784 : fetch_word Plain.M.loaded_segments (0x15880 : word) = Some W_15784.
Proof. vm_refl. Qed.
Lemma D_15784 : decode_any W_15784 = Some (Mul M_MUL 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15788 : bv 32 := 0x20000737.
Lemma F_15788 : fetch_word Plain.M.loaded_segments (0x15884 : word) = Some W_15788.
Proof. vm_refl. Qed.
Lemma D_15788 : decode_any W_15788 = Some (Lui 14 131072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1578c : bv 32 := 0xfe17071b.
Lemma F_1578c : fetch_word Plain.M.loaded_segments (0x15888 : word) = Some W_1578c.
Proof. vm_refl. Qed.
Lemma D_1578c : decode_any W_1578c = Some (OpImm32 14 14 4065, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15790 : bv 32 := 0x0ae6e863.
Lemma F_15790 : fetch_word Plain.M.loaded_segments (0x1588c : word) = Some W_15790.
Proof. vm_refl. Qed.
Lemma D_15790 : decode_any W_15790 = Some (Branch BC_LTU 13 14 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15840 : bv 32 := 0x01f68693.
Lemma F_15840 : fetch_word Plain.M.loaded_segments (0x1593c : word) = Some W_15840.
Proof. vm_refl. Qed.
Lemma D_15840 : decode_any W_15840 = Some (OpImm ALU_ADD 13 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15844 : bv 32 := 0x0056d413.
Lemma F_15844 : fetch_word Plain.M.loaded_segments (0x15940 : word) = Some W_15844.
Proof. vm_refl. Qed.
Lemma D_15844 : decode_any W_15844 = Some (ShiftImm ALU_SRL 8 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15848 : bv 32 := 0x02b406b3.
Lemma F_15848 : fetch_word Plain.M.loaded_segments (0x15944 : word) = Some W_15848.
Proof. vm_refl. Qed.
Lemma D_15848 : decode_any W_15848 = Some (Mul M_MUL 13 8 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1584c : bv 32 := 0x00269693.
Lemma F_1584c : fetch_word Plain.M.loaded_segments (0x15948 : word) = Some W_1584c.
Proof. vm_refl. Qed.
Lemma D_1584c : decode_any W_1584c = Some (ShiftImm ALU_SLL 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15850 : bv 32 := 0x01f6d713.
Lemma F_15850 : fetch_word Plain.M.loaded_segments (0x1594c : word) = Some W_15850.
Proof. vm_refl. Qed.
Lemma D_15850 : decode_any W_15850 = Some (ShiftImm ALU_SRL 14 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15854 : bv 32 := 0x0a070463.
Lemma F_15854 : fetch_word Plain.M.loaded_segments (0x15950 : word) = Some W_15854.
Proof. vm_refl. Qed.
Lemma D_15854 : decode_any W_15854 = Some (Branch BC_EQ 14 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158b4 : bv 32 := 0x00015517.
Lemma F_158b4 : fetch_word Plain.M.loaded_segments (0x159b0 : word) = Some W_158b4.
Proof. vm_refl. Qed.
Lemma D_158b4 : decode_any W_158b4 = Some (Auipc 10 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158b8 : bv 32 := 0x09053503.
Lemma F_158b8 : fetch_word Plain.M.loaded_segments (0x159b4 : word) = Some W_158b8.
Proof. vm_refl. Qed.
Lemma D_158b8 : decode_any W_158b8 = Some (Load SZ8 true 10 10 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158bc : bv 32 := 0x00052503.
Lemma F_158bc : fetch_word Plain.M.loaded_segments (0x159b8 : word) = Some W_158bc.
Proof. vm_refl. Qed.
Lemma D_158bc : decode_any W_158bc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158c0 : bv 32 := 0x00500593.
Lemma F_158c0 : fetch_word Plain.M.loaded_segments (0x159bc : word) = Some W_158c0.
Proof. vm_refl. Qed.
Lemma D_158c0 : decode_any W_158c0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158c4 : bv 32 := 0x0ca5c663.
Lemma F_158c4 : fetch_word Plain.M.loaded_segments (0x159c0 : word) = Some W_158c4.
Proof. vm_refl. Qed.
Lemma D_158c4 : decode_any W_158c4 = Some (Branch BC_LT 11 10 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158c8 : bv 32 := 0xffffb517.
Lemma F_158c8 : fetch_word Plain.M.loaded_segments (0x159c4 : word) = Some W_158c8.
Proof. vm_refl. Qed.
Lemma D_158c8 : decode_any W_158c8 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158cc : bv 32 := 0xffffb597.
Lemma F_158cc : fetch_word Plain.M.loaded_segments (0x159c8 : word) = Some W_158cc.
Proof. vm_refl. Qed.
Lemma D_158cc : decode_any W_158cc = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158d0 : bv 32 := 0xba250513.
Lemma F_158d0 : fetch_word Plain.M.loaded_segments (0x159cc : word) = Some W_158d0.
Proof. vm_refl. Qed.
Lemma D_158d0 : decode_any W_158d0 = Some (OpImm ALU_ADD 10 10 2978, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158d4 : bv 32 := 0xfa258593.
Lemma F_158d4 : fetch_word Plain.M.loaded_segments (0x159d0 : word) = Some W_158d4.
Proof. vm_refl. Qed.
Lemma D_158d4 : decode_any W_158d4 = Some (OpImm ALU_ADD 11 11 4002, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158d8 : bv 32 := 0x00000613.
Lemma F_158d8 : fetch_word Plain.M.loaded_segments (0x159d4 : word) = Some W_158d8.
Proof. vm_refl. Qed.
Lemma D_158d8 : decode_any W_158d8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158dc : bv 32 := 0x02813083.
Lemma F_158dc : fetch_word Plain.M.loaded_segments (0x159d8 : word) = Some W_158dc.
Proof. vm_refl. Qed.
Lemma D_158dc : decode_any W_158dc = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158e0 : bv 32 := 0x02013403.
Lemma F_158e0 : fetch_word Plain.M.loaded_segments (0x159dc : word) = Some W_158e0.
Proof. vm_refl. Qed.
Lemma D_158e0 : decode_any W_158e0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158e4 : bv 32 := 0x01813483.
Lemma F_158e4 : fetch_word Plain.M.loaded_segments (0x159e0 : word) = Some W_158e4.
Proof. vm_refl. Qed.
Lemma D_158e4 : decode_any W_158e4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158e8 : bv 32 := 0x01013903.
Lemma F_158e8 : fetch_word Plain.M.loaded_segments (0x159e4 : word) = Some W_158e8.
Proof. vm_refl. Qed.
Lemma D_158e8 : decode_any W_158e8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158ec : bv 32 := 0x00813983.
Lemma F_158ec : fetch_word Plain.M.loaded_segments (0x159e8 : word) = Some W_158ec.
Proof. vm_refl. Qed.
Lemma D_158ec : decode_any W_158ec = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158f0 : bv 32 := 0x00013a03.
Lemma F_158f0 : fetch_word Plain.M.loaded_segments (0x159ec : word) = Some W_158f0.
Proof. vm_refl. Qed.
Lemma D_158f0 : decode_any W_158f0 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158f4 : bv 32 := 0x03010113.
Lemma F_158f4 : fetch_word Plain.M.loaded_segments (0x159f0 : word) = Some W_158f4.
Proof. vm_refl. Qed.
Lemma D_158f4 : decode_any W_158f4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158f8 : bv 32 := 0xa49ff06f.
Lemma F_158f8 : fetch_word Plain.M.loaded_segments (0x159f4 : word) = Some W_158f8.
Proof. vm_refl. Qed.
Lemma D_158f8 : decode_any W_158f8 = Some (Jal 0 2095688, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158fc : bv 32 := 0x04000737.
Lemma F_158fc : fetch_word Plain.M.loaded_segments (0x159f8 : word) = Some W_158fc.
Proof. vm_refl. Qed.
Lemma D_158fc : decode_any W_158fc = Some (Lui 14 16384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15900 : bv 32 := 0x0017071b.
Lemma F_15900 : fetch_word Plain.M.loaded_segments (0x159fc : word) = Some W_15900.
Proof. vm_refl. Qed.
Lemma D_15900 : decode_any W_15900 = Some (OpImm32 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15904 : bv 32 := 0x02e6e663.
Lemma F_15904 : fetch_word Plain.M.loaded_segments (0x15a00 : word) = Some W_15904.
Proof. vm_refl. Qed.
Lemma D_15904 : decode_any W_15904 = Some (Branch BC_LTU 13 14 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15908 : bv 32 := 0x00015517.
Lemma F_15908 : fetch_word Plain.M.loaded_segments (0x15a04 : word) = Some W_15908.
Proof. vm_refl. Qed.
Lemma D_15908 : decode_any W_15908 = Some (Auipc 10 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1590c : bv 32 := 0x03c53503.
Lemma F_1590c : fetch_word Plain.M.loaded_segments (0x15a08 : word) = Some W_1590c.
Proof. vm_refl. Qed.
Lemma D_1590c : decode_any W_1590c = Some (Load SZ8 true 10 10 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15910 : bv 32 := 0x00052503.
Lemma F_15910 : fetch_word Plain.M.loaded_segments (0x15a0c : word) = Some W_15910.
Proof. vm_refl. Qed.
Lemma D_15910 : decode_any W_15910 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15914 : bv 32 := 0x00500593.
Lemma F_15914 : fetch_word Plain.M.loaded_segments (0x15a10 : word) = Some W_15914.
Proof. vm_refl. Qed.
Lemma D_15914 : decode_any W_15914 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15918 : bv 32 := 0x06a5cc63.
Lemma F_15918 : fetch_word Plain.M.loaded_segments (0x15a14 : word) = Some W_15918.
Proof. vm_refl. Qed.
Lemma D_15918 : decode_any W_15918 = Some (Branch BC_LT 11 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1591c : bv 32 := 0xffffb517.
Lemma F_1591c : fetch_word Plain.M.loaded_segments (0x15a18 : word) = Some W_1591c.
Proof. vm_refl. Qed.
Lemma D_1591c : decode_any W_1591c = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15920 : bv 32 := 0xffffb597.
Lemma F_15920 : fetch_word Plain.M.loaded_segments (0x15a1c : word) = Some W_15920.
Proof. vm_refl. Qed.
Lemma D_15920 : decode_any W_15920 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15924 : bv 32 := 0xa0650513.
Lemma F_15924 : fetch_word Plain.M.loaded_segments (0x15a20 : word) = Some W_15924.
Proof. vm_refl. Qed.
Lemma D_15924 : decode_any W_15924 = Some (OpImm ALU_ADD 10 10 2566, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15928 : bv 32 := 0xf4e58593.
Lemma F_15928 : fetch_word Plain.M.loaded_segments (0x15a24 : word) = Some W_15928.
Proof. vm_refl. Qed.
Lemma D_15928 : decode_any W_15928 = Some (OpImm ALU_ADD 11 11 3918, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1592c : bv 32 := 0x0600006f.
Lemma F_1592c : fetch_word Plain.M.loaded_segments (0x15a28 : word) = Some W_1592c.
Proof. vm_refl. Qed.
Lemma D_1592c : decode_any W_1592c = Some (Jal 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15930 : bv 32 := 0x000056b7.
Lemma F_15930 : fetch_word Plain.M.loaded_segments (0x15a2c : word) = Some W_15930.
Proof. vm_refl. Qed.
Lemma D_15930 : decode_any W_15930 = Some (Lui 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15934 : bv 32 := 0xe216869b.
Lemma F_15934 : fetch_word Plain.M.loaded_segments (0x15a30 : word) = Some W_15934.
Proof. vm_refl. Qed.
Lemma D_15934 : decode_any W_15934 = Some (OpImm32 13 13 3617, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15938 : bv 32 := 0x02d56663.
Lemma F_15938 : fetch_word Plain.M.loaded_segments (0x15a34 : word) = Some W_15938.
Proof. vm_refl. Qed.
Lemma D_15938 : decode_any W_15938 = Some (Branch BC_LTU 10 13 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1593c : bv 32 := 0x00015517.
Lemma F_1593c : fetch_word Plain.M.loaded_segments (0x15a38 : word) = Some W_1593c.
Proof. vm_refl. Qed.
Lemma D_1593c : decode_any W_1593c = Some (Auipc 10 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15940 : bv 32 := 0x00853503.
Lemma F_15940 : fetch_word Plain.M.loaded_segments (0x15a3c : word) = Some W_15940.
Proof. vm_refl. Qed.
Lemma D_15940 : decode_any W_15940 = Some (Load SZ8 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15944 : bv 32 := 0x00052503.
Lemma F_15944 : fetch_word Plain.M.loaded_segments (0x15a40 : word) = Some W_15944.
Proof. vm_refl. Qed.
Lemma D_15944 : decode_any W_15944 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15948 : bv 32 := 0x00500593.
Lemma F_15948 : fetch_word Plain.M.loaded_segments (0x15a44 : word) = Some W_15948.
Proof. vm_refl. Qed.
Lemma D_15948 : decode_any W_15948 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1594c : bv 32 := 0x04a5c263.
Lemma F_1594c : fetch_word Plain.M.loaded_segments (0x15a48 : word) = Some W_1594c.
Proof. vm_refl. Qed.
Lemma D_1594c : decode_any W_1594c = Some (Branch BC_LT 11 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15950 : bv 32 := 0xffffb517.
Lemma F_15950 : fetch_word Plain.M.loaded_segments (0x15a4c : word) = Some W_15950.
Proof. vm_refl. Qed.
Lemma D_15950 : decode_any W_15950 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15954 : bv 32 := 0xffffb597.
Lemma F_15954 : fetch_word Plain.M.loaded_segments (0x15a50 : word) = Some W_15954.
Proof. vm_refl. Qed.
Lemma D_15954 : decode_any W_15954 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15958 : bv 32 := 0x75f50513.
Lemma F_15958 : fetch_word Plain.M.loaded_segments (0x15a54 : word) = Some W_15958.
Proof. vm_refl. Qed.
Lemma D_15958 : decode_any W_15958 = Some (OpImm ALU_ADD 10 10 1887, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1595c : bv 32 := 0xf1a58593.
Lemma F_1595c : fetch_word Plain.M.loaded_segments (0x15a58 : word) = Some W_1595c.
Proof. vm_refl. Qed.
Lemma D_1595c : decode_any W_1595c = Some (OpImm ALU_ADD 11 11 3866, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15960 : bv 32 := 0x02c0006f.
Lemma F_15960 : fetch_word Plain.M.loaded_segments (0x15a5c : word) = Some W_15960.
Proof. vm_refl. Qed.
Lemma D_15960 : decode_any W_15960 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15964 : bv 32 := 0x04d5e863.
Lemma F_15964 : fetch_word Plain.M.loaded_segments (0x15a60 : word) = Some W_15964.
Proof. vm_refl. Qed.
Lemma D_15964 : decode_any W_15964 = Some (Branch BC_LTU 11 13 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15968 : bv 32 := 0x00015517.
Lemma F_15968 : fetch_word Plain.M.loaded_segments (0x15a64 : word) = Some W_15968.
Proof. vm_refl. Qed.
Lemma D_15968 : decode_any W_15968 = Some (Auipc 10 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1596c : bv 32 := 0xfdc53503.
Lemma F_1596c : fetch_word Plain.M.loaded_segments (0x15a68 : word) = Some W_1596c.
Proof. vm_refl. Qed.
Lemma D_1596c : decode_any W_1596c = Some (Load SZ8 true 10 10 4060, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15970 : bv 32 := 0x00052503.
Lemma F_15970 : fetch_word Plain.M.loaded_segments (0x15a6c : word) = Some W_15970.
Proof. vm_refl. Qed.
Lemma D_15970 : decode_any W_15970 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15974 : bv 32 := 0x00500593.
Lemma F_15974 : fetch_word Plain.M.loaded_segments (0x15a70 : word) = Some W_15974.
Proof. vm_refl. Qed.
Lemma D_15974 : decode_any W_15974 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15978 : bv 32 := 0x00a5cc63.
Lemma F_15978 : fetch_word Plain.M.loaded_segments (0x15a74 : word) = Some W_15978.
Proof. vm_refl. Qed.
Lemma D_15978 : decode_any W_15978 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1597c : bv 32 := 0xffffb517.
Lemma F_1597c : fetch_word Plain.M.loaded_segments (0x15a78 : word) = Some W_1597c.
Proof. vm_refl. Qed.
Lemma D_1597c : decode_any W_1597c = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15980 : bv 32 := 0xffffb597.
Lemma F_15980 : fetch_word Plain.M.loaded_segments (0x15a7c : word) = Some W_15980.
Proof. vm_refl. Qed.
Lemma D_15980 : decode_any W_15980 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15984 : bv 32 := 0x2b450513.
Lemma F_15984 : fetch_word Plain.M.loaded_segments (0x15a80 : word) = Some W_15984.
Proof. vm_refl. Qed.
Lemma D_15984 : decode_any W_15984 = Some (OpImm ALU_ADD 10 10 692, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15988 : bv 32 := 0xeee58593.
Lemma F_15988 : fetch_word Plain.M.loaded_segments (0x15a84 : word) = Some W_15988.
Proof. vm_refl. Qed.
Lemma D_15988 : decode_any W_15988 = Some (OpImm ALU_ADD 11 11 3822, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1598c : bv 32 := 0x919ff0ef.
Lemma F_1598c : fetch_word Plain.M.loaded_segments (0x15a88 : word) = Some W_1598c.
Proof. vm_refl. Qed.
Lemma D_1598c : decode_any W_1598c = Some (Jal 1 2095384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15990 : bv 32 := 0x00000513.
Lemma F_15990 : fetch_word Plain.M.loaded_segments (0x15a8c : word) = Some W_15990.
Proof. vm_refl. Qed.
Lemma D_15990 : decode_any W_15990 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15994 : bv 32 := 0x02813083.
Lemma F_15994 : fetch_word Plain.M.loaded_segments (0x15a90 : word) = Some W_15994.
Proof. vm_refl. Qed.
Lemma D_15994 : decode_any W_15994 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15998 : bv 32 := 0x02013403.
Lemma F_15998 : fetch_word Plain.M.loaded_segments (0x15a94 : word) = Some W_15998.
Proof. vm_refl. Qed.
Lemma D_15998 : decode_any W_15998 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1599c : bv 32 := 0x01813483.
Lemma F_1599c : fetch_word Plain.M.loaded_segments (0x15a98 : word) = Some W_1599c.
Proof. vm_refl. Qed.
Lemma D_1599c : decode_any W_1599c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159a0 : bv 32 := 0x01013903.
Lemma F_159a0 : fetch_word Plain.M.loaded_segments (0x15a9c : word) = Some W_159a0.
Proof. vm_refl. Qed.
Lemma D_159a0 : decode_any W_159a0 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159a4 : bv 32 := 0x00813983.
Lemma F_159a4 : fetch_word Plain.M.loaded_segments (0x15aa0 : word) = Some W_159a4.
Proof. vm_refl. Qed.
Lemma D_159a4 : decode_any W_159a4 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159a8 : bv 32 := 0x00013a03.
Lemma F_159a8 : fetch_word Plain.M.loaded_segments (0x15aa4 : word) = Some W_159a8.
Proof. vm_refl. Qed.
Lemma D_159a8 : decode_any W_159a8 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159ac : bv 32 := 0x03010113.
Lemma F_159ac : fetch_word Plain.M.loaded_segments (0x15aa8 : word) = Some W_159ac.
Proof. vm_refl. Qed.
Lemma D_159ac : decode_any W_159ac = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159b0 : bv 32 := 0x00008067.
Lemma F_159b0 : fetch_word Plain.M.loaded_segments (0x15aac : word) = Some W_159b0.
Proof. vm_refl. Qed.
Lemma D_159b0 : decode_any W_159b0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159b4 : bv 32 := 0x00050993.
Lemma F_159b4 : fetch_word Plain.M.loaded_segments (0x15ab0 : word) = Some W_159b4.
Proof. vm_refl. Qed.
Lemma D_159b4 : decode_any W_159b4 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159b8 : bv 32 := 0x00058913.
Lemma F_159b8 : fetch_word Plain.M.loaded_segments (0x15ab4 : word) = Some W_159b8.
Proof. vm_refl. Qed.
Lemma D_159b8 : decode_any W_159b8 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159bc : bv 32 := 0x00060a13.
Lemma F_159bc : fetch_word Plain.M.loaded_segments (0x15ab8 : word) = Some W_159bc.
Proof. vm_refl. Qed.
Lemma D_159bc : decode_any W_159bc = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159c0 : bv 32 := 0x00100513.
Lemma F_159c0 : fetch_word Plain.M.loaded_segments (0x15abc : word) = Some W_159c0.
Proof. vm_refl. Qed.
Lemma D_159c0 : decode_any W_159c0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159c4 : bv 32 := 0x04000593.
Lemma F_159c4 : fetch_word Plain.M.loaded_segments (0x15ac0 : word) = Some W_159c4.
Proof. vm_refl. Qed.
Lemma D_159c4 : decode_any W_159c4 = Some (OpImm ALU_ADD 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159c8 : bv 32 := 0x00100493.
Lemma F_159c8 : fetch_word Plain.M.loaded_segments (0x15ac4 : word) = Some W_159c8.
Proof. vm_refl. Qed.
Lemma D_159c8 : decode_any W_159c8 = Some (OpImm ALU_ADD 9 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159cc : bv 32 := 0x2f40c0ef.
Lemma F_159cc : fetch_word Plain.M.loaded_segments (0x15ac8 : word) = Some W_159cc.
Proof. vm_refl. Qed.
Lemma D_159cc : decode_any W_159cc = Some (Jal 1 49908, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159d0 : bv 32 := 0x02050463.
Lemma F_159d0 : fetch_word Plain.M.loaded_segments (0x15acc : word) = Some W_159d0.
Proof. vm_refl. Qed.
Lemma D_159d0 : decode_any W_159d0 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159d4 : bv 32 := 0xfe8a059b.
Lemma F_159d4 : fetch_word Plain.M.loaded_segments (0x15ad0 : word) = Some W_159d4.
Proof. vm_refl. Qed.
Lemma D_159d4 : decode_any W_159d4 = Some (OpImm32 11 20 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159d8 : bv 32 := 0xff75f593.
Lemma F_159d8 : fetch_word Plain.M.loaded_segments (0x15ad4 : word) = Some W_159d8.
Proof. vm_refl. Qed.
Lemma D_159d8 : decode_any W_159d8 = Some (OpImm ALU_AND 11 11 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159dc : bv 32 := 0x01352023.
Lemma F_159dc : fetch_word Plain.M.loaded_segments (0x15ad8 : word) = Some W_159dc.
Proof. vm_refl. Qed.
Lemma D_159dc : decode_any W_159dc = Some (Store SZ4 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159e0 : bv 32 := 0x01252223.
Lemma F_159e0 : fetch_word Plain.M.loaded_segments (0x15adc : word) = Some W_159e0.
Proof. vm_refl. Qed.
Lemma D_159e0 : decode_any W_159e0 = Some (Store SZ4 10 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159e4 : bv 32 := 0x01452423.
Lemma F_159e4 : fetch_word Plain.M.loaded_segments (0x15ae0 : word) = Some W_159e4.
Proof. vm_refl. Qed.
Lemma D_159e4 : decode_any W_159e4 = Some (Store SZ4 10 20 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159e8 : bv 32 := 0x00852823.
Lemma F_159e8 : fetch_word Plain.M.loaded_segments (0x15ae4 : word) = Some W_159e8.
Proof. vm_refl. Qed.
Lemma D_159e8 : decode_any W_159e8 = Some (Store SZ4 10 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159ec : bv 32 := 0x02058a63.
Lemma F_159ec : fetch_word Plain.M.loaded_segments (0x15ae8 : word) = Some W_159ec.
Proof. vm_refl. Qed.
Lemma D_159ec : decode_any W_159ec = Some (Branch BC_EQ 11 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159f0 : bv 32 := 0x00100593.
Lemma F_159f0 : fetch_word Plain.M.loaded_segments (0x15aec : word) = Some W_159f0.
Proof. vm_refl. Qed.
Lemma D_159f0 : decode_any W_159f0 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159f4 : bv 32 := 0x0300006f.
Lemma F_159f4 : fetch_word Plain.M.loaded_segments (0x15af0 : word) = Some W_159f4.
Proof. vm_refl. Qed.
Lemma D_159f4 : decode_any W_159f4 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159f8 : bv 32 := 0x00015517.
Lemma F_159f8 : fetch_word Plain.M.loaded_segments (0x15af4 : word) = Some W_159f8.
Proof. vm_refl. Qed.
Lemma D_159f8 : decode_any W_159f8 = Some (Auipc 10 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159fc : bv 32 := 0xf4c53503.
Lemma F_159fc : fetch_word Plain.M.loaded_segments (0x15af8 : word) = Some W_159fc.
Proof. vm_refl. Qed.
Lemma D_159fc : decode_any W_159fc = Some (Load SZ8 true 10 10 3916, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a00 : bv 32 := 0x00052503.
Lemma F_15a00 : fetch_word Plain.M.loaded_segments (0x15afc : word) = Some W_15a00.
Proof. vm_refl. Qed.
Lemma D_15a00 : decode_any W_15a00 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a04 : bv 32 := 0x00500593.
Lemma F_15a04 : fetch_word Plain.M.loaded_segments (0x15b00 : word) = Some W_15a04.
Proof. vm_refl. Qed.
Lemma D_15a04 : decode_any W_15a04 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a08 : bv 32 := 0xf8a5c4e3.
Lemma F_15a08 : fetch_word Plain.M.loaded_segments (0x15b04 : word) = Some W_15a08.
Proof. vm_refl. Qed.
Lemma D_15a08 : decode_any W_15a08 = Some (Branch BC_LT 11 10 8072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a0c : bv 32 := 0xffffb517.
Lemma F_15a0c : fetch_word Plain.M.loaded_segments (0x15b08 : word) = Some W_15a0c.
Proof. vm_refl. Qed.
Lemma D_15a0c : decode_any W_15a0c = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a10 : bv 32 := 0xffffb597.
Lemma F_15a10 : fetch_word Plain.M.loaded_segments (0x15b0c : word) = Some W_15a10.
Proof. vm_refl. Qed.
Lemma D_15a10 : decode_any W_15a10 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a14 : bv 32 := 0x9b550513.
Lemma F_15a14 : fetch_word Plain.M.loaded_segments (0x15b10 : word) = Some W_15a14.
Proof. vm_refl. Qed.
Lemma D_15a14 : decode_any W_15a14 = Some (OpImm ALU_ADD 10 10 2485, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a18 : bv 32 := 0xe5e58593.
Lemma F_15a18 : fetch_word Plain.M.loaded_segments (0x15b14 : word) = Some W_15a18.
Proof. vm_refl. Qed.
Lemma D_15a18 : decode_any W_15a18 = Some (OpImm ALU_ADD 11 11 3678, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a1c : bv 32 := 0xebdff06f.
Lemma F_15a1c : fetch_word Plain.M.loaded_segments (0x15b18 : word) = Some W_15a1c.
Proof. vm_refl. Qed.
Lemma D_15a1c : decode_any W_15a1c = Some (Jal 0 2096828, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a20 : bv 32 := 0x00300593.
Lemma F_15a20 : fetch_word Plain.M.loaded_segments (0x15b1c : word) = Some W_15a20.
Proof. vm_refl. Qed.
Lemma D_15a20 : decode_any W_15a20 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a24 : bv 32 := 0x00b52623.
Lemma F_15a24 : fetch_word Plain.M.loaded_segments (0x15b20 : word) = Some W_15a24.
Proof. vm_refl. Qed.
Lemma D_15a24 : decode_any W_15a24 = Some (Store SZ4 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a28 : bv 32 := 0x0310000f.
Lemma F_15a28 : fetch_word Plain.M.loaded_segments (0x15b24 : word) = Some W_15a28.
Proof. vm_refl. Qed.
Lemma D_15a28 : decode_any W_15a28 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a2c : bv 32 := 0x00952a23.
Lemma F_15a2c : fetch_word Plain.M.loaded_segments (0x15b28 : word) = Some W_15a2c.
Proof. vm_refl. Qed.
Lemma D_15a2c : decode_any W_15a2c = Some (Store SZ4 10 9 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a30 : bv 32 := 0x0330000f.
Lemma F_15a30 : fetch_word Plain.M.loaded_segments (0x15b2c : word) = Some W_15a30.
Proof. vm_refl. Qed.
Lemma D_15a30 : decode_any W_15a30 = Some (Fence 0 3 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a34 : bv 32 := 0x02052023.
Lemma F_15a34 : fetch_word Plain.M.loaded_segments (0x15b30 : word) = Some W_15a34.
Proof. vm_refl. Qed.
Lemma D_15a34 : decode_any W_15a34 = Some (Store SZ4 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a38 : bv 32 := 0xf5dff06f.
Lemma F_15a38 : fetch_word Plain.M.loaded_segments (0x15b34 : word) = Some W_15a38.
Proof. vm_refl. Qed.
Lemma D_15a38 : decode_any W_15a38 = Some (Jal 0 2096988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a7c : bv 32 := 0xfe010113.
Lemma F_15a7c : fetch_word Plain.M.loaded_segments (0x15b78 : word) = Some W_15a7c.
Proof. vm_refl. Qed.
Lemma D_15a7c : decode_any W_15a7c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a80 : bv 32 := 0x00113c23.
Lemma F_15a80 : fetch_word Plain.M.loaded_segments (0x15b7c : word) = Some W_15a80.
Proof. vm_refl. Qed.
Lemma D_15a80 : decode_any W_15a80 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a84 : bv 32 := 0x00813823.
Lemma F_15a84 : fetch_word Plain.M.loaded_segments (0x15b80 : word) = Some W_15a84.
Proof. vm_refl. Qed.
Lemma D_15a84 : decode_any W_15a84 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a88 : bv 32 := 0x00913423.
Lemma F_15a88 : fetch_word Plain.M.loaded_segments (0x15b84 : word) = Some W_15a88.
Proof. vm_refl. Qed.
Lemma D_15a88 : decode_any W_15a88 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a8c : bv 32 := 0x06050863.
Lemma F_15a8c : fetch_word Plain.M.loaded_segments (0x15b88 : word) = Some W_15a8c.
Proof. vm_refl. Qed.
Lemma D_15a8c : decode_any W_15a8c = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a90 : bv 32 := 0x00053403.
Lemma F_15a90 : fetch_word Plain.M.loaded_segments (0x15b8c : word) = Some W_15a90.
Proof. vm_refl. Qed.
Lemma D_15a90 : decode_any W_15a90 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a94 : bv 32 := 0x0a040063.
Lemma F_15a94 : fetch_word Plain.M.loaded_segments (0x15b90 : word) = Some W_15a94.
Proof. vm_refl. Qed.
Lemma D_15a94 : decode_any W_15a94 = Some (Branch BC_EQ 8 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a98 : bv 32 := 0x01440593.
Lemma F_15a98 : fetch_word Plain.M.loaded_segments (0x15b94 : word) = Some W_15a98.
Proof. vm_refl. Qed.
Lemma D_15a98 : decode_any W_15a98 = Some (OpImm ALU_ADD 11 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a9c : bv 32 := 0xfff00613.
Lemma F_15a9c : fetch_word Plain.M.loaded_segments (0x15b98 : word) = Some W_15a9c.
Proof. vm_refl. Qed.
Lemma D_15a9c : decode_any W_15a9c = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15aa0 : bv 32 := 0x06c5a5af.
Lemma F_15aa0 : fetch_word Plain.M.loaded_segments (0x15b9c : word) = Some W_15aa0.
Proof. vm_refl. Qed.
Lemma D_15aa0 : decode_any W_15aa0 = Some (Amo AMO_ADD AW true true 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15aa4 : bv 32 := 0x00100613.
Lemma F_15aa4 : fetch_word Plain.M.loaded_segments (0x15ba0 : word) = Some W_15aa4.
Proof. vm_refl. Qed.
Lemma D_15aa4 : decode_any W_15aa4 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15aa8 : bv 32 := 0x04c59663.
Lemma F_15aa8 : fetch_word Plain.M.loaded_segments (0x15ba4 : word) = Some W_15aa8.
Proof. vm_refl. Qed.
Lemma D_15aa8 : decode_any W_15aa8 = Some (Branch BC_NE 11 12 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15aac : bv 32 := 0x00050493.
Lemma F_15aac : fetch_word Plain.M.loaded_segments (0x15ba8 : word) = Some W_15aac.
Proof. vm_refl. Qed.
Lemma D_15aac : decode_any W_15aac = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ab0 : bv 32 := 0x03843503.
Lemma F_15ab0 : fetch_word Plain.M.loaded_segments (0x15bac : word) = Some W_15ab0.
Proof. vm_refl. Qed.
Lemma D_15ab0 : decode_any W_15ab0 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ab4 : bv 32 := 0x00050863.
Lemma F_15ab4 : fetch_word Plain.M.loaded_segments (0x15bb0 : word) = Some W_15ab4.
Proof. vm_refl. Qed.
Lemma D_15ab4 : decode_any W_15ab4 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ab8 : bv 32 := 0x00016597.
Lemma F_15ab8 : fetch_word Plain.M.loaded_segments (0x15bb4 : word) = Some W_15ab8.
Proof. vm_refl. Qed.
Lemma D_15ab8 : decode_any W_15ab8 = Some (Auipc 11 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15abc : bv 32 := 0xf145b583.
Lemma F_15abc : fetch_word Plain.M.loaded_segments (0x15bb8 : word) = Some W_15abc.
Proof. vm_refl. Qed.
Lemma D_15abc : decode_any W_15abc = Some (Load SZ8 true 11 11 3860, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ac0 : bv 32 := 0x000580e7.
Lemma F_15ac0 : fetch_word Plain.M.loaded_segments (0x15bbc : word) = Some W_15ac0.
Proof. vm_refl. Qed.
Lemma D_15ac0 : decode_any W_15ac0 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ac4 : bv 32 := 0x02843503.
Lemma F_15ac4 : fetch_word Plain.M.loaded_segments (0x15bc0 : word) = Some W_15ac4.
Proof. vm_refl. Qed.
Lemma D_15ac4 : decode_any W_15ac4 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ac8 : bv 32 := 0x00050463.
Lemma F_15ac8 : fetch_word Plain.M.loaded_segments (0x15bc4 : word) = Some W_15ac8.
Proof. vm_refl. Qed.
Lemma D_15ac8 : decode_any W_15ac8 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ad0 : bv 32 := 0x03043503.
Lemma F_15ad0 : fetch_word Plain.M.loaded_segments (0x15bcc : word) = Some W_15ad0.
Proof. vm_refl. Qed.
Lemma D_15ad0 : decode_any W_15ad0 = Some (Load SZ8 true 10 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ad4 : bv 32 := 0x00a13023.
Lemma F_15ad4 : fetch_word Plain.M.loaded_segments (0x15bd0 : word) = Some W_15ad4.
Proof. vm_refl. Qed.
Lemma D_15ad4 : decode_any W_15ad4 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ad8 : bv 32 := 0x00050863.
Lemma F_15ad8 : fetch_word Plain.M.loaded_segments (0x15bd4 : word) = Some W_15ad8.
Proof. vm_refl. Qed.
Lemma D_15ad8 : decode_any W_15ad8 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15adc : bv 32 := 0x00010513.
Lemma F_15adc : fetch_word Plain.M.loaded_segments (0x15bd8 : word) = Some W_15adc.
Proof. vm_refl. Qed.
Lemma D_15adc : decode_any W_15adc = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ae0 : bv 32 := 0x1a8030ef.
Lemma F_15ae0 : fetch_word Plain.M.loaded_segments (0x15bdc : word) = Some W_15ae0.
Proof. vm_refl. Qed.
Lemma D_15ae0 : decode_any W_15ae0 = Some (Jal 1 12712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ae4 : bv 32 := 0x02043823.
Lemma F_15ae4 : fetch_word Plain.M.loaded_segments (0x15be0 : word) = Some W_15ae4.
Proof. vm_refl. Qed.
Lemma D_15ae4 : decode_any W_15ae4 = Some (Store SZ8 8 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ae8 : bv 32 := 0x00040513.
Lemma F_15ae8 : fetch_word Plain.M.loaded_segments (0x15be4 : word) = Some W_15ae8.
Proof. vm_refl. Qed.
Lemma D_15ae8 : decode_any W_15ae8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15aec : bv 32 := 0x30c0c0ef.
Lemma F_15aec : fetch_word Plain.M.loaded_segments (0x15be8 : word) = Some W_15aec.
Proof. vm_refl. Qed.
Lemma D_15aec : decode_any W_15aec = Some (Jal 1 49932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15af0 : bv 32 := 0x00048513.
Lemma F_15af0 : fetch_word Plain.M.loaded_segments (0x15bec : word) = Some W_15af0.
Proof. vm_refl. Qed.
Lemma D_15af0 : decode_any W_15af0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15af4 : bv 32 := 0x00053023.
Lemma F_15af4 : fetch_word Plain.M.loaded_segments (0x15bf0 : word) = Some W_15af4.
Proof. vm_refl. Qed.
Lemma D_15af4 : decode_any W_15af4 = Some (Store SZ8 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15af8 : bv 32 := 0x03c0006f.
Lemma F_15af8 : fetch_word Plain.M.loaded_segments (0x15bf4 : word) = Some W_15af8.
Proof. vm_refl. Qed.
Lemma D_15af8 : decode_any W_15af8 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b34 : bv 32 := 0x01813083.
Lemma F_15b34 : fetch_word Plain.M.loaded_segments (0x15c30 : word) = Some W_15b34.
Proof. vm_refl. Qed.
Lemma D_15b34 : decode_any W_15b34 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b38 : bv 32 := 0x01013403.
Lemma F_15b38 : fetch_word Plain.M.loaded_segments (0x15c34 : word) = Some W_15b38.
Proof. vm_refl. Qed.
Lemma D_15b38 : decode_any W_15b38 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b3c : bv 32 := 0x00813483.
Lemma F_15b3c : fetch_word Plain.M.loaded_segments (0x15c38 : word) = Some W_15b3c.
Proof. vm_refl. Qed.
Lemma D_15b3c : decode_any W_15b3c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b40 : bv 32 := 0x02010113.
Lemma F_15b40 : fetch_word Plain.M.loaded_segments (0x15c3c : word) = Some W_15b40.
Proof. vm_refl. Qed.
Lemma D_15b40 : decode_any W_15b40 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b44 : bv 32 := 0x00008067.
Lemma F_15b44 : fetch_word Plain.M.loaded_segments (0x15c40 : word) = Some W_15b44.
Proof. vm_refl. Qed.
Lemma D_15b44 : decode_any W_15b44 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c00 : bv 32 := 0xfe010113.
Lemma F_15c00 : fetch_word Plain.M.loaded_segments (0x15cfc : word) = Some W_15c00.
Proof. vm_refl. Qed.
Lemma D_15c00 : decode_any W_15c00 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c04 : bv 32 := 0x00113c23.
Lemma F_15c04 : fetch_word Plain.M.loaded_segments (0x15d00 : word) = Some W_15c04.
Proof. vm_refl. Qed.
Lemma D_15c04 : decode_any W_15c04 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c08 : bv 32 := 0x00813823.
Lemma F_15c08 : fetch_word Plain.M.loaded_segments (0x15d04 : word) = Some W_15c08.
Proof. vm_refl. Qed.
Lemma D_15c08 : decode_any W_15c08 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c0c : bv 32 := 0x00913423.
Lemma F_15c0c : fetch_word Plain.M.loaded_segments (0x15d08 : word) = Some W_15c0c.
Proof. vm_refl. Qed.
Lemma D_15c0c : decode_any W_15c0c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c10 : bv 32 := 0x02050a63.
Lemma F_15c10 : fetch_word Plain.M.loaded_segments (0x15d0c : word) = Some W_15c10.
Proof. vm_refl. Qed.
Lemma D_15c10 : decode_any W_15c10 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c14 : bv 32 := 0x00050493.
Lemma F_15c14 : fetch_word Plain.M.loaded_segments (0x15d10 : word) = Some W_15c14.
Proof. vm_refl. Qed.
Lemma D_15c14 : decode_any W_15c14 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c18 : bv 32 := 0x00052503.
Lemma F_15c18 : fetch_word Plain.M.loaded_segments (0x15d14 : word) = Some W_15c18.
Proof. vm_refl. Qed.
Lemma D_15c18 : decode_any W_15c18 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c1c : bv 32 := 0x0044a583.
Lemma F_15c1c : fetch_word Plain.M.loaded_segments (0x15d18 : word) = Some W_15c1c.
Proof. vm_refl. Qed.
Lemma D_15c1c : decode_any W_15c1c = Some (Load SZ4 true 11 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c20 : bv 32 := 0x0084a603.
Lemma F_15c20 : fetch_word Plain.M.loaded_segments (0x15d1c : word) = Some W_15c20.
Proof. vm_refl. Qed.
Lemma D_15c20 : decode_any W_15c20 = Some (Load SZ4 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c24 : bv 32 := 0x9e1ff0ef.
Lemma F_15c24 : fetch_word Plain.M.loaded_segments (0x15d20 : word) = Some W_15c24.
Proof. vm_refl. Qed.
Lemma D_15c24 : decode_any W_15c24 = Some (Jal 1 2095584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c28 : bv 32 := 0x04050263.
Lemma F_15c28 : fetch_word Plain.M.loaded_segments (0x15d24 : word) = Some W_15c28.
Proof. vm_refl. Qed.
Lemma D_15c28 : decode_any W_15c28 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c2c : bv 32 := 0x00050413.
Lemma F_15c2c : fetch_word Plain.M.loaded_segments (0x15d28 : word) = Some W_15c2c.
Proof. vm_refl. Qed.
Lemma D_15c2c : decode_any W_15c2c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c30 : bv 32 := 0x08a48063.
Lemma F_15c30 : fetch_word Plain.M.loaded_segments (0x15d2c : word) = Some W_15c30.
Proof. vm_refl. Qed.
Lemma D_15c30 : decode_any W_15c30 = Some (Branch BC_EQ 9 10 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c34 : bv 32 := 0x00c4a503.
Lemma F_15c34 : fetch_word Plain.M.loaded_segments (0x15d30 : word) = Some W_15c34.
Proof. vm_refl. Qed.
Lemma D_15c34 : decode_any W_15c34 = Some (Load SZ4 true 10 9 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c38 : bv 32 := 0x08a05463.
Lemma F_15c38 : fetch_word Plain.M.loaded_segments (0x15d34 : word) = Some W_15c38.
Proof. vm_refl. Qed.
Lemma D_15c38 : decode_any W_15c38 = Some (Branch BC_GE 0 10 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c3c : bv 32 := 0x00a42623.
Lemma F_15c3c : fetch_word Plain.M.loaded_segments (0x15d38 : word) = Some W_15c3c.
Proof. vm_refl. Qed.
Lemma D_15c3c : decode_any W_15c3c = Some (Store SZ4 8 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c40 : bv 32 := 0x0ac0006f.
Lemma F_15c40 : fetch_word Plain.M.loaded_segments (0x15d3c : word) = Some W_15c40.
Proof. vm_refl. Qed.
Lemma D_15c40 : decode_any W_15c40 = Some (Jal 0 172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c6c : bv 32 := 0x00015517.
Lemma F_15c6c : fetch_word Plain.M.loaded_segments (0x15d68 : word) = Some W_15c6c.
Proof. vm_refl. Qed.
Lemma D_15c6c : decode_any W_15c6c = Some (Auipc 10 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c70 : bv 32 := 0xcd853503.
Lemma F_15c70 : fetch_word Plain.M.loaded_segments (0x15d6c : word) = Some W_15c70.
Proof. vm_refl. Qed.
Lemma D_15c70 : decode_any W_15c70 = Some (Load SZ8 true 10 10 3288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c74 : bv 32 := 0x00052503.
Lemma F_15c74 : fetch_word Plain.M.loaded_segments (0x15d70 : word) = Some W_15c74.
Proof. vm_refl. Qed.
Lemma D_15c74 : decode_any W_15c74 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c78 : bv 32 := 0x00500593.
Lemma F_15c78 : fetch_word Plain.M.loaded_segments (0x15d74 : word) = Some W_15c78.
Proof. vm_refl. Qed.
Lemma D_15c78 : decode_any W_15c78 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c7c : bv 32 := 0x02a5c663.
Lemma F_15c7c : fetch_word Plain.M.loaded_segments (0x15d78 : word) = Some W_15c7c.
Proof. vm_refl. Qed.
Lemma D_15c7c : decode_any W_15c7c = Some (Branch BC_LT 11 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c80 : bv 32 := 0xffffa517.
Lemma F_15c80 : fetch_word Plain.M.loaded_segments (0x15d7c : word) = Some W_15c80.
Proof. vm_refl. Qed.
Lemma D_15c80 : decode_any W_15c80 = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c84 : bv 32 := 0xffffb597.
Lemma F_15c84 : fetch_word Plain.M.loaded_segments (0x15d80 : word) = Some W_15c84.
Proof. vm_refl. Qed.
Lemma D_15c84 : decode_any W_15c84 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c88 : bv 32 := 0x74150513.
Lemma F_15c88 : fetch_word Plain.M.loaded_segments (0x15d84 : word) = Some W_15c88.
Proof. vm_refl. Qed.
Lemma D_15c88 : decode_any W_15c88 = Some (OpImm ALU_ADD 10 10 1857, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c8c : bv 32 := 0x2f658593.
Lemma F_15c8c : fetch_word Plain.M.loaded_segments (0x15d88 : word) = Some W_15c8c.
Proof. vm_refl. Qed.
Lemma D_15c8c : decode_any W_15c8c = Some (OpImm ALU_ADD 11 11 758, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c90 : bv 32 := 0x00000613.
Lemma F_15c90 : fetch_word Plain.M.loaded_segments (0x15d8c : word) = Some W_15c90.
Proof. vm_refl. Qed.
Lemma D_15c90 : decode_any W_15c90 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c94 : bv 32 := 0x01813083.
Lemma F_15c94 : fetch_word Plain.M.loaded_segments (0x15d90 : word) = Some W_15c94.
Proof. vm_refl. Qed.
Lemma D_15c94 : decode_any W_15c94 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c98 : bv 32 := 0x01013403.
Lemma F_15c98 : fetch_word Plain.M.loaded_segments (0x15d94 : word) = Some W_15c98.
Proof. vm_refl. Qed.
Lemma D_15c98 : decode_any W_15c98 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c9c : bv 32 := 0x00813483.
Lemma F_15c9c : fetch_word Plain.M.loaded_segments (0x15d98 : word) = Some W_15c9c.
Proof. vm_refl. Qed.
Lemma D_15c9c : decode_any W_15c9c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ca0 : bv 32 := 0x02010113.
Lemma F_15ca0 : fetch_word Plain.M.loaded_segments (0x15d9c : word) = Some W_15ca0.
Proof. vm_refl. Qed.
Lemma D_15ca0 : decode_any W_15ca0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ca4 : bv 32 := 0xe9cff06f.
Lemma F_15ca4 : fetch_word Plain.M.loaded_segments (0x15da0 : word) = Some W_15ca4.
Proof. vm_refl. Qed.
Lemma D_15ca4 : decode_any W_15ca4 = Some (Jal 0 2094748, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15cec : bv 32 := 0x0184b503.
Lemma F_15cec : fetch_word Plain.M.loaded_segments (0x15de8 : word) = Some W_15cec.
Proof. vm_refl. Qed.
Lemma D_15cec : decode_any W_15cec = Some (Load SZ8 true 10 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15cf0 : bv 32 := 0x00a43c23.
Lemma F_15cf0 : fetch_word Plain.M.loaded_segments (0x15dec : word) = Some W_15cf0.
Proof. vm_refl. Qed.
Lemma D_15cf0 : decode_any W_15cf0 = Some (Store SZ8 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15cf4 : bv 32 := 0x00040513.
Lemma F_15cf4 : fetch_word Plain.M.loaded_segments (0x15df0 : word) = Some W_15cf4.
Proof. vm_refl. Qed.
Lemma D_15cf4 : decode_any W_15cf4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15cf8 : bv 32 := 0x00048593.
Lemma F_15cf8 : fetch_word Plain.M.loaded_segments (0x15df4 : word) = Some W_15cf8.
Proof. vm_refl. Qed.
Lemma D_15cf8 : decode_any W_15cf8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15cfc : bv 32 := 0x214000ef.
Lemma F_15cfc : fetch_word Plain.M.loaded_segments (0x15df8 : word) = Some W_15cfc.
Proof. vm_refl. Qed.
Lemma D_15cfc : decode_any W_15cfc = Some (Jal 1 532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d00 : bv 32 := 0x0284b583.
Lemma F_15d00 : fetch_word Plain.M.loaded_segments (0x15dfc : word) = Some W_15d00.
Proof. vm_refl. Qed.
Lemma D_15d00 : decode_any W_15d00 = Some (Load SZ8 true 11 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d04 : bv 32 := 0x02840513.
Lemma F_15d04 : fetch_word Plain.M.loaded_segments (0x15e00 : word) = Some W_15d04.
Proof. vm_refl. Qed.
Lemma D_15d04 : decode_any W_15d04 = Some (OpImm ALU_ADD 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d08 : bv 32 := 0xfe0ff0ef.
Lemma F_15d08 : fetch_word Plain.M.loaded_segments (0x15e04 : word) = Some W_15d08.
Proof. vm_refl. Qed.
Lemma D_15d08 : decode_any W_15d08 = Some (Jal 1 2095072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d0c : bv 32 := 0x0204a503.
Lemma F_15d0c : fetch_word Plain.M.loaded_segments (0x15e08 : word) = Some W_15d0c.
Proof. vm_refl. Qed.
Lemma D_15d0c : decode_any W_15d0c = Some (Load SZ4 true 10 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d10 : bv 32 := 0x02a42023.
Lemma F_15d10 : fetch_word Plain.M.loaded_segments (0x15e0c : word) = Some W_15d10.
Proof. vm_refl. Qed.
Lemma D_15d10 : decode_any W_15d10 = Some (Store SZ4 8 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d14 : bv 32 := 0x00040513.
Lemma F_15d14 : fetch_word Plain.M.loaded_segments (0x15e10 : word) = Some W_15d14.
Proof. vm_refl. Qed.
Lemma D_15d14 : decode_any W_15d14 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d18 : bv 32 := 0x00000593.
Lemma F_15d18 : fetch_word Plain.M.loaded_segments (0x15e14 : word) = Some W_15d18.
Proof. vm_refl. Qed.
Lemma D_15d18 : decode_any W_15d18 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d1c : bv 32 := 0x3b0010ef.
Lemma F_15d1c : fetch_word Plain.M.loaded_segments (0x15e18 : word) = Some W_15d1c.
Proof. vm_refl. Qed.
Lemma D_15d1c : decode_any W_15d1c = Some (Jal 1 5040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d20 : bv 32 := 0x00040513.
Lemma F_15d20 : fetch_word Plain.M.loaded_segments (0x15e1c : word) = Some W_15d20.
Proof. vm_refl. Qed.
Lemma D_15d20 : decode_any W_15d20 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d24 : bv 32 := 0x01813083.
Lemma F_15d24 : fetch_word Plain.M.loaded_segments (0x15e20 : word) = Some W_15d24.
Proof. vm_refl. Qed.
Lemma D_15d24 : decode_any W_15d24 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d28 : bv 32 := 0x01013403.
Lemma F_15d28 : fetch_word Plain.M.loaded_segments (0x15e24 : word) = Some W_15d28.
Proof. vm_refl. Qed.
Lemma D_15d28 : decode_any W_15d28 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d2c : bv 32 := 0x00813483.
Lemma F_15d2c : fetch_word Plain.M.loaded_segments (0x15e28 : word) = Some W_15d2c.
Proof. vm_refl. Qed.
Lemma D_15d2c : decode_any W_15d2c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d30 : bv 32 := 0x02010113.
Lemma F_15d30 : fetch_word Plain.M.loaded_segments (0x15e2c : word) = Some W_15d30.
Proof. vm_refl. Qed.
Lemma D_15d30 : decode_any W_15d30 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d34 : bv 32 := 0x00008067.
Lemma F_15d34 : fetch_word Plain.M.loaded_segments (0x15e30 : word) = Some W_15d34.
Proof. vm_refl. Qed.
Lemma D_15d34 : decode_any W_15d34 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d38 : bv 32 := 0x00058463.
Lemma F_15d38 : fetch_word Plain.M.loaded_segments (0x15e34 : word) = Some W_15d38.
Proof. vm_refl. Qed.
Lemma D_15d38 : decode_any W_15d38 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d3c : bv 32 := 0x0005a023.
Lemma F_15d3c : fetch_word Plain.M.loaded_segments (0x15e38 : word) = Some W_15d3c.
Proof. vm_refl. Qed.
Lemma D_15d3c : decode_any W_15d3c = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d40 : bv 32 := 0x00060463.
Lemma F_15d40 : fetch_word Plain.M.loaded_segments (0x15e3c : word) = Some W_15d40.
Proof. vm_refl. Qed.
Lemma D_15d40 : decode_any W_15d40 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d44 : bv 32 := 0x00062023.
Lemma F_15d44 : fetch_word Plain.M.loaded_segments (0x15e40 : word) = Some W_15d44.
Proof. vm_refl. Qed.
Lemma D_15d44 : decode_any W_15d44 = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d48 : bv 32 := 0x00068463.
Lemma F_15d48 : fetch_word Plain.M.loaded_segments (0x15e44 : word) = Some W_15d48.
Proof. vm_refl. Qed.
Lemma D_15d48 : decode_any W_15d48 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d4c : bv 32 := 0x0006a023.
Lemma F_15d4c : fetch_word Plain.M.loaded_segments (0x15e48 : word) = Some W_15d4c.
Proof. vm_refl. Qed.
Lemma D_15d4c : decode_any W_15d4c = Some (Store SZ4 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d50 : bv 32 := 0x02050a63.
Lemma F_15d50 : fetch_word Plain.M.loaded_segments (0x15e4c : word) = Some W_15d50.
Proof. vm_refl. Qed.
Lemma D_15d50 : decode_any W_15d50 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d54 : bv 32 := 0x00058663.
Lemma F_15d54 : fetch_word Plain.M.loaded_segments (0x15e50 : word) = Some W_15d54.
Proof. vm_refl. Qed.
Lemma D_15d54 : decode_any W_15d54 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d58 : bv 32 := 0x00052703.
Lemma F_15d58 : fetch_word Plain.M.loaded_segments (0x15e54 : word) = Some W_15d58.
Proof. vm_refl. Qed.
Lemma D_15d58 : decode_any W_15d58 = Some (Load SZ4 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d5c : bv 32 := 0x00e5a023.
Lemma F_15d5c : fetch_word Plain.M.loaded_segments (0x15e58 : word) = Some W_15d5c.
Proof. vm_refl. Qed.
Lemma D_15d5c : decode_any W_15d5c = Some (Store SZ4 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d60 : bv 32 := 0x00060663.
Lemma F_15d60 : fetch_word Plain.M.loaded_segments (0x15e5c : word) = Some W_15d60.
Proof. vm_refl. Qed.
Lemma D_15d60 : decode_any W_15d60 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d64 : bv 32 := 0x00452583.
Lemma F_15d64 : fetch_word Plain.M.loaded_segments (0x15e60 : word) = Some W_15d64.
Proof. vm_refl. Qed.
Lemma D_15d64 : decode_any W_15d64 = Some (Load SZ4 true 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d68 : bv 32 := 0x00b62023.
Lemma F_15d68 : fetch_word Plain.M.loaded_segments (0x15e64 : word) = Some W_15d68.
Proof. vm_refl. Qed.
Lemma D_15d68 : decode_any W_15d68 = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d6c : bv 32 := 0x00000593.
Lemma F_15d6c : fetch_word Plain.M.loaded_segments (0x15e68 : word) = Some W_15d6c.
Proof. vm_refl. Qed.
Lemma D_15d6c : decode_any W_15d6c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d70 : bv 32 := 0x00068663.
Lemma F_15d70 : fetch_word Plain.M.loaded_segments (0x15e6c : word) = Some W_15d70.
Proof. vm_refl. Qed.
Lemma D_15d70 : decode_any W_15d70 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d74 : bv 32 := 0x00852503.
Lemma F_15d74 : fetch_word Plain.M.loaded_segments (0x15e70 : word) = Some W_15d74.
Proof. vm_refl. Qed.
Lemma D_15d74 : decode_any W_15d74 = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d78 : bv 32 := 0x00a6a023.
Lemma F_15d78 : fetch_word Plain.M.loaded_segments (0x15e74 : word) = Some W_15d78.
Proof. vm_refl. Qed.
Lemma D_15d78 : decode_any W_15d78 = Some (Store SZ4 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d7c : bv 32 := 0x00058513.
Lemma F_15d7c : fetch_word Plain.M.loaded_segments (0x15e78 : word) = Some W_15d7c.
Proof. vm_refl. Qed.
Lemma D_15d7c : decode_any W_15d7c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d80 : bv 32 := 0x00008067.
Lemma F_15d80 : fetch_word Plain.M.loaded_segments (0x15e7c : word) = Some W_15d80.
Proof. vm_refl. Qed.
Lemma D_15d80 : decode_any W_15d80 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f10 : bv 32 := 0xfd010113.
Lemma F_15f10 : fetch_word Plain.M.loaded_segments (0x1600c : word) = Some W_15f10.
Proof. vm_refl. Qed.
Lemma D_15f10 : decode_any W_15f10 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f14 : bv 32 := 0x02113423.
Lemma F_15f14 : fetch_word Plain.M.loaded_segments (0x16010 : word) = Some W_15f14.
Proof. vm_refl. Qed.
Lemma D_15f14 : decode_any W_15f14 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f18 : bv 32 := 0x02813023.
Lemma F_15f18 : fetch_word Plain.M.loaded_segments (0x16014 : word) = Some W_15f18.
Proof. vm_refl. Qed.
Lemma D_15f18 : decode_any W_15f18 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f1c : bv 32 := 0x00913c23.
Lemma F_15f1c : fetch_word Plain.M.loaded_segments (0x16018 : word) = Some W_15f1c.
Proof. vm_refl. Qed.
Lemma D_15f1c : decode_any W_15f1c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f20 : bv 32 := 0x0e058063.
Lemma F_15f20 : fetch_word Plain.M.loaded_segments (0x1601c : word) = Some W_15f20.
Proof. vm_refl. Qed.
Lemma D_15f20 : decode_any W_15f20 = Some (Branch BC_EQ 11 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f24 : bv 32 := 0x10050263.
Lemma F_15f24 : fetch_word Plain.M.loaded_segments (0x16020 : word) = Some W_15f24.
Proof. vm_refl. Qed.
Lemma D_15f24 : decode_any W_15f24 = Some (Branch BC_EQ 10 0 260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f28 : bv 32 := 0x0ca58863.
Lemma F_15f28 : fetch_word Plain.M.loaded_segments (0x16024 : word) = Some W_15f28.
Proof. vm_refl. Qed.
Lemma D_15f28 : decode_any W_15f28 = Some (Branch BC_EQ 11 10 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f2c : bv 32 := 0x0085a603.
Lemma F_15f2c : fetch_word Plain.M.loaded_segments (0x16028 : word) = Some W_15f2c.
Proof. vm_refl. Qed.
Lemma D_15f2c : decode_any W_15f2c = Some (Load SZ4 true 12 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f30 : bv 32 := 0x00852683.
Lemma F_15f30 : fetch_word Plain.M.loaded_segments (0x1602c : word) = Some W_15f30.
Proof. vm_refl. Qed.
Lemma D_15f30 : decode_any W_15f30 = Some (Load SZ4 true 13 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f34 : bv 32 := 0x10d61e63.
Lemma F_15f34 : fetch_word Plain.M.loaded_segments (0x16030 : word) = Some W_15f34.
Proof. vm_refl. Qed.
Lemma D_15f34 : decode_any W_15f34 = Some (Branch BC_NE 12 13 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f38 : bv 32 := 0x03053603.
Lemma F_15f38 : fetch_word Plain.M.loaded_segments (0x16034 : word) = Some W_15f38.
Proof. vm_refl. Qed.
Lemma D_15f38 : decode_any W_15f38 = Some (Load SZ8 true 12 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f3c : bv 32 := 0x00c13823.
Lemma F_15f3c : fetch_word Plain.M.loaded_segments (0x16038 : word) = Some W_15f3c.
Proof. vm_refl. Qed.
Lemma D_15f3c : decode_any W_15f3c = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f40 : bv 32 := 0x02060063.
Lemma F_15f40 : fetch_word Plain.M.loaded_segments (0x1603c : word) = Some W_15f40.
Proof. vm_refl. Qed.
Lemma D_15f40 : decode_any W_15f40 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f60 : bv 32 := 0x0305b403.
Lemma F_15f60 : fetch_word Plain.M.loaded_segments (0x1605c : word) = Some W_15f60.
Proof. vm_refl. Qed.
Lemma D_15f60 : decode_any W_15f60 = Some (Load SZ8 true 8 11 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f64 : bv 32 := 0x08040a63.
Lemma F_15f64 : fetch_word Plain.M.loaded_segments (0x16060 : word) = Some W_15f64.
Proof. vm_refl. Qed.
Lemma D_15f64 : decode_any W_15f64 = Some (Branch BC_EQ 8 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f68 : bv 32 := 0x00050493.
Lemma F_15f68 : fetch_word Plain.M.loaded_segments (0x16064 : word) = Some W_15f68.
Proof. vm_refl. Qed.
Lemma D_15f68 : decode_any W_15f68 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f6c : bv 32 := 0x00c10613.
Lemma F_15f6c : fetch_word Plain.M.loaded_segments (0x16068 : word) = Some W_15f6c.
Proof. vm_refl. Qed.
Lemma D_15f6c : decode_any W_15f6c = Some (OpImm ALU_ADD 12 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f70 : bv 32 := 0x00040513.
Lemma F_15f70 : fetch_word Plain.M.loaded_segments (0x1606c : word) = Some W_15f70.
Proof. vm_refl. Qed.
Lemma D_15f70 : decode_any W_15f70 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f74 : bv 32 := 0x00000593.
Lemma F_15f74 : fetch_word Plain.M.loaded_segments (0x16070 : word) = Some W_15f74.
Proof. vm_refl. Qed.
Lemma D_15f74 : decode_any W_15f74 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f78 : bv 32 := 0x215020ef.
Lemma F_15f78 : fetch_word Plain.M.loaded_segments (0x16074 : word) = Some W_15f78.
Proof. vm_refl. Qed.
Lemma D_15f78 : decode_any W_15f78 = Some (Jal 1 10772, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f7c : bv 32 := 0x00c12503.
Lemma F_15f7c : fetch_word Plain.M.loaded_segments (0x16078 : word) = Some W_15f7c.
Proof. vm_refl. Qed.
Lemma D_15f7c : decode_any W_15f7c = Some (Load SZ4 true 10 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f80 : bv 32 := 0x10050663.
Lemma F_15f80 : fetch_word Plain.M.loaded_segments (0x1607c : word) = Some W_15f80.
Proof. vm_refl. Qed.
Lemma D_15f80 : decode_any W_15f80 = Some (Branch BC_EQ 10 0 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f84 : bv 32 := 0x00040513.
Lemma F_15f84 : fetch_word Plain.M.loaded_segments (0x16080 : word) = Some W_15f84.
Proof. vm_refl. Qed.
Lemma D_15f84 : decode_any W_15f84 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f88 : bv 32 := 0x109020ef.
Lemma F_15f88 : fetch_word Plain.M.loaded_segments (0x16084 : word) = Some W_15f88.
Proof. vm_refl. Qed.
Lemma D_15f88 : decode_any W_15f88 = Some (Jal 1 10504, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f8c : bv 32 := 0x12050463.
Lemma F_15f8c : fetch_word Plain.M.loaded_segments (0x16088 : word) = Some W_15f8c.
Proof. vm_refl. Qed.
Lemma D_15f8c : decode_any W_15f8c = Some (Branch BC_EQ 10 0 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f90 : bv 32 := 0x00048593.
Lemma F_15f90 : fetch_word Plain.M.loaded_segments (0x1608c : word) = Some W_15f90.
Proof. vm_refl. Qed.
Lemma D_15f90 : decode_any W_15f90 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f94 : bv 32 := 0x0304b603.
Lemma F_15f94 : fetch_word Plain.M.loaded_segments (0x16090 : word) = Some W_15f94.
Proof. vm_refl. Qed.
Lemma D_15f94 : decode_any W_15f94 = Some (Load SZ8 true 12 9 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f98 : bv 32 := 0x00c13823.
Lemma F_15f98 : fetch_word Plain.M.loaded_segments (0x16094 : word) = Some W_15f98.
Proof. vm_refl. Qed.
Lemma D_15f98 : decode_any W_15f98 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f9c : bv 32 := 0x00060c63.
Lemma F_15f9c : fetch_word Plain.M.loaded_segments (0x16098 : word) = Some W_15f9c.
Proof. vm_refl. Qed.
Lemma D_15f9c : decode_any W_15f9c = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15fb4 : bv 32 := 0x02a5b823.
Lemma F_15fb4 : fetch_word Plain.M.loaded_segments (0x160b0 : word) = Some W_15fb4.
Proof. vm_refl. Qed.
Lemma D_15fb4 : decode_any W_15fb4 = Some (Store SZ8 11 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15fb8 : bv 32 := 0x01010613.
Lemma F_15fb8 : fetch_word Plain.M.loaded_segments (0x160b4 : word) = Some W_15fb8.
Proof. vm_refl. Qed.
Lemma D_15fb8 : decode_any W_15fb8 = Some (OpImm ALU_ADD 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15fbc : bv 32 := 0x00000593.
Lemma F_15fbc : fetch_word Plain.M.loaded_segments (0x160b8 : word) = Some W_15fbc.
Proof. vm_refl. Qed.
Lemma D_15fbc : decode_any W_15fbc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15fc0 : bv 32 := 0x1cd020ef.
Lemma F_15fc0 : fetch_word Plain.M.loaded_segments (0x160bc : word) = Some W_15fc0.
Proof. vm_refl. Qed.
Lemma D_15fc0 : decode_any W_15fc0 = Some (Jal 1 10700, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15fc4 : bv 32 := 0x01012503.
Lemma F_15fc4 : fetch_word Plain.M.loaded_segments (0x160c0 : word) = Some W_15fc4.
Proof. vm_refl. Qed.
Lemma D_15fc4 : decode_any W_15fc4 = Some (Load SZ4 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15fc8 : bv 32 := 0x02051863.
Lemma F_15fc8 : fetch_word Plain.M.loaded_segments (0x160c4 : word) = Some W_15fc8.
Proof. vm_refl. Qed.
Lemma D_15fc8 : decode_any W_15fc8 = Some (Branch BC_NE 10 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ff8 : bv 32 := 0x00000513.
Lemma F_15ff8 : fetch_word Plain.M.loaded_segments (0x160f4 : word) = Some W_15ff8.
Proof. vm_refl. Qed.
Lemma D_15ff8 : decode_any W_15ff8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ffc : bv 32 := 0x0ec0006f.
Lemma F_15ffc : fetch_word Plain.M.loaded_segments (0x160f8 : word) = Some W_15ffc.
Proof. vm_refl. Qed.
Lemma D_15ffc : decode_any W_15ffc = Some (Jal 0 236, 4%Z).
Proof. vm_refl. Qed.
