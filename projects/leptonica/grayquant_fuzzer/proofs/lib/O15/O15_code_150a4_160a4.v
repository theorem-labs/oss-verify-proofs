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
Definition W_15350 : bv 32 := 0xff010113.
Lemma F_15350 : fetch_word Plain.M.loaded_segments (0x153a8 : word) = Some W_15350.
Proof. vm_refl. Qed.
Lemma D_15350 : decode_any W_15350 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15354 : bv 32 := 0x00113423.
Lemma F_15354 : fetch_word Plain.M.loaded_segments (0x153ac : word) = Some W_15354.
Proof. vm_refl. Qed.
Lemma D_15354 : decode_any W_15354 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15358 : bv 32 := 0x00813023.
Lemma F_15358 : fetch_word Plain.M.loaded_segments (0x153b0 : word) = Some W_15358.
Proof. vm_refl. Qed.
Lemma D_15358 : decode_any W_15358 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1535c : bv 32 := 0x00060413.
Lemma F_1535c : fetch_word Plain.M.loaded_segments (0x153b4 : word) = Some W_1535c.
Proof. vm_refl. Qed.
Lemma D_1535c : decode_any W_1535c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15360 : bv 32 := 0x00050613.
Lemma F_15360 : fetch_word Plain.M.loaded_segments (0x153b8 : word) = Some W_15360.
Proof. vm_refl. Qed.
Lemma D_15360 : decode_any W_15360 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15364 : bv 32 := 0xffffc517.
Lemma F_15364 : fetch_word Plain.M.loaded_segments (0x153bc : word) = Some W_15364.
Proof. vm_refl. Qed.
Lemma D_15364 : decode_any W_15364 = Some (Auipc 10 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15368 : bv 32 := 0x0c750513.
Lemma F_15368 : fetch_word Plain.M.loaded_segments (0x153c0 : word) = Some W_15368.
Proof. vm_refl. Qed.
Lemma D_15368 : decode_any W_15368 = Some (OpImm ALU_ADD 10 10 199, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1536c : bv 32 := 0x018000ef.
Lemma F_1536c : fetch_word Plain.M.loaded_segments (0x153c4 : word) = Some W_1536c.
Proof. vm_refl. Qed.
Lemma D_1536c : decode_any W_1536c = Some (Jal 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15370 : bv 32 := 0x00040513.
Lemma F_15370 : fetch_word Plain.M.loaded_segments (0x153c8 : word) = Some W_15370.
Proof. vm_refl. Qed.
Lemma D_15370 : decode_any W_15370 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15374 : bv 32 := 0x00813083.
Lemma F_15374 : fetch_word Plain.M.loaded_segments (0x153cc : word) = Some W_15374.
Proof. vm_refl. Qed.
Lemma D_15374 : decode_any W_15374 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15378 : bv 32 := 0x00013403.
Lemma F_15378 : fetch_word Plain.M.loaded_segments (0x153d0 : word) = Some W_15378.
Proof. vm_refl. Qed.
Lemma D_15378 : decode_any W_15378 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1537c : bv 32 := 0x01010113.
Lemma F_1537c : fetch_word Plain.M.loaded_segments (0x153d4 : word) = Some W_1537c.
Proof. vm_refl. Qed.
Lemma D_1537c : decode_any W_1537c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15380 : bv 32 := 0x00008067.
Lemma F_15380 : fetch_word Plain.M.loaded_segments (0x153d8 : word) = Some W_15380.
Proof. vm_refl. Qed.
Lemma D_15380 : decode_any W_15380 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15420 : bv 32 := 0xff010113.
Lemma F_15420 : fetch_word Plain.M.loaded_segments (0x15478 : word) = Some W_15420.
Proof. vm_refl. Qed.
Lemma D_15420 : decode_any W_15420 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15424 : bv 32 := 0x00113423.
Lemma F_15424 : fetch_word Plain.M.loaded_segments (0x1547c : word) = Some W_15424.
Proof. vm_refl. Qed.
Lemma D_15424 : decode_any W_15424 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15428 : bv 32 := 0x00813023.
Lemma F_15428 : fetch_word Plain.M.loaded_segments (0x15480 : word) = Some W_15428.
Proof. vm_refl. Qed.
Lemma D_15428 : decode_any W_15428 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1542c : bv 32 := 0x00060413.
Lemma F_1542c : fetch_word Plain.M.loaded_segments (0x15484 : word) = Some W_1542c.
Proof. vm_refl. Qed.
Lemma D_1542c : decode_any W_1542c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15430 : bv 32 := 0x00050613.
Lemma F_15430 : fetch_word Plain.M.loaded_segments (0x15488 : word) = Some W_15430.
Proof. vm_refl. Qed.
Lemma D_15430 : decode_any W_15430 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15434 : bv 32 := 0xffffc517.
Lemma F_15434 : fetch_word Plain.M.loaded_segments (0x1548c : word) = Some W_15434.
Proof. vm_refl. Qed.
Lemma D_15434 : decode_any W_15434 = Some (Auipc 10 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15438 : bv 32 := 0xff750513.
Lemma F_15438 : fetch_word Plain.M.loaded_segments (0x15490 : word) = Some W_15438.
Proof. vm_refl. Qed.
Lemma D_15438 : decode_any W_15438 = Some (OpImm ALU_ADD 10 10 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1543c : bv 32 := 0xf49ff0ef.
Lemma F_1543c : fetch_word Plain.M.loaded_segments (0x15494 : word) = Some W_1543c.
Proof. vm_refl. Qed.
Lemma D_1543c : decode_any W_1543c = Some (Jal 1 2096968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15440 : bv 32 := 0x00040513.
Lemma F_15440 : fetch_word Plain.M.loaded_segments (0x15498 : word) = Some W_15440.
Proof. vm_refl. Qed.
Lemma D_15440 : decode_any W_15440 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15444 : bv 32 := 0x00813083.
Lemma F_15444 : fetch_word Plain.M.loaded_segments (0x1549c : word) = Some W_15444.
Proof. vm_refl. Qed.
Lemma D_15444 : decode_any W_15444 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15448 : bv 32 := 0x00013403.
Lemma F_15448 : fetch_word Plain.M.loaded_segments (0x154a0 : word) = Some W_15448.
Proof. vm_refl. Qed.
Lemma D_15448 : decode_any W_15448 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1544c : bv 32 := 0x01010113.
Lemma F_1544c : fetch_word Plain.M.loaded_segments (0x154a4 : word) = Some W_1544c.
Proof. vm_refl. Qed.
Lemma D_1544c : decode_any W_1544c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15450 : bv 32 := 0x00008067.
Lemma F_15450 : fetch_word Plain.M.loaded_segments (0x154a8 : word) = Some W_15450.
Proof. vm_refl. Qed.
Lemma D_15450 : decode_any W_15450 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155c8 : bv 32 := 0x02050e63.
Lemma F_155c8 : fetch_word Plain.M.loaded_segments (0x15620 : word) = Some W_155c8.
Proof. vm_refl. Qed.
Lemma D_155c8 : decode_any W_155c8 = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155cc : bv 32 := 0xfe010113.
Lemma F_155cc : fetch_word Plain.M.loaded_segments (0x15624 : word) = Some W_155cc.
Proof. vm_refl. Qed.
Lemma D_155cc : decode_any W_155cc = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155d0 : bv 32 := 0x00113c23.
Lemma F_155d0 : fetch_word Plain.M.loaded_segments (0x15628 : word) = Some W_155d0.
Proof. vm_refl. Qed.
Lemma D_155d0 : decode_any W_155d0 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155d4 : bv 32 := 0x00813823.
Lemma F_155d4 : fetch_word Plain.M.loaded_segments (0x1562c : word) = Some W_155d4.
Proof. vm_refl. Qed.
Lemma D_155d4 : decode_any W_155d4 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155d8 : bv 32 := 0x00913423.
Lemma F_155d8 : fetch_word Plain.M.loaded_segments (0x15630 : word) = Some W_155d8.
Proof. vm_refl. Qed.
Lemma D_155d8 : decode_any W_155d8 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155dc : bv 32 := 0x00058493.
Lemma F_155dc : fetch_word Plain.M.loaded_segments (0x15634 : word) = Some W_155dc.
Proof. vm_refl. Qed.
Lemma D_155dc : decode_any W_155dc = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155e0 : bv 32 := 0x00050413.
Lemma F_155e0 : fetch_word Plain.M.loaded_segments (0x15638 : word) = Some W_155e0.
Proof. vm_refl. Qed.
Lemma D_155e0 : decode_any W_155e0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155e4 : bv 32 := 0x00053503.
Lemma F_155e4 : fetch_word Plain.M.loaded_segments (0x1563c : word) = Some W_155e4.
Proof. vm_refl. Qed.
Lemma D_155e4 : decode_any W_155e4 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155e8 : bv 32 := 0x00050463.
Lemma F_155e8 : fetch_word Plain.M.loaded_segments (0x15640 : word) = Some W_155e8.
Proof. vm_refl. Qed.
Lemma D_155e8 : decode_any W_155e8 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155f0 : bv 32 := 0x04048063.
Lemma F_155f0 : fetch_word Plain.M.loaded_segments (0x15648 : word) = Some W_155f0.
Proof. vm_refl. Qed.
Lemma D_155f0 : decode_any W_155f0 = Some (Branch BC_EQ 9 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15630 : bv 32 := 0x00000593.
Lemma F_15630 : fetch_word Plain.M.loaded_segments (0x15688 : word) = Some W_15630.
Proof. vm_refl. Qed.
Lemma D_15630 : decode_any W_15630 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15634 : bv 32 := 0x00000513.
Lemma F_15634 : fetch_word Plain.M.loaded_segments (0x1568c : word) = Some W_15634.
Proof. vm_refl. Qed.
Lemma D_15634 : decode_any W_15634 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15638 : bv 32 := 0x00b43023.
Lemma F_15638 : fetch_word Plain.M.loaded_segments (0x15690 : word) = Some W_15638.
Proof. vm_refl. Qed.
Lemma D_15638 : decode_any W_15638 = Some (Store SZ8 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1563c : bv 32 := 0x01813083.
Lemma F_1563c : fetch_word Plain.M.loaded_segments (0x15694 : word) = Some W_1563c.
Proof. vm_refl. Qed.
Lemma D_1563c : decode_any W_1563c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15640 : bv 32 := 0x01013403.
Lemma F_15640 : fetch_word Plain.M.loaded_segments (0x15698 : word) = Some W_15640.
Proof. vm_refl. Qed.
Lemma D_15640 : decode_any W_15640 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15644 : bv 32 := 0x00813483.
Lemma F_15644 : fetch_word Plain.M.loaded_segments (0x1569c : word) = Some W_15644.
Proof. vm_refl. Qed.
Lemma D_15644 : decode_any W_15644 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15648 : bv 32 := 0x02010113.
Lemma F_15648 : fetch_word Plain.M.loaded_segments (0x156a0 : word) = Some W_15648.
Proof. vm_refl. Qed.
Lemma D_15648 : decode_any W_15648 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1564c : bv 32 := 0x00008067.
Lemma F_1564c : fetch_word Plain.M.loaded_segments (0x156a4 : word) = Some W_1564c.
Proof. vm_refl. Qed.
Lemma D_1564c : decode_any W_1564c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

