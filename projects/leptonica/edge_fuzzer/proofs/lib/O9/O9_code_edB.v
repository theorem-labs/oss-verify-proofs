(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.H Require GcFlushS9.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_625bc : bv 32 := 0x00050663.
Lemma F_625bc : fetch_word Plain.M.loaded_segments (0x62614 : word) = Some W_625bc.
Proof. vm_refl. Qed.
Lemma D_625bc : decode_any W_625bc = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_625c0 : bv 32 := 0x01052503.
Lemma F_625c0 : fetch_word Plain.M.loaded_segments (0x62618 : word) = Some W_625c0.
Proof. vm_refl. Qed.
Lemma D_625c0 : decode_any W_625c0 = Some (Load SZ4 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_625c4 : bv 32 := 0x00008067.
Lemma F_625c4 : fetch_word Plain.M.loaded_segments (0x6261c : word) = Some W_625c4.
Proof. vm_refl. Qed.
Lemma D_625c4 : decode_any W_625c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628b8 : bv 32 := 0x00058463.
Lemma F_628b8 : fetch_word Plain.M.loaded_segments (0x62910 : word) = Some W_628b8.
Proof. vm_refl. Qed.
Lemma D_628b8 : decode_any W_628b8 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628bc : bv 32 := 0x0005a023.
Lemma F_628bc : fetch_word Plain.M.loaded_segments (0x62914 : word) = Some W_628bc.
Proof. vm_refl. Qed.
Lemma D_628bc : decode_any W_628bc = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628c0 : bv 32 := 0x00060463.
Lemma F_628c0 : fetch_word Plain.M.loaded_segments (0x62918 : word) = Some W_628c0.
Proof. vm_refl. Qed.
Lemma D_628c0 : decode_any W_628c0 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628c4 : bv 32 := 0x00062023.
Lemma F_628c4 : fetch_word Plain.M.loaded_segments (0x6291c : word) = Some W_628c4.
Proof. vm_refl. Qed.
Lemma D_628c4 : decode_any W_628c4 = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628c8 : bv 32 := 0x00068463.
Lemma F_628c8 : fetch_word Plain.M.loaded_segments (0x62920 : word) = Some W_628c8.
Proof. vm_refl. Qed.
Lemma D_628c8 : decode_any W_628c8 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628cc : bv 32 := 0x0006a023.
Lemma F_628cc : fetch_word Plain.M.loaded_segments (0x62924 : word) = Some W_628cc.
Proof. vm_refl. Qed.
Lemma D_628cc : decode_any W_628cc = Some (Store SZ4 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628d0 : bv 32 := 0x02050a63.
Lemma F_628d0 : fetch_word Plain.M.loaded_segments (0x62928 : word) = Some W_628d0.
Proof. vm_refl. Qed.
Lemma D_628d0 : decode_any W_628d0 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628d4 : bv 32 := 0x00058663.
Lemma F_628d4 : fetch_word Plain.M.loaded_segments (0x6292c : word) = Some W_628d4.
Proof. vm_refl. Qed.
Lemma D_628d4 : decode_any W_628d4 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628d8 : bv 32 := 0x00052703.
Lemma F_628d8 : fetch_word Plain.M.loaded_segments (0x62930 : word) = Some W_628d8.
Proof. vm_refl. Qed.
Lemma D_628d8 : decode_any W_628d8 = Some (Load SZ4 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628dc : bv 32 := 0x00e5a023.
Lemma F_628dc : fetch_word Plain.M.loaded_segments (0x62934 : word) = Some W_628dc.
Proof. vm_refl. Qed.
Lemma D_628dc : decode_any W_628dc = Some (Store SZ4 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628e0 : bv 32 := 0x00060663.
Lemma F_628e0 : fetch_word Plain.M.loaded_segments (0x62938 : word) = Some W_628e0.
Proof. vm_refl. Qed.
Lemma D_628e0 : decode_any W_628e0 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628e4 : bv 32 := 0x00452583.
Lemma F_628e4 : fetch_word Plain.M.loaded_segments (0x6293c : word) = Some W_628e4.
Proof. vm_refl. Qed.
Lemma D_628e4 : decode_any W_628e4 = Some (Load SZ4 true 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628e8 : bv 32 := 0x00b62023.
Lemma F_628e8 : fetch_word Plain.M.loaded_segments (0x62940 : word) = Some W_628e8.
Proof. vm_refl. Qed.
Lemma D_628e8 : decode_any W_628e8 = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628ec : bv 32 := 0x00000593.
Lemma F_628ec : fetch_word Plain.M.loaded_segments (0x62944 : word) = Some W_628ec.
Proof. vm_refl. Qed.
Lemma D_628ec : decode_any W_628ec = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628f0 : bv 32 := 0x00068663.
Lemma F_628f0 : fetch_word Plain.M.loaded_segments (0x62948 : word) = Some W_628f0.
Proof. vm_refl. Qed.
Lemma D_628f0 : decode_any W_628f0 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628f4 : bv 32 := 0x00852503.
Lemma F_628f4 : fetch_word Plain.M.loaded_segments (0x6294c : word) = Some W_628f4.
Proof. vm_refl. Qed.
Lemma D_628f4 : decode_any W_628f4 = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628f8 : bv 32 := 0x00a6a023.
Lemma F_628f8 : fetch_word Plain.M.loaded_segments (0x62950 : word) = Some W_628f8.
Proof. vm_refl. Qed.
Lemma D_628f8 : decode_any W_628f8 = Some (Store SZ4 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628fc : bv 32 := 0x00058513.
Lemma F_628fc : fetch_word Plain.M.loaded_segments (0x62954 : word) = Some W_628fc.
Proof. vm_refl. Qed.
Lemma D_628fc : decode_any W_628fc = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62900 : bv 32 := 0x00008067.
Lemma F_62900 : fetch_word Plain.M.loaded_segments (0x62958 : word) = Some W_62900.
Proof. vm_refl. Qed.
Lemma D_62900 : decode_any W_62900 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63264 : bv 32 := 0x00050663.
Lemma F_63264 : fetch_word Plain.M.loaded_segments (0x632bc : word) = Some W_63264.
Proof. vm_refl. Qed.
Lemma D_63264 : decode_any W_63264 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63268 : bv 32 := 0x00852503.
Lemma F_63268 : fetch_word Plain.M.loaded_segments (0x632c0 : word) = Some W_63268.
Proof. vm_refl. Qed.
Lemma D_63268 : decode_any W_63268 = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6326c : bv 32 := 0x00008067.
Lemma F_6326c : fetch_word Plain.M.loaded_segments (0x632c4 : word) = Some W_6326c.
Proof. vm_refl. Qed.
Lemma D_6326c : decode_any W_6326c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63324 : bv 32 := 0x00050663.
Lemma F_63324 : fetch_word Plain.M.loaded_segments (0x6337c : word) = Some W_63324.
Proof. vm_refl. Qed.
Lemma D_63324 : decode_any W_63324 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63328 : bv 32 := 0x03853503.
Lemma F_63328 : fetch_word Plain.M.loaded_segments (0x63380 : word) = Some W_63328.
Proof. vm_refl. Qed.
Lemma D_63328 : decode_any W_63328 = Some (Load SZ8 true 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6332c : bv 32 := 0x00008067.
Lemma F_6332c : fetch_word Plain.M.loaded_segments (0x63384 : word) = Some W_6332c.
Proof. vm_refl. Qed.
Lemma D_6332c : decode_any W_6332c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63524 : bv 32 := 0xfc010113.
Lemma F_63524 : fetch_word Plain.M.loaded_segments (0x6357c : word) = Some W_63524.
Proof. vm_refl. Qed.
Lemma D_63524 : decode_any W_63524 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63528 : bv 32 := 0x02113c23.
Lemma F_63528 : fetch_word Plain.M.loaded_segments (0x63580 : word) = Some W_63528.
Proof. vm_refl. Qed.
Lemma D_63528 : decode_any W_63528 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6352c : bv 32 := 0x02813823.
Lemma F_6352c : fetch_word Plain.M.loaded_segments (0x63584 : word) = Some W_6352c.
Proof. vm_refl. Qed.
Lemma D_6352c : decode_any W_6352c = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63530 : bv 32 := 0x02913423.
Lemma F_63530 : fetch_word Plain.M.loaded_segments (0x63588 : word) = Some W_63530.
Proof. vm_refl. Qed.
Lemma D_63530 : decode_any W_63530 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63534 : bv 32 := 0x03213023.
Lemma F_63534 : fetch_word Plain.M.loaded_segments (0x6358c : word) = Some W_63534.
Proof. vm_refl. Qed.
Lemma D_63534 : decode_any W_63534 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63538 : bv 32 := 0x01313c23.
Lemma F_63538 : fetch_word Plain.M.loaded_segments (0x63590 : word) = Some W_63538.
Proof. vm_refl. Qed.
Lemma D_63538 : decode_any W_63538 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6353c : bv 32 := 0x01413823.
Lemma F_6353c : fetch_word Plain.M.loaded_segments (0x63594 : word) = Some W_6353c.
Proof. vm_refl. Qed.
Lemma D_6353c : decode_any W_6353c = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63540 : bv 32 := 0x0a068a63.
Lemma F_63540 : fetch_word Plain.M.loaded_segments (0x63598 : word) = Some W_63540.
Proof. vm_refl. Qed.
Lemma D_63540 : decode_any W_63540 = Some (Branch BC_EQ 13 0 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63544 : bv 32 := 0x0006a023.
Lemma F_63544 : fetch_word Plain.M.loaded_segments (0x6359c : word) = Some W_63544.
Proof. vm_refl. Qed.
Lemma D_63544 : decode_any W_63544 = Some (Store SZ4 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63548 : bv 32 := 0x0c050a63.
Lemma F_63548 : fetch_word Plain.M.loaded_segments (0x635a0 : word) = Some W_63548.
Proof. vm_refl. Qed.
Lemma D_63548 : decode_any W_63548 = Some (Branch BC_EQ 10 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6354c : bv 32 := 0x00060493.
Lemma F_6354c : fetch_word Plain.M.loaded_segments (0x635a4 : word) = Some W_6354c.
Proof. vm_refl. Qed.
Lemma D_6354c : decode_any W_6354c = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63550 : bv 32 := 0x00058413.
Lemma F_63550 : fetch_word Plain.M.loaded_segments (0x635a8 : word) = Some W_63550.
Proof. vm_refl. Qed.
Lemma D_63550 : decode_any W_63550 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63554 : bv 32 := 0x00068a13.
Lemma F_63554 : fetch_word Plain.M.loaded_segments (0x635ac : word) = Some W_63554.
Proof. vm_refl. Qed.
Lemma D_63554 : decode_any W_63554 = Some (OpImm ALU_ADD 20 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63558 : bv 32 := 0x00c10593.
Lemma F_63558 : fetch_word Plain.M.loaded_segments (0x635b0 : word) = Some W_63558.
Proof. vm_refl. Qed.
Lemma D_63558 : decode_any W_63558 = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6355c : bv 32 := 0x00810613.
Lemma F_6355c : fetch_word Plain.M.loaded_segments (0x635b4 : word) = Some W_6355c.
Proof. vm_refl. Qed.
Lemma D_6355c : decode_any W_6355c = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63560 : bv 32 := 0x00410693.
Lemma F_63560 : fetch_word Plain.M.loaded_segments (0x635b8 : word) = Some W_63560.
Proof. vm_refl. Qed.
Lemma D_63560 : decode_any W_63560 = Some (OpImm ALU_ADD 13 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63564 : bv 32 := 0x00050993.
Lemma F_63564 : fetch_word Plain.M.loaded_segments (0x635bc : word) = Some W_63564.
Proof. vm_refl. Qed.
Lemma D_63564 : decode_any W_63564 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63568 : bv 32 := 0xb50ff0ef.
Lemma F_63568 : fetch_word Plain.M.loaded_segments (0x635c0 : word) = Some W_63568.
Proof. vm_refl. Qed.
Lemma D_63568 : decode_any W_63568 = Some (Jal 1 2093904, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6356c : bv 32 := 0x00200513.
Lemma F_6356c : fetch_word Plain.M.loaded_segments (0x635c4 : word) = Some W_6356c.
Proof. vm_refl. Qed.
Lemma D_6356c : decode_any W_6356c = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63570 : bv 32 := 0x1a044663.
Lemma F_63570 : fetch_word Plain.M.loaded_segments (0x635c8 : word) = Some W_63570.
Proof. vm_refl. Qed.
Lemma D_63570 : decode_any W_63570 = Some (Branch BC_LT 8 0 428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63574 : bv 32 := 0x1a04c463.
Lemma F_63574 : fetch_word Plain.M.loaded_segments (0x635cc : word) = Some W_63574.
Proof. vm_refl. Qed.
Lemma D_63574 : decode_any W_63574 = Some (Branch BC_LT 9 0 424, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63578 : bv 32 := 0x00c12583.
Lemma F_63578 : fetch_word Plain.M.loaded_segments (0x635d0 : word) = Some W_63578.
Proof. vm_refl. Qed.
Lemma D_63578 : decode_any W_63578 = Some (Load SZ4 true 11 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6357c : bv 32 := 0x1ab45063.
Lemma F_6357c : fetch_word Plain.M.loaded_segments (0x635d4 : word) = Some W_6357c.
Proof. vm_refl. Qed.
Lemma D_6357c : decode_any W_6357c = Some (Branch BC_GE 8 11 416, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63580 : bv 32 := 0x00812583.
Lemma F_63580 : fetch_word Plain.M.loaded_segments (0x635d8 : word) = Some W_63580.
Proof. vm_refl. Qed.
Lemma D_63580 : decode_any W_63580 = Some (Load SZ4 true 11 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63584 : bv 32 := 0x18b4dc63.
Lemma F_63584 : fetch_word Plain.M.loaded_segments (0x635dc : word) = Some W_63584.
Proof. vm_refl. Qed.
Lemma D_63584 : decode_any W_63584 = Some (Branch BC_GE 9 11 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63588 : bv 32 := 0x00098513.
Lemma F_63588 : fetch_word Plain.M.loaded_segments (0x635e0 : word) = Some W_63588.
Proof. vm_refl. Qed.
Lemma D_63588 : decode_any W_63588 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6358c : bv 32 := 0x830ff0ef.
Lemma F_6358c : fetch_word Plain.M.loaded_segments (0x635e4 : word) = Some W_6358c.
Proof. vm_refl. Qed.
Lemma D_6358c : decode_any W_6358c = Some (Jal 1 2093104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63590 : bv 32 := 0x00050913.
Lemma F_63590 : fetch_word Plain.M.loaded_segments (0x635e8 : word) = Some W_63590.
Proof. vm_refl. Qed.
Lemma D_63590 : decode_any W_63590 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63594 : bv 32 := 0x00098513.
Lemma F_63594 : fetch_word Plain.M.loaded_segments (0x635ec : word) = Some W_63594.
Proof. vm_refl. Qed.
Lemma D_63594 : decode_any W_63594 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63598 : bv 32 := 0xd8dff0ef.
Lemma F_63598 : fetch_word Plain.M.loaded_segments (0x635f0 : word) = Some W_63598.
Proof. vm_refl. Qed.
Lemma D_63598 : decode_any W_63598 = Some (Jal 1 2096524, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6359c : bv 32 := 0x00412583.
Lemma F_6359c : fetch_word Plain.M.loaded_segments (0x635f4 : word) = Some W_6359c.
Proof. vm_refl. Qed.
Lemma D_6359c : decode_any W_6359c = Some (Load SZ4 true 11 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635a0 : bv 32 := 0xfff58593.
Lemma F_635a0 : fetch_word Plain.M.loaded_segments (0x635f8 : word) = Some W_635a0.
Proof. vm_refl. Qed.
Lemma D_635a0 : decode_any W_635a0 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635a4 : bv 32 := 0x01f00613.
Lemma F_635a4 : fetch_word Plain.M.loaded_segments (0x635fc : word) = Some W_635a4.
Proof. vm_refl. Qed.
Lemma D_635a4 : decode_any W_635a4 = Some (OpImm ALU_ADD 12 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635a8 : bv 32 := 0x0eb66863.
Lemma F_635a8 : fetch_word Plain.M.loaded_segments (0x63600 : word) = Some W_635a8.
Proof. vm_refl. Qed.
Lemma D_635a8 : decode_any W_635a8 = Some (Branch BC_LTU 12 11 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635ac : bv 32 := 0x00259593.
Lemma F_635ac : fetch_word Plain.M.loaded_segments (0x63604 : word) = Some W_635ac.
Proof. vm_refl. Qed.
Lemma D_635ac : decode_any W_635ac = Some (ShiftImm ALU_SLL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635b0 : bv 32 := 0xfffb9617.
Lemma F_635b0 : fetch_word Plain.M.loaded_segments (0x63608 : word) = Some W_635b0.
Proof. vm_refl. Qed.
Lemma D_635b0 : decode_any W_635b0 = Some (Auipc 12 1048505, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635b4 : bv 32 := 0x04460613.
Lemma F_635b4 : fetch_word Plain.M.loaded_segments (0x6360c : word) = Some W_635b4.
Proof. vm_refl. Qed.
Lemma D_635b4 : decode_any W_635b4 = Some (OpImm ALU_ADD 12 12 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635b8 : bv 32 := 0x00c585b3.
Lemma F_635b8 : fetch_word Plain.M.loaded_segments (0x63610 : word) = Some W_635b8.
Proof. vm_refl. Qed.
Lemma D_635b8 : decode_any W_635b8 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635bc : bv 32 := 0x0005a583.
Lemma F_635bc : fetch_word Plain.M.loaded_segments (0x63614 : word) = Some W_635bc.
Proof. vm_refl. Qed.
Lemma D_635bc : decode_any W_635bc = Some (Load SZ4 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635c0 : bv 32 := 0x029906bb.
Lemma F_635c0 : fetch_word Plain.M.loaded_segments (0x63618 : word) = Some W_635c0.
Proof. vm_refl. Qed.
Lemma D_635c0 : decode_any W_635c0 = Some (Mul32 M_MUL 13 18 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635c4 : bv 32 := 0x00269693.
Lemma F_635c4 : fetch_word Plain.M.loaded_segments (0x6361c : word) = Some W_635c4.
Proof. vm_refl. Qed.
Lemma D_635c4 : decode_any W_635c4 = Some (ShiftImm ALU_SLL 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635c8 : bv 32 := 0x00c585b3.
Lemma F_635c8 : fetch_word Plain.M.loaded_segments (0x63620 : word) = Some W_635c8.
Proof. vm_refl. Qed.
Lemma D_635c8 : decode_any W_635c8 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635cc : bv 32 := 0x00d50533.
Lemma F_635cc : fetch_word Plain.M.loaded_segments (0x63624 : word) = Some W_635cc.
Proof. vm_refl. Qed.
Lemma D_635cc : decode_any W_635cc = Some (Op ALU_ADD 10 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635d0 : bv 32 := 0x00058067.
Lemma F_635d0 : fetch_word Plain.M.loaded_segments (0x63628 : word) = Some W_635d0.
Proof. vm_refl. Qed.
Lemma D_635d0 : decode_any W_635d0 = Some (Jalr 0 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635d4 : bv 32 := 0x0054559b.
Lemma F_635d4 : fetch_word Plain.M.loaded_segments (0x6362c : word) = Some W_635d4.
Proof. vm_refl. Qed.
Lemma D_635d4 : decode_any W_635d4 = Some (ShiftImm32 ALU_SRL 11 8 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635d8 : bv 32 := 0x00259593.
Lemma F_635d8 : fetch_word Plain.M.loaded_segments (0x63630 : word) = Some W_635d8.
Proof. vm_refl. Qed.
Lemma D_635d8 : decode_any W_635d8 = Some (ShiftImm ALU_SLL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635dc : bv 32 := 0x00b50533.
Lemma F_635dc : fetch_word Plain.M.loaded_segments (0x63634 : word) = Some W_635dc.
Proof. vm_refl. Qed.
Lemma D_635dc : decode_any W_635dc = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635e0 : bv 32 := 0x00052503.
Lemma F_635e0 : fetch_word Plain.M.loaded_segments (0x63638 : word) = Some W_635e0.
Proof. vm_refl. Qed.
Lemma D_635e0 : decode_any W_635e0 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635e4 : bv 32 := 0xfff44593.
Lemma F_635e4 : fetch_word Plain.M.loaded_segments (0x6363c : word) = Some W_635e4.
Proof. vm_refl. Qed.
Lemma D_635e4 : decode_any W_635e4 = Some (OpImm ALU_XOR 11 8 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635e8 : bv 32 := 0x00b555bb.
Lemma F_635e8 : fetch_word Plain.M.loaded_segments (0x63640 : word) = Some W_635e8.
Proof. vm_refl. Qed.
Lemma D_635e8 : decode_any W_635e8 = Some (Op32 ALU_SRL 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635ec : bv 32 := 0x0015f593.
Lemma F_635ec : fetch_word Plain.M.loaded_segments (0x63644 : word) = Some W_635ec.
Proof. vm_refl. Qed.
Lemma D_635ec : decode_any W_635ec = Some (OpImm ALU_AND 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635f0 : bv 32 := 0x1240006f.
Lemma F_635f0 : fetch_word Plain.M.loaded_segments (0x63648 : word) = Some W_635f0.
Proof. vm_refl. Qed.
Lemma D_635f0 : decode_any W_635f0 = Some (Jal 0 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63714 : bv 32 := 0x00000513.
Lemma F_63714 : fetch_word Plain.M.loaded_segments (0x6376c : word) = Some W_63714.
Proof. vm_refl. Qed.
Lemma D_63714 : decode_any W_63714 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63718 : bv 32 := 0x00ba2023.
Lemma F_63718 : fetch_word Plain.M.loaded_segments (0x63770 : word) = Some W_63718.
Proof. vm_refl. Qed.
Lemma D_63718 : decode_any W_63718 = Some (Store SZ4 20 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6371c : bv 32 := 0x03813083.
Lemma F_6371c : fetch_word Plain.M.loaded_segments (0x63774 : word) = Some W_6371c.
Proof. vm_refl. Qed.
Lemma D_6371c : decode_any W_6371c = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63720 : bv 32 := 0x03013403.
Lemma F_63720 : fetch_word Plain.M.loaded_segments (0x63778 : word) = Some W_63720.
Proof. vm_refl. Qed.
Lemma D_63720 : decode_any W_63720 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63724 : bv 32 := 0x02813483.
Lemma F_63724 : fetch_word Plain.M.loaded_segments (0x6377c : word) = Some W_63724.
Proof. vm_refl. Qed.
Lemma D_63724 : decode_any W_63724 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63728 : bv 32 := 0x02013903.
Lemma F_63728 : fetch_word Plain.M.loaded_segments (0x63780 : word) = Some W_63728.
Proof. vm_refl. Qed.
Lemma D_63728 : decode_any W_63728 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6372c : bv 32 := 0x01813983.
Lemma F_6372c : fetch_word Plain.M.loaded_segments (0x63784 : word) = Some W_6372c.
Proof. vm_refl. Qed.
Lemma D_6372c : decode_any W_6372c = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63730 : bv 32 := 0x01013a03.
Lemma F_63730 : fetch_word Plain.M.loaded_segments (0x63788 : word) = Some W_63730.
Proof. vm_refl. Qed.
Lemma D_63730 : decode_any W_63730 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63734 : bv 32 := 0x04010113.
Lemma F_63734 : fetch_word Plain.M.loaded_segments (0x6378c : word) = Some W_63734.
Proof. vm_refl. Qed.
Lemma D_63734 : decode_any W_63734 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63738 : bv 32 := 0x00008067.
Lemma F_63738 : fetch_word Plain.M.loaded_segments (0x63790 : word) = Some W_63738.
Proof. vm_refl. Qed.
Lemma D_63738 : decode_any W_63738 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d38 : bv 32 := 0xf7010113.
Lemma F_77d38 : fetch_word Plain.M.loaded_segments (0x77d90 : word) = Some W_77d38.
Proof. vm_refl. Qed.
Lemma D_77d38 : decode_any W_77d38 = Some (OpImm ALU_ADD 2 2 3952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d3c : bv 32 := 0x08113423.
Lemma F_77d3c : fetch_word Plain.M.loaded_segments (0x77d94 : word) = Some W_77d3c.
Proof. vm_refl. Qed.
Lemma D_77d3c : decode_any W_77d3c = Some (Store SZ8 2 1 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d40 : bv 32 := 0x08813023.
Lemma F_77d40 : fetch_word Plain.M.loaded_segments (0x77d98 : word) = Some W_77d40.
Proof. vm_refl. Qed.
Lemma D_77d40 : decode_any W_77d40 = Some (Store SZ8 2 8 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d44 : bv 32 := 0x06913c23.
Lemma F_77d44 : fetch_word Plain.M.loaded_segments (0x77d9c : word) = Some W_77d44.
Proof. vm_refl. Qed.
Lemma D_77d44 : decode_any W_77d44 = Some (Store SZ8 2 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d48 : bv 32 := 0x07213823.
Lemma F_77d48 : fetch_word Plain.M.loaded_segments (0x77da0 : word) = Some W_77d48.
Proof. vm_refl. Qed.
Lemma D_77d48 : decode_any W_77d48 = Some (Store SZ8 2 18 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d4c : bv 32 := 0x07313423.
Lemma F_77d4c : fetch_word Plain.M.loaded_segments (0x77da4 : word) = Some W_77d4c.
Proof. vm_refl. Qed.
Lemma D_77d4c : decode_any W_77d4c = Some (Store SZ8 2 19 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d50 : bv 32 := 0x07413023.
Lemma F_77d50 : fetch_word Plain.M.loaded_segments (0x77da8 : word) = Some W_77d50.
Proof. vm_refl. Qed.
Lemma D_77d50 : decode_any W_77d50 = Some (Store SZ8 2 20 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d54 : bv 32 := 0x05513c23.
Lemma F_77d54 : fetch_word Plain.M.loaded_segments (0x77dac : word) = Some W_77d54.
Proof. vm_refl. Qed.
Lemma D_77d54 : decode_any W_77d54 = Some (Store SZ8 2 21 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d58 : bv 32 := 0x05613823.
Lemma F_77d58 : fetch_word Plain.M.loaded_segments (0x77db0 : word) = Some W_77d58.
Proof. vm_refl. Qed.
Lemma D_77d58 : decode_any W_77d58 = Some (Store SZ8 2 22 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d5c : bv 32 := 0x05713423.
Lemma F_77d5c : fetch_word Plain.M.loaded_segments (0x77db4 : word) = Some W_77d5c.
Proof. vm_refl. Qed.
Lemma D_77d5c : decode_any W_77d5c = Some (Store SZ8 2 23 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d60 : bv 32 := 0x05813023.
Lemma F_77d60 : fetch_word Plain.M.loaded_segments (0x77db8 : word) = Some W_77d60.
Proof. vm_refl. Qed.
Lemma D_77d60 : decode_any W_77d60 = Some (Store SZ8 2 24 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d64 : bv 32 := 0x03913c23.
Lemma F_77d64 : fetch_word Plain.M.loaded_segments (0x77dbc : word) = Some W_77d64.
Proof. vm_refl. Qed.
Lemma D_77d64 : decode_any W_77d64 = Some (Store SZ8 2 25 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d68 : bv 32 := 0x03a13823.
Lemma F_77d68 : fetch_word Plain.M.loaded_segments (0x77dc0 : word) = Some W_77d68.
Proof. vm_refl. Qed.
Lemma D_77d68 : decode_any W_77d68 = Some (Store SZ8 2 26 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d6c : bv 32 := 0x03b13423.
Lemma F_77d6c : fetch_word Plain.M.loaded_segments (0x77dc4 : word) = Some W_77d6c.
Proof. vm_refl. Qed.
Lemma D_77d6c : decode_any W_77d6c = Some (Store SZ8 2 27 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d70 : bv 32 := 0x04050663.
Lemma F_77d70 : fetch_word Plain.M.loaded_segments (0x77dc8 : word) = Some W_77d70.
Proof. vm_refl. Qed.
Lemma D_77d70 : decode_any W_77d70 = Some (Branch BC_EQ 10 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d74 : bv 32 := 0x00060413.
Lemma F_77d74 : fetch_word Plain.M.loaded_segments (0x77dcc : word) = Some W_77d74.
Proof. vm_refl. Qed.
Lemma D_77d74 : decode_any W_77d74 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d78 : bv 32 := 0x00058913.
Lemma F_77d78 : fetch_word Plain.M.loaded_segments (0x77dd0 : word) = Some W_77d78.
Proof. vm_refl. Qed.
Lemma D_77d78 : decode_any W_77d78 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d7c : bv 32 := 0x00050993.
Lemma F_77d7c : fetch_word Plain.M.loaded_segments (0x77dd4 : word) = Some W_77d7c.
Proof. vm_refl. Qed.
Lemma D_77d7c : decode_any W_77d7c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d80 : bv 32 := 0xce4eb0ef.
Lemma F_77d80 : fetch_word Plain.M.loaded_segments (0x77dd8 : word) = Some W_77d80.
Proof. vm_refl. Qed.
Lemma D_77d80 : decode_any W_77d80 = Some (Jal 1 2012388, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d84 : bv 32 := 0x00100593.
Lemma F_77d84 : fetch_word Plain.M.loaded_segments (0x77ddc : word) = Some W_77d84.
Proof. vm_refl. Qed.
Lemma D_77d84 : decode_any W_77d84 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d88 : bv 32 := 0x02b51a63.
Lemma F_77d88 : fetch_word Plain.M.loaded_segments (0x77de0 : word) = Some W_77d88.
Proof. vm_refl. Qed.
Lemma D_77d88 : decode_any W_77d88 = Some (Branch BC_NE 10 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d8c : bv 32 := 0x00400513.
Lemma F_77d8c : fetch_word Plain.M.loaded_segments (0x77de4 : word) = Some W_77d8c.
Proof. vm_refl. Qed.
Lemma D_77d8c : decode_any W_77d8c = Some (OpImm ALU_ADD 10 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d90 : bv 32 := 0x0ca96a63.
Lemma F_77d90 : fetch_word Plain.M.loaded_segments (0x77de8 : word) = Some W_77d90.
Proof. vm_refl. Qed.
Lemma D_77d90 : decode_any W_77d90 = Some (Branch BC_LTU 18 10 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77e24 : bv 32 := 0x00048513.
Lemma F_77e24 : fetch_word Plain.M.loaded_segments (0x77e7c : word) = Some W_77e24.
Proof. vm_refl. Qed.
Lemma D_77e24 : decode_any W_77e24 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77e28 : bv 32 := 0x08813083.
Lemma F_77e28 : fetch_word Plain.M.loaded_segments (0x77e80 : word) = Some W_77e28.
Proof. vm_refl. Qed.
Lemma D_77e28 : decode_any W_77e28 = Some (Load SZ8 true 1 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77e2c : bv 32 := 0x08013403.
Lemma F_77e2c : fetch_word Plain.M.loaded_segments (0x77e84 : word) = Some W_77e2c.
Proof. vm_refl. Qed.
Lemma D_77e2c : decode_any W_77e2c = Some (Load SZ8 true 8 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77e30 : bv 32 := 0x07813483.
Lemma F_77e30 : fetch_word Plain.M.loaded_segments (0x77e88 : word) = Some W_77e30.
Proof. vm_refl. Qed.
Lemma D_77e30 : decode_any W_77e30 = Some (Load SZ8 true 9 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77e34 : bv 32 := 0x07013903.
Lemma F_77e34 : fetch_word Plain.M.loaded_segments (0x77e8c : word) = Some W_77e34.
Proof. vm_refl. Qed.
Lemma D_77e34 : decode_any W_77e34 = Some (Load SZ8 true 18 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77e38 : bv 32 := 0x06813983.
Lemma F_77e38 : fetch_word Plain.M.loaded_segments (0x77e90 : word) = Some W_77e38.
Proof. vm_refl. Qed.
Lemma D_77e38 : decode_any W_77e38 = Some (Load SZ8 true 19 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77e3c : bv 32 := 0x06013a03.
Lemma F_77e3c : fetch_word Plain.M.loaded_segments (0x77e94 : word) = Some W_77e3c.
Proof. vm_refl. Qed.
Lemma D_77e3c : decode_any W_77e3c = Some (Load SZ8 true 20 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77e40 : bv 32 := 0x05813a83.
Lemma F_77e40 : fetch_word Plain.M.loaded_segments (0x77e98 : word) = Some W_77e40.
Proof. vm_refl. Qed.
Lemma D_77e40 : decode_any W_77e40 = Some (Load SZ8 true 21 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77e44 : bv 32 := 0x05013b03.
Lemma F_77e44 : fetch_word Plain.M.loaded_segments (0x77e9c : word) = Some W_77e44.
Proof. vm_refl. Qed.
Lemma D_77e44 : decode_any W_77e44 = Some (Load SZ8 true 22 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77e48 : bv 32 := 0x04813b83.
Lemma F_77e48 : fetch_word Plain.M.loaded_segments (0x77ea0 : word) = Some W_77e48.
Proof. vm_refl. Qed.
Lemma D_77e48 : decode_any W_77e48 = Some (Load SZ8 true 23 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77e4c : bv 32 := 0x04013c03.
Lemma F_77e4c : fetch_word Plain.M.loaded_segments (0x77ea4 : word) = Some W_77e4c.
Proof. vm_refl. Qed.
Lemma D_77e4c : decode_any W_77e4c = Some (Load SZ8 true 24 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77e50 : bv 32 := 0x03813c83.
Lemma F_77e50 : fetch_word Plain.M.loaded_segments (0x77ea8 : word) = Some W_77e50.
Proof. vm_refl. Qed.
Lemma D_77e50 : decode_any W_77e50 = Some (Load SZ8 true 25 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77e54 : bv 32 := 0x03013d03.
Lemma F_77e54 : fetch_word Plain.M.loaded_segments (0x77eac : word) = Some W_77e54.
Proof. vm_refl. Qed.
Lemma D_77e54 : decode_any W_77e54 = Some (Load SZ8 true 26 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77e58 : bv 32 := 0x02813d83.
Lemma F_77e58 : fetch_word Plain.M.loaded_segments (0x77eb0 : word) = Some W_77e58.
Proof. vm_refl. Qed.
Lemma D_77e58 : decode_any W_77e58 = Some (Load SZ8 true 27 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77e5c : bv 32 := 0x09010113.
Lemma F_77e5c : fetch_word Plain.M.loaded_segments (0x77eb4 : word) = Some W_77e5c.
Proof. vm_refl. Qed.
Lemma D_77e5c : decode_any W_77e5c = Some (OpImm ALU_ADD 2 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77e60 : bv 32 := 0x00008067.
Lemma F_77e60 : fetch_word Plain.M.loaded_segments (0x77eb8 : word) = Some W_77e60.
Proof. vm_refl. Qed.
Lemma D_77e60 : decode_any W_77e60 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77e64 : bv 32 := 0x01c10593.
Lemma F_77e64 : fetch_word Plain.M.loaded_segments (0x77ebc : word) = Some W_77e64.
Proof. vm_refl. Qed.
Lemma D_77e64 : decode_any W_77e64 = Some (OpImm ALU_ADD 11 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77e68 : bv 32 := 0x01810613.
Lemma F_77e68 : fetch_word Plain.M.loaded_segments (0x77ec0 : word) = Some W_77e68.
Proof. vm_refl. Qed.
Lemma D_77e68 : decode_any W_77e68 = Some (OpImm ALU_ADD 12 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77e6c : bv 32 := 0x01810493.
Lemma F_77e6c : fetch_word Plain.M.loaded_segments (0x77ec4 : word) = Some W_77e6c.
Proof. vm_refl. Qed.
Lemma D_77e6c : decode_any W_77e6c = Some (OpImm ALU_ADD 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77e70 : bv 32 := 0x00098513.
Lemma F_77e70 : fetch_word Plain.M.loaded_segments (0x77ec8 : word) = Some W_77e70.
Proof. vm_refl. Qed.
Lemma D_77e70 : decode_any W_77e70 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77e74 : bv 32 := 0x00000693.
Lemma F_77e74 : fetch_word Plain.M.loaded_segments (0x77ecc : word) = Some W_77e74.
Proof. vm_refl. Qed.
Lemma D_77e74 : decode_any W_77e74 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77e78 : bv 32 := 0xa41ea0ef.
Lemma F_77e78 : fetch_word Plain.M.loaded_segments (0x77ed0 : word) = Some W_77e78.
Proof. vm_refl. Qed.
Lemma D_77e78 : decode_any W_77e78 = Some (Jal 1 2009664, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77e7c : bv 32 := 0x00200a13.
Lemma F_77e7c : fetch_word Plain.M.loaded_segments (0x77ed4 : word) = Some W_77e7c.
Proof. vm_refl. Qed.
Lemma D_77e7c : decode_any W_77e7c = Some (OpImm ALU_ADD 20 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77e80 : bv 32 := 0x01496463.
Lemma F_77e80 : fetch_word Plain.M.loaded_segments (0x77ed8 : word) = Some W_77e80.
Proof. vm_refl. Qed.
Lemma D_77e80 : decode_any W_77e80 = Some (Branch BC_LTU 18 20 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77e88 : bv 32 := 0x0004a503.
Lemma F_77e88 : fetch_word Plain.M.loaded_segments (0x77ee0 : word) = Some W_77e88.
Proof. vm_refl. Qed.
Lemma D_77e88 : decode_any W_77e88 = Some (Load SZ4 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77e8c : bv 32 := 0xb09e80ef.
Lemma F_77e8c : fetch_word Plain.M.loaded_segments (0x77ee4 : word) = Some W_77e8c.
Proof. vm_refl. Qed.
Lemma D_77e8c : decode_any W_77e8c = Some (Jal 1 2001672, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77e90 : bv 32 := 0x00050493.
Lemma F_77e90 : fetch_word Plain.M.loaded_segments (0x77ee8 : word) = Some W_77e90.
Proof. vm_refl. Qed.
Lemma D_77e90 : decode_any W_77e90 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77e94 : bv 32 := 0x0d490663.
Lemma F_77e94 : fetch_word Plain.M.loaded_segments (0x77eec : word) = Some W_77e94.
Proof. vm_refl. Qed.
Lemma D_77e94 : decode_any W_77e94 = Some (Branch BC_EQ 18 20 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77e98 : bv 32 := 0x00100a13.
Lemma F_77e98 : fetch_word Plain.M.loaded_segments (0x77ef0 : word) = Some W_77e98.
Proof. vm_refl. Qed.
Lemma D_77e98 : decode_any W_77e98 = Some (OpImm ALU_ADD 20 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77e9c : bv 32 := 0x07490663.
Lemma F_77e9c : fetch_word Plain.M.loaded_segments (0x77ef4 : word) = Some W_77e9c.
Proof. vm_refl. Qed.
Lemma D_77e9c : decode_any W_77e9c = Some (Branch BC_EQ 18 20 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f08 : bv 32 := 0x01c12a83.
Lemma F_77f08 : fetch_word Plain.M.loaded_segments (0x77f60 : word) = Some W_77f08.
Proof. vm_refl. Qed.
Lemma D_77f08 : decode_any W_77f08 = Some (Load SZ4 true 21 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f0c : bv 32 := 0x00098513.
Lemma F_77f0c : fetch_word Plain.M.loaded_segments (0x77f64 : word) = Some W_77f0c.
Proof. vm_refl. Qed.
Lemma D_77f0c : decode_any W_77f0c = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f10 : bv 32 := 0xb54eb0ef.
Lemma F_77f10 : fetch_word Plain.M.loaded_segments (0x77f68 : word) = Some W_77f10.
Proof. vm_refl. Qed.
Lemma D_77f10 : decode_any W_77f10 = Some (Jal 1 2011988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f14 : bv 32 := 0x11451663.
Lemma F_77f14 : fetch_word Plain.M.loaded_segments (0x77f6c : word) = Some W_77f14.
Proof. vm_refl. Qed.
Lemma D_77f14 : decode_any W_77f14 = Some (Branch BC_NE 10 20 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f18 : bv 32 := 0x00810593.
Lemma F_77f18 : fetch_word Plain.M.loaded_segments (0x77f70 : word) = Some W_77f18.
Proof. vm_refl. Qed.
Lemma D_77f18 : decode_any W_77f18 = Some (OpImm ALU_ADD 11 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f1c : bv 32 := 0x02410613.
Lemma F_77f1c : fetch_word Plain.M.loaded_segments (0x77f74 : word) = Some W_77f1c.
Proof. vm_refl. Qed.
Lemma D_77f1c : decode_any W_77f1c = Some (OpImm ALU_ADD 12 2 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f20 : bv 32 := 0x00098513.
Lemma F_77f20 : fetch_word Plain.M.loaded_segments (0x77f78 : word) = Some W_77f20.
Proof. vm_refl. Qed.
Lemma D_77f20 : decode_any W_77f20 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f24 : bv 32 := 0x00000693.
Lemma F_77f24 : fetch_word Plain.M.loaded_segments (0x77f7c : word) = Some W_77f24.
Proof. vm_refl. Qed.
Lemma D_77f24 : decode_any W_77f24 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f28 : bv 32 := 0x991ea0ef.
Lemma F_77f28 : fetch_word Plain.M.loaded_segments (0x77f80 : word) = Some W_77f28.
Proof. vm_refl. Qed.
Lemma D_77f28 : decode_any W_77f28 = Some (Jal 1 2009488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f2c : bv 32 := 0x1b505e63.
Lemma F_77f2c : fetch_word Plain.M.loaded_segments (0x77f84 : word) = Some W_77f2c.
Proof. vm_refl. Qed.
Lemma D_77f2c : decode_any W_77f2c = Some (Branch BC_GE 0 21 444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f30 : bv 32 := 0x00100b13.
Lemma F_77f30 : fetch_word Plain.M.loaded_segments (0x77f88 : word) = Some W_77f30.
Proof. vm_refl. Qed.
Lemma D_77f30 : decode_any W_77f30 = Some (OpImm ALU_ADD 22 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f34 : bv 32 := 0xfffa8a1b.
Lemma F_77f34 : fetch_word Plain.M.loaded_segments (0x77f8c : word) = Some W_77f34.
Proof. vm_refl. Qed.
Lemma D_77f34 : decode_any W_77f34 = Some (OpImm32 20 21 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f38 : bv 32 := 0x02010693.
Lemma F_77f38 : fetch_word Plain.M.loaded_segments (0x77f90 : word) = Some W_77f38.
Proof. vm_refl. Qed.
Lemma D_77f38 : decode_any W_77f38 = Some (OpImm ALU_ADD 13 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f3c : bv 32 := 0x00098513.
Lemma F_77f3c : fetch_word Plain.M.loaded_segments (0x77f94 : word) = Some W_77f3c.
Proof. vm_refl. Qed.
Lemma D_77f3c : decode_any W_77f3c = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f40 : bv 32 := 0x000a0593.
Lemma F_77f40 : fetch_word Plain.M.loaded_segments (0x77f98 : word) = Some W_77f40.
Proof. vm_refl. Qed.
Lemma D_77f40 : decode_any W_77f40 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f44 : bv 32 := 0x00000613.
Lemma F_77f44 : fetch_word Plain.M.loaded_segments (0x77f9c : word) = Some W_77f44.
Proof. vm_refl. Qed.
Lemma D_77f44 : decode_any W_77f44 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f48 : bv 32 := 0xddceb0ef.
Lemma F_77f48 : fetch_word Plain.M.loaded_segments (0x77fa0 : word) = Some W_77f48.
Proof. vm_refl. Qed.
Lemma D_77f48 : decode_any W_77f48 = Some (Jal 1 2012636, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f4c : bv 32 := 0x02012503.
Lemma F_77f4c : fetch_word Plain.M.loaded_segments (0x77fa4 : word) = Some W_77f4c.
Proof. vm_refl. Qed.
Lemma D_77f4c : decode_any W_77f4c = Some (Load SZ4 true 10 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f50 : bv 32 := 0x19650c63.
Lemma F_77f50 : fetch_word Plain.M.loaded_segments (0x77fa8 : word) = Some W_77f50.
Proof. vm_refl. Qed.
Lemma D_77f50 : decode_any W_77f50 = Some (Branch BC_EQ 10 22 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f54 : bv 32 := 0x000a0a93.
Lemma F_77f54 : fetch_word Plain.M.loaded_segments (0x77fac : word) = Some W_77f54.
Proof. vm_refl. Qed.
Lemma D_77f54 : decode_any W_77f54 = Some (OpImm ALU_ADD 21 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f58 : bv 32 := 0xfd404ee3.
Lemma F_77f58 : fetch_word Plain.M.loaded_segments (0x77fb0 : word) = Some W_77f58.
Proof. vm_refl. Qed.
Lemma D_77f58 : decode_any W_77f58 = Some (Branch BC_LT 0 20 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77f5c : bv 32 := 0x1980006f.
Lemma F_77f5c : fetch_word Plain.M.loaded_segments (0x77fb4 : word) = Some W_77f5c.
Proof. vm_refl. Qed.
Lemma D_77f5c : decode_any W_77f5c = Some (Jal 0 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780e8 : bv 32 := 0xfffa8a93.
Lemma F_780e8 : fetch_word Plain.M.loaded_segments (0x78140 : word) = Some W_780e8.
Proof. vm_refl. Qed.
Lemma D_780e8 : decode_any W_780e8 = Some (OpImm ALU_ADD 21 21 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780ec : bv 32 := 0x001a8c1b.
Lemma F_780ec : fetch_word Plain.M.loaded_segments (0x78144 : word) = Some W_780ec.
Proof. vm_refl. Qed.
Lemma D_780ec : decode_any W_780ec = Some (OpImm32 24 21 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780f0 : bv 32 := 0x000c1463.
Lemma F_780f0 : fetch_word Plain.M.loaded_segments (0x78148 : word) = Some W_780f0.
Proof. vm_refl. Qed.
Lemma D_780f0 : decode_any W_780f0 = Some (Branch BC_NE 24 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780f4 : bv 32 := 0x01c12c03.
Lemma F_780f4 : fetch_word Plain.M.loaded_segments (0x7814c : word) = Some W_780f4.
Proof. vm_refl. Qed.
Lemma D_780f4 : decode_any W_780f4 = Some (Load SZ4 true 24 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780f8 : bv 32 := 0xfffc0c1b.
Lemma F_780f8 : fetch_word Plain.M.loaded_segments (0x78150 : word) = Some W_780f8.
Proof. vm_refl. Qed.
Lemma D_780f8 : decode_any W_780f8 = Some (OpImm32 24 24 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_780fc : bv 32 := 0xd00c7553.
Lemma F_780fc : fetch_word Plain.M.loaded_segments (0x78154 : word) = Some W_780fc.
Proof. vm_refl. Qed.
Lemma D_780fc : decode_any W_780fc = Some (Fcvt FC_S FC_W 10 24 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78100 : bv 32 := 0x00048513.
Lemma F_78100 : fetch_word Plain.M.loaded_segments (0x78158 : word) = Some W_78100.
Proof. vm_refl. Qed.
Lemma D_78100 : decode_any W_78100 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78104 : bv 32 := 0xa35e80ef.
Lemma F_78104 : fetch_word Plain.M.loaded_segments (0x7815c : word) = Some W_78104.
Proof. vm_refl. Qed.
Lemma D_78104 : decode_any W_78104 = Some (Jal 1 2001460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78108 : bv 32 := 0x01812503.
Lemma F_78108 : fetch_word Plain.M.loaded_segments (0x78160 : word) = Some W_78108.
Proof. vm_refl. Qed.
Lemma D_78108 : decode_any W_78108 = Some (Load SZ4 true 10 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7810c : bv 32 := 0x00200593.
Lemma F_7810c : fetch_word Plain.M.loaded_segments (0x78164 : word) = Some W_7810c.
Proof. vm_refl. Qed.
Lemma D_7810c : decode_any W_7810c = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78110 : bv 32 := 0x68b54c63.
Lemma F_78110 : fetch_word Plain.M.loaded_segments (0x78168 : word) = Some W_78110.
Proof. vm_refl. Qed.
Lemma D_78110 : decode_any W_78110 = Some (Branch BC_LT 10 11 1688, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78114 : bv 32 := 0x00100d13.
Lemma F_78114 : fetch_word Plain.M.loaded_segments (0x7816c : word) = Some W_78114.
Proof. vm_refl. Qed.
Lemma D_78114 : decode_any W_78114 = Some (OpImm ALU_ADD 26 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78118 : bv 32 := 0x00076517.
Lemma F_78118 : fetch_word Plain.M.loaded_segments (0x78170 : word) = Some W_78118.
Proof. vm_refl. Qed.
Lemma D_78118 : decode_any W_78118 = Some (Auipc 10 118, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7811c : bv 32 := 0x00500d93.
Lemma F_7811c : fetch_word Plain.M.loaded_segments (0x78174 : word) = Some W_7811c.
Proof. vm_refl. Qed.
Lemma D_7811c : decode_any W_7811c = Some (OpImm ALU_ADD 27 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78120 : bv 32 := 0xfffa2597.
Lemma F_78120 : fetch_word Plain.M.loaded_segments (0x78178 : word) = Some W_78120.
Proof. vm_refl. Qed.
Lemma D_78120 : decode_any W_78120 = Some (Auipc 11 1048482, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78124 : bv 32 := 0xfff9c617.
Lemma F_78124 : fetch_word Plain.M.loaded_segments (0x7817c : word) = Some W_78124.
Proof. vm_refl. Qed.
Lemma D_78124 : decode_any W_78124 = Some (Auipc 12 1048476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78128 : bv 32 := 0x40053a83.
Lemma F_78128 : fetch_word Plain.M.loaded_segments (0x78180 : word) = Some W_78128.
Proof. vm_refl. Qed.
Lemma D_78128 : decode_any W_78128 = Some (Load SZ8 true 21 10 1024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7812c : bv 32 := 0xa1e58a13.
Lemma F_7812c : fetch_word Plain.M.loaded_segments (0x78184 : word) = Some W_7812c.
Proof. vm_refl. Qed.
Lemma D_7812c : decode_any W_7812c = Some (OpImm ALU_ADD 20 11 2590, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78130 : bv 32 := 0xf3a60513.
Lemma F_78130 : fetch_word Plain.M.loaded_segments (0x78188 : word) = Some W_78130.
Proof. vm_refl. Qed.
Lemma D_78130 : decode_any W_78130 = Some (OpImm ALU_ADD 10 12 3898, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78134 : bv 32 := 0x00a13023.
Lemma F_78134 : fetch_word Plain.M.loaded_segments (0x7818c : word) = Some W_78134.
Proof. vm_refl. Qed.
Lemma D_78134 : decode_any W_78134 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78138 : bv 32 := 0xfffa3517.
Lemma F_78138 : fetch_word Plain.M.loaded_segments (0x78190 : word) = Some W_78138.
Proof. vm_refl. Qed.
Lemma D_78138 : decode_any W_78138 = Some (Auipc 10 1048483, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7813c : bv 32 := 0xb6250b13.
Lemma F_7813c : fetch_word Plain.M.loaded_segments (0x78194 : word) = Some W_7813c.
Proof. vm_refl. Qed.
Lemma D_7813c : decode_any W_7813c = Some (OpImm ALU_ADD 22 10 2914, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78140 : bv 32 := 0x00100b93.
Lemma F_78140 : fetch_word Plain.M.loaded_segments (0x78198 : word) = Some W_78140.
Proof. vm_refl. Qed.
Lemma D_78140 : decode_any W_78140 = Some (OpImm ALU_ADD 23 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78144 : bv 32 := 0x0240006f.
Lemma F_78144 : fetch_word Plain.M.loaded_segments (0x7819c : word) = Some W_78144.
Proof. vm_refl. Qed.
Lemma D_78144 : decode_any W_78144 = Some (Jal 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78148 : bv 32 := 0x01c12c03.
Lemma F_78148 : fetch_word Plain.M.loaded_segments (0x781a0 : word) = Some W_78148.
Proof. vm_refl. Qed.
Lemma D_78148 : decode_any W_78148 = Some (Load SZ4 true 24 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7814c : bv 32 := 0xfffc0c1b.
Lemma F_7814c : fetch_word Plain.M.loaded_segments (0x781a4 : word) = Some W_7814c.
Proof. vm_refl. Qed.
Lemma D_7814c : decode_any W_7814c = Some (OpImm32 24 24 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78150 : bv 32 := 0xd00c7553.
Lemma F_78150 : fetch_word Plain.M.loaded_segments (0x781a8 : word) = Some W_78150.
Proof. vm_refl. Qed.
Lemma D_78150 : decode_any W_78150 = Some (Fcvt FC_S FC_W 10 24 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78154 : bv 32 := 0x00048513.
Lemma F_78154 : fetch_word Plain.M.loaded_segments (0x781ac : word) = Some W_78154.
Proof. vm_refl. Qed.
Lemma D_78154 : decode_any W_78154 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78158 : bv 32 := 0x9e1e80ef.
Lemma F_78158 : fetch_word Plain.M.loaded_segments (0x781b0 : word) = Some W_78158.
Proof. vm_refl. Qed.
Lemma D_78158 : decode_any W_78158 = Some (Jal 1 2001376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7815c : bv 32 := 0x01812503.
Lemma F_7815c : fetch_word Plain.M.loaded_segments (0x781b4 : word) = Some W_7815c.
Proof. vm_refl. Qed.
Lemma D_7815c : decode_any W_7815c = Some (Load SZ4 true 10 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78160 : bv 32 := 0x001b8b9b.
Lemma F_78160 : fetch_word Plain.M.loaded_segments (0x781b8 : word) = Some W_78160.
Proof. vm_refl. Qed.
Lemma D_78160 : decode_any W_78160 = Some (OpImm32 23 23 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78164 : bv 32 := 0x64abd263.
Lemma F_78164 : fetch_word Plain.M.loaded_segments (0x781bc : word) = Some W_78164.
Proof. vm_refl. Qed.
Lemma D_78164 : decode_any W_78164 = Some (Branch BC_GE 23 10 1604, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78168 : bv 32 := 0x01410693.
Lemma F_78168 : fetch_word Plain.M.loaded_segments (0x781c0 : word) = Some W_78168.
Proof. vm_refl. Qed.
Lemma D_78168 : decode_any W_78168 = Some (OpImm ALU_ADD 13 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7816c : bv 32 := 0x00098513.
Lemma F_7816c : fetch_word Plain.M.loaded_segments (0x781c4 : word) = Some W_7816c.
Proof. vm_refl. Qed.
Lemma D_7816c : decode_any W_7816c = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78170 : bv 32 := 0x000c0593.
Lemma F_78170 : fetch_word Plain.M.loaded_segments (0x781c8 : word) = Some W_78170.
Proof. vm_refl. Qed.
Lemma D_78170 : decode_any W_78170 = Some (OpImm ALU_ADD 11 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78174 : bv 32 := 0x000b8613.
Lemma F_78174 : fetch_word Plain.M.loaded_segments (0x781cc : word) = Some W_78174.
Proof. vm_refl. Qed.
Lemma D_78174 : decode_any W_78174 = Some (OpImm ALU_ADD 12 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78178 : bv 32 := 0xbaceb0ef.
Lemma F_78178 : fetch_word Plain.M.loaded_segments (0x781d0 : word) = Some W_78178.
Proof. vm_refl. Qed.
Lemma D_78178 : decode_any W_78178 = Some (Jal 1 2012076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7817c : bv 32 := 0x01412503.
Lemma F_7817c : fetch_word Plain.M.loaded_segments (0x781d4 : word) = Some W_7817c.
Proof. vm_refl. Qed.
Lemma D_7817c : decode_any W_7817c = Some (Load SZ4 true 10 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78180 : bv 32 := 0x05a51c63.
Lemma F_78180 : fetch_word Plain.M.loaded_segments (0x781d8 : word) = Some W_78180.
Proof. vm_refl. Qed.
Lemma D_78180 : decode_any W_78180 = Some (Branch BC_NE 10 26 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78184 : bv 32 := 0x00098513.
Lemma F_78184 : fetch_word Plain.M.loaded_segments (0x781dc : word) = Some W_78184.
Proof. vm_refl. Qed.
Lemma D_78184 : decode_any W_78184 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78188 : bv 32 := 0x8dceb0ef.
Lemma F_78188 : fetch_word Plain.M.loaded_segments (0x781e0 : word) = Some W_78188.
Proof. vm_refl. Qed.
Lemma D_78188 : decode_any W_78188 = Some (Jal 1 2011356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7818c : bv 32 := 0x09a51e63.
Lemma F_7818c : fetch_word Plain.M.loaded_segments (0x781e4 : word) = Some W_7818c.
Proof. vm_refl. Qed.
Lemma D_7818c : decode_any W_7818c = Some (Branch BC_NE 10 26 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78190 : bv 32 := 0x00810593.
Lemma F_78190 : fetch_word Plain.M.loaded_segments (0x781e8 : word) = Some W_78190.
Proof. vm_refl. Qed.
Lemma D_78190 : decode_any W_78190 = Some (OpImm ALU_ADD 11 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78194 : bv 32 := 0x02410613.
Lemma F_78194 : fetch_word Plain.M.loaded_segments (0x781ec : word) = Some W_78194.
Proof. vm_refl. Qed.
Lemma D_78194 : decode_any W_78194 = Some (OpImm ALU_ADD 12 2 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78198 : bv 32 := 0x00098513.
Lemma F_78198 : fetch_word Plain.M.loaded_segments (0x781f0 : word) = Some W_78198.
Proof. vm_refl. Qed.
Lemma D_78198 : decode_any W_78198 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7819c : bv 32 := 0x00000693.
Lemma F_7819c : fetch_word Plain.M.loaded_segments (0x781f4 : word) = Some W_7819c.
Proof. vm_refl. Qed.
Lemma D_7819c : decode_any W_7819c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781a0 : bv 32 := 0xf18ea0ef.
Lemma F_781a0 : fetch_word Plain.M.loaded_segments (0x781f8 : word) = Some W_781a0.
Proof. vm_refl. Qed.
Lemma D_781a0 : decode_any W_781a0 = Some (Jal 1 2008856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781a4 : bv 32 := 0x00812503.
Lemma F_781a4 : fetch_word Plain.M.loaded_segments (0x781fc : word) = Some W_781a4.
Proof. vm_refl. Qed.
Lemma D_781a4 : decode_any W_781a4 = Some (Load SZ4 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781a8 : bv 32 := 0xfaac52e3.
Lemma F_781a8 : fetch_word Plain.M.loaded_segments (0x78200 : word) = Some W_781a8.
Proof. vm_refl. Qed.
Lemma D_781a8 : decode_any W_781a8 = Some (Branch BC_GE 24 10 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781ac : bv 32 := 0x02010693.
Lemma F_781ac : fetch_word Plain.M.loaded_segments (0x78204 : word) = Some W_781ac.
Proof. vm_refl. Qed.
Lemma D_781ac : decode_any W_781ac = Some (OpImm ALU_ADD 13 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781b0 : bv 32 := 0x00098513.
Lemma F_781b0 : fetch_word Plain.M.loaded_segments (0x78208 : word) = Some W_781b0.
Proof. vm_refl. Qed.
Lemma D_781b0 : decode_any W_781b0 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781b4 : bv 32 := 0x000c0593.
Lemma F_781b4 : fetch_word Plain.M.loaded_segments (0x7820c : word) = Some W_781b4.
Proof. vm_refl. Qed.
Lemma D_781b4 : decode_any W_781b4 = Some (OpImm ALU_ADD 11 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781b8 : bv 32 := 0x000b8613.
Lemma F_781b8 : fetch_word Plain.M.loaded_segments (0x78210 : word) = Some W_781b8.
Proof. vm_refl. Qed.
Lemma D_781b8 : decode_any W_781b8 = Some (OpImm ALU_ADD 12 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781bc : bv 32 := 0xb68eb0ef.
Lemma F_781bc : fetch_word Plain.M.loaded_segments (0x78214 : word) = Some W_781bc.
Proof. vm_refl. Qed.
Lemma D_781bc : decode_any W_781bc = Some (Jal 1 2012008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781c0 : bv 32 := 0x02012503.
Lemma F_781c0 : fetch_word Plain.M.loaded_segments (0x78218 : word) = Some W_781c0.
Proof. vm_refl. Qed.
Lemma D_781c0 : decode_any W_781c0 = Some (Load SZ4 true 10 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781c4 : bv 32 := 0xf80504e3.
Lemma F_781c4 : fetch_word Plain.M.loaded_segments (0x7821c : word) = Some W_781c4.
Proof. vm_refl. Qed.
Lemma D_781c4 : decode_any W_781c4 = Some (Branch BC_EQ 10 0 8072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781c8 : bv 32 := 0x00812503.
Lemma F_781c8 : fetch_word Plain.M.loaded_segments (0x78220 : word) = Some W_781c8.
Proof. vm_refl. Qed.
Lemma D_781c8 : decode_any W_781c8 = Some (Load SZ4 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781cc : bv 32 := 0x001c0c1b.
Lemma F_781cc : fetch_word Plain.M.loaded_segments (0x78224 : word) = Some W_781cc.
Proof. vm_refl. Qed.
Lemma D_781cc : decode_any W_781cc = Some (OpImm32 24 24 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781d0 : bv 32 := 0xfcac4ee3.
Lemma F_781d0 : fetch_word Plain.M.loaded_segments (0x78228 : word) = Some W_781d0.
Proof. vm_refl. Qed.
Lemma D_781d0 : decode_any W_781d0 = Some (Branch BC_LT 24 10 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781d4 : bv 32 := 0xf79ff06f.
Lemma F_781d4 : fetch_word Plain.M.loaded_segments (0x7822c : word) = Some W_781d4.
Proof. vm_refl. Qed.
Lemma D_781d4 : decode_any W_781d4 = Some (Jal 0 2097016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781d8 : bv 32 := 0x00098513.
Lemma F_781d8 : fetch_word Plain.M.loaded_segments (0x78230 : word) = Some W_781d8.
Proof. vm_refl. Qed.
Lemma D_781d8 : decode_any W_781d8 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781dc : bv 32 := 0x888eb0ef.
Lemma F_781dc : fetch_word Plain.M.loaded_segments (0x78234 : word) = Some W_781dc.
Proof. vm_refl. Qed.
Lemma D_781dc : decode_any W_781dc = Some (Jal 1 2011272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781e0 : bv 32 := 0x07a51463.
Lemma F_781e0 : fetch_word Plain.M.loaded_segments (0x78238 : word) = Some W_781e0.
Proof. vm_refl. Qed.
Lemma D_781e0 : decode_any W_781e0 = Some (Branch BC_NE 10 26 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781e4 : bv 32 := 0x00810593.
Lemma F_781e4 : fetch_word Plain.M.loaded_segments (0x7823c : word) = Some W_781e4.
Proof. vm_refl. Qed.
Lemma D_781e4 : decode_any W_781e4 = Some (OpImm ALU_ADD 11 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781e8 : bv 32 := 0x02410613.
Lemma F_781e8 : fetch_word Plain.M.loaded_segments (0x78240 : word) = Some W_781e8.
Proof. vm_refl. Qed.
Lemma D_781e8 : decode_any W_781e8 = Some (OpImm ALU_ADD 12 2 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781ec : bv 32 := 0x00098513.
Lemma F_781ec : fetch_word Plain.M.loaded_segments (0x78244 : word) = Some W_781ec.
Proof. vm_refl. Qed.
Lemma D_781ec : decode_any W_781ec = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781f0 : bv 32 := 0x00000693.
Lemma F_781f0 : fetch_word Plain.M.loaded_segments (0x78248 : word) = Some W_781f0.
Proof. vm_refl. Qed.
Lemma D_781f0 : decode_any W_781f0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781f4 : bv 32 := 0xec4ea0ef.
Lemma F_781f4 : fetch_word Plain.M.loaded_segments (0x7824c : word) = Some W_781f4.
Proof. vm_refl. Qed.
Lemma D_781f4 : decode_any W_781f4 = Some (Jal 1 2008772, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781f8 : bv 32 := 0x060c4c63.
Lemma F_781f8 : fetch_word Plain.M.loaded_segments (0x78250 : word) = Some W_781f8.
Proof. vm_refl. Qed.
Lemma D_781f8 : decode_any W_781f8 = Some (Branch BC_LT 24 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_781fc : bv 32 := 0x000c0c93.
Lemma F_781fc : fetch_word Plain.M.loaded_segments (0x78254 : word) = Some W_781fc.
Proof. vm_refl. Qed.
Lemma D_781fc : decode_any W_781fc = Some (OpImm ALU_ADD 25 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78200 : bv 32 := 0x02010693.
Lemma F_78200 : fetch_word Plain.M.loaded_segments (0x78258 : word) = Some W_78200.
Proof. vm_refl. Qed.
Lemma D_78200 : decode_any W_78200 = Some (OpImm ALU_ADD 13 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78204 : bv 32 := 0x00098513.
Lemma F_78204 : fetch_word Plain.M.loaded_segments (0x7825c : word) = Some W_78204.
Proof. vm_refl. Qed.
Lemma D_78204 : decode_any W_78204 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78208 : bv 32 := 0x000c0593.
Lemma F_78208 : fetch_word Plain.M.loaded_segments (0x78260 : word) = Some W_78208.
Proof. vm_refl. Qed.
Lemma D_78208 : decode_any W_78208 = Some (OpImm ALU_ADD 11 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7820c : bv 32 := 0x000b8613.
Lemma F_7820c : fetch_word Plain.M.loaded_segments (0x78264 : word) = Some W_7820c.
Proof. vm_refl. Qed.
Lemma D_7820c : decode_any W_7820c = Some (OpImm ALU_ADD 12 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78210 : bv 32 := 0xb14eb0ef.
Lemma F_78210 : fetch_word Plain.M.loaded_segments (0x78268 : word) = Some W_78210.
Proof. vm_refl. Qed.
Lemma D_78210 : decode_any W_78210 = Some (Jal 1 2011924, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78214 : bv 32 := 0x02012503.
Lemma F_78214 : fetch_word Plain.M.loaded_segments (0x7826c : word) = Some W_78214.
Proof. vm_refl. Qed.
Lemma D_78214 : decode_any W_78214 = Some (Load SZ4 true 10 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78218 : bv 32 := 0x05a50a63.
Lemma F_78218 : fetch_word Plain.M.loaded_segments (0x78270 : word) = Some W_78218.
Proof. vm_refl. Qed.
Lemma D_78218 : decode_any W_78218 = Some (Branch BC_EQ 10 26 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7821c : bv 32 := 0xfffc8c1b.
Lemma F_7821c : fetch_word Plain.M.loaded_segments (0x78274 : word) = Some W_7821c.
Proof. vm_refl. Qed.
Lemma D_7821c : decode_any W_7821c = Some (OpImm32 24 25 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78220 : bv 32 := 0xfd904ee3.
Lemma F_78220 : fetch_word Plain.M.loaded_segments (0x78278 : word) = Some W_78220.
Proof. vm_refl. Qed.
Lemma D_78220 : decode_any W_78220 = Some (Branch BC_LT 0 25 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78224 : bv 32 := 0xf25ff06f.
Lemma F_78224 : fetch_word Plain.M.loaded_segments (0x7827c : word) = Some W_78224.
Proof. vm_refl. Qed.
Lemma D_78224 : decode_any W_78224 = Some (Jal 0 2096932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7826c : bv 32 := 0x000c8c13.
Lemma F_7826c : fetch_word Plain.M.loaded_segments (0x782c4 : word) = Some W_7826c.
Proof. vm_refl. Qed.
Lemma D_7826c : decode_any W_7826c = Some (OpImm ALU_ADD 24 25 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78270 : bv 32 := 0x001c0c1b.
Lemma F_78270 : fetch_word Plain.M.loaded_segments (0x782c8 : word) = Some W_78270.
Proof. vm_refl. Qed.
Lemma D_78270 : decode_any W_78270 = Some (OpImm32 24 24 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78274 : bv 32 := 0xec0c0ae3.
Lemma F_78274 : fetch_word Plain.M.loaded_segments (0x782cc : word) = Some W_78274.
Proof. vm_refl. Qed.
Lemma D_78274 : decode_any W_78274 = Some (Branch BC_EQ 24 0 7892, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78278 : bv 32 := 0xed5ff06f.
Lemma F_78278 : fetch_word Plain.M.loaded_segments (0x782d0 : word) = Some W_78278.
Proof. vm_refl. Qed.
Lemma D_78278 : decode_any W_78278 = Some (Jal 0 2096852, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_787a8 : bv 32 := 0xe6040e63.
Lemma F_787a8 : fetch_word Plain.M.loaded_segments (0x78800 : word) = Some W_787a8.
Proof. vm_refl. Qed.
Lemma D_787a8 : decode_any W_787a8 = Some (Branch BC_EQ 8 0 5756, 4%Z).
Proof. vm_refl. Qed.

