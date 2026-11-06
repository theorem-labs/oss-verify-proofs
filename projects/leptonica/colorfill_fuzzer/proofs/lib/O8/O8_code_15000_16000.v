(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.H Require GcFlushS8.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.colorfill_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_151b0 : bv 32 := 0xfe010113.
Lemma F_151b0 : fetch_word Plain.M.loaded_segments (0x152b4 : word) = Some W_151b0.
Proof. vm_refl. Qed.
Lemma D_151b0 : decode_any W_151b0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151b4 : bv 32 := 0x00113c23.
Lemma F_151b4 : fetch_word Plain.M.loaded_segments (0x152b8 : word) = Some W_151b4.
Proof. vm_refl. Qed.
Lemma D_151b4 : decode_any W_151b4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151b8 : bv 32 := 0x00813823.
Lemma F_151b8 : fetch_word Plain.M.loaded_segments (0x152bc : word) = Some W_151b8.
Proof. vm_refl. Qed.
Lemma D_151b8 : decode_any W_151b8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151bc : bv 32 := 0x00913423.
Lemma F_151bc : fetch_word Plain.M.loaded_segments (0x152c0 : word) = Some W_151bc.
Proof. vm_refl. Qed.
Lemma D_151bc : decode_any W_151bc = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151c0 : bv 32 := 0x06050863.
Lemma F_151c0 : fetch_word Plain.M.loaded_segments (0x152c4 : word) = Some W_151c0.
Proof. vm_refl. Qed.
Lemma D_151c0 : decode_any W_151c0 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151c4 : bv 32 := 0x00053403.
Lemma F_151c4 : fetch_word Plain.M.loaded_segments (0x152c8 : word) = Some W_151c4.
Proof. vm_refl. Qed.
Lemma D_151c4 : decode_any W_151c4 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151c8 : bv 32 := 0x0a040063.
Lemma F_151c8 : fetch_word Plain.M.loaded_segments (0x152cc : word) = Some W_151c8.
Proof. vm_refl. Qed.
Lemma D_151c8 : decode_any W_151c8 = Some (Branch BC_EQ 8 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151cc : bv 32 := 0x01440593.
Lemma F_151cc : fetch_word Plain.M.loaded_segments (0x152d0 : word) = Some W_151cc.
Proof. vm_refl. Qed.
Lemma D_151cc : decode_any W_151cc = Some (OpImm ALU_ADD 11 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151d0 : bv 32 := 0xfff00613.
Lemma F_151d0 : fetch_word Plain.M.loaded_segments (0x152d4 : word) = Some W_151d0.
Proof. vm_refl. Qed.
Lemma D_151d0 : decode_any W_151d0 = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151d4 : bv 32 := 0x06c5a5af.
Lemma F_151d4 : fetch_word Plain.M.loaded_segments (0x152d8 : word) = Some W_151d4.
Proof. vm_refl. Qed.
Lemma D_151d4 : decode_any W_151d4 = Some (Amo AMO_ADD AW true true 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151d8 : bv 32 := 0x00100613.
Lemma F_151d8 : fetch_word Plain.M.loaded_segments (0x152dc : word) = Some W_151d8.
Proof. vm_refl. Qed.
Lemma D_151d8 : decode_any W_151d8 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151dc : bv 32 := 0x04c59663.
Lemma F_151dc : fetch_word Plain.M.loaded_segments (0x152e0 : word) = Some W_151dc.
Proof. vm_refl. Qed.
Lemma D_151dc : decode_any W_151dc = Some (Branch BC_NE 11 12 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15228 : bv 32 := 0x00053023.
Lemma F_15228 : fetch_word Plain.M.loaded_segments (0x1532c : word) = Some W_15228.
Proof. vm_refl. Qed.
Lemma D_15228 : decode_any W_15228 = Some (Store SZ8 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1522c : bv 32 := 0x03c0006f.
Lemma F_1522c : fetch_word Plain.M.loaded_segments (0x15330 : word) = Some W_1522c.
Proof. vm_refl. Qed.
Lemma D_1522c : decode_any W_1522c = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15268 : bv 32 := 0x01813083.
Lemma F_15268 : fetch_word Plain.M.loaded_segments (0x1536c : word) = Some W_15268.
Proof. vm_refl. Qed.
Lemma D_15268 : decode_any W_15268 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1526c : bv 32 := 0x01013403.
Lemma F_1526c : fetch_word Plain.M.loaded_segments (0x15370 : word) = Some W_1526c.
Proof. vm_refl. Qed.
Lemma D_1526c : decode_any W_1526c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15270 : bv 32 := 0x00813483.
Lemma F_15270 : fetch_word Plain.M.loaded_segments (0x15374 : word) = Some W_15270.
Proof. vm_refl. Qed.
Lemma D_15270 : decode_any W_15270 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15274 : bv 32 := 0x02010113.
Lemma F_15274 : fetch_word Plain.M.loaded_segments (0x15378 : word) = Some W_15274.
Proof. vm_refl. Qed.
Lemma D_15274 : decode_any W_15274 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15278 : bv 32 := 0x00008067.
Lemma F_15278 : fetch_word Plain.M.loaded_segments (0x1537c : word) = Some W_15278.
Proof. vm_refl. Qed.
Lemma D_15278 : decode_any W_15278 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1527c : bv 32 := 0x00058463.
Lemma F_1527c : fetch_word Plain.M.loaded_segments (0x15380 : word) = Some W_1527c.
Proof. vm_refl. Qed.
Lemma D_1527c : decode_any W_1527c = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15280 : bv 32 := 0x0005a023.
Lemma F_15280 : fetch_word Plain.M.loaded_segments (0x15384 : word) = Some W_15280.
Proof. vm_refl. Qed.
Lemma D_15280 : decode_any W_15280 = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15284 : bv 32 := 0x00060463.
Lemma F_15284 : fetch_word Plain.M.loaded_segments (0x15388 : word) = Some W_15284.
Proof. vm_refl. Qed.
Lemma D_15284 : decode_any W_15284 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15288 : bv 32 := 0x00062023.
Lemma F_15288 : fetch_word Plain.M.loaded_segments (0x1538c : word) = Some W_15288.
Proof. vm_refl. Qed.
Lemma D_15288 : decode_any W_15288 = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1528c : bv 32 := 0x00068463.
Lemma F_1528c : fetch_word Plain.M.loaded_segments (0x15390 : word) = Some W_1528c.
Proof. vm_refl. Qed.
Lemma D_1528c : decode_any W_1528c = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15294 : bv 32 := 0x02050a63.
Lemma F_15294 : fetch_word Plain.M.loaded_segments (0x15398 : word) = Some W_15294.
Proof. vm_refl. Qed.
Lemma D_15294 : decode_any W_15294 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15298 : bv 32 := 0x00058663.
Lemma F_15298 : fetch_word Plain.M.loaded_segments (0x1539c : word) = Some W_15298.
Proof. vm_refl. Qed.
Lemma D_15298 : decode_any W_15298 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1529c : bv 32 := 0x00052703.
Lemma F_1529c : fetch_word Plain.M.loaded_segments (0x153a0 : word) = Some W_1529c.
Proof. vm_refl. Qed.
Lemma D_1529c : decode_any W_1529c = Some (Load SZ4 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a0 : bv 32 := 0x00e5a023.
Lemma F_152a0 : fetch_word Plain.M.loaded_segments (0x153a4 : word) = Some W_152a0.
Proof. vm_refl. Qed.
Lemma D_152a0 : decode_any W_152a0 = Some (Store SZ4 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a4 : bv 32 := 0x00060663.
Lemma F_152a4 : fetch_word Plain.M.loaded_segments (0x153a8 : word) = Some W_152a4.
Proof. vm_refl. Qed.
Lemma D_152a4 : decode_any W_152a4 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a8 : bv 32 := 0x00452583.
Lemma F_152a8 : fetch_word Plain.M.loaded_segments (0x153ac : word) = Some W_152a8.
Proof. vm_refl. Qed.
Lemma D_152a8 : decode_any W_152a8 = Some (Load SZ4 true 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ac : bv 32 := 0x00b62023.
Lemma F_152ac : fetch_word Plain.M.loaded_segments (0x153b0 : word) = Some W_152ac.
Proof. vm_refl. Qed.
Lemma D_152ac : decode_any W_152ac = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b0 : bv 32 := 0x00000593.
Lemma F_152b0 : fetch_word Plain.M.loaded_segments (0x153b4 : word) = Some W_152b0.
Proof. vm_refl. Qed.
Lemma D_152b0 : decode_any W_152b0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b4 : bv 32 := 0x00068663.
Lemma F_152b4 : fetch_word Plain.M.loaded_segments (0x153b8 : word) = Some W_152b4.
Proof. vm_refl. Qed.
Lemma D_152b4 : decode_any W_152b4 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c0 : bv 32 := 0x00058513.
Lemma F_152c0 : fetch_word Plain.M.loaded_segments (0x153c4 : word) = Some W_152c0.
Proof. vm_refl. Qed.
Lemma D_152c0 : decode_any W_152c0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c4 : bv 32 := 0x00008067.
Lemma F_152c4 : fetch_word Plain.M.loaded_segments (0x153c8 : word) = Some W_152c4.
Proof. vm_refl. Qed.
Lemma D_152c4 : decode_any W_152c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153e0 : bv 32 := 0x00050a63.
Lemma F_153e0 : fetch_word Plain.M.loaded_segments (0x154e4 : word) = Some W_153e0.
Proof. vm_refl. Qed.
Lemma D_153e0 : decode_any W_153e0 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153e4 : bv 32 := 0x01450593.
Lemma F_153e4 : fetch_word Plain.M.loaded_segments (0x154e8 : word) = Some W_153e4.
Proof. vm_refl. Qed.
Lemma D_153e4 : decode_any W_153e4 = Some (OpImm ALU_ADD 11 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153e8 : bv 32 := 0x00100613.
Lemma F_153e8 : fetch_word Plain.M.loaded_segments (0x154ec : word) = Some W_153e8.
Proof. vm_refl. Qed.
Lemma D_153e8 : decode_any W_153e8 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153ec : bv 32 := 0x06c5a02f.
Lemma F_153ec : fetch_word Plain.M.loaded_segments (0x154f0 : word) = Some W_153ec.
Proof. vm_refl. Qed.
Lemma D_153ec : decode_any W_153ec = Some (Amo AMO_ADD AW true true 0 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153f0 : bv 32 := 0x00008067.
Lemma F_153f0 : fetch_word Plain.M.loaded_segments (0x154f4 : word) = Some W_153f0.
Proof. vm_refl. Qed.
Lemma D_153f0 : decode_any W_153f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15468 : bv 32 := 0x00050663.
Lemma F_15468 : fetch_word Plain.M.loaded_segments (0x1556c : word) = Some W_15468.
Proof. vm_refl. Qed.
Lemma D_15468 : decode_any W_15468 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1546c : bv 32 := 0x00852503.
Lemma F_1546c : fetch_word Plain.M.loaded_segments (0x15570 : word) = Some W_1546c.
Proof. vm_refl. Qed.
Lemma D_1546c : decode_any W_1546c = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15470 : bv 32 := 0x00008067.
Lemma F_15470 : fetch_word Plain.M.loaded_segments (0x15574 : word) = Some W_15470.
Proof. vm_refl. Qed.
Lemma D_15470 : decode_any W_15470 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
