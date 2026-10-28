(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushU23.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_730dc : bv 32 := 0xfe010113.
Lemma F_730dc : fetch_word Ubsan.M.loaded_segments (0x730dc : word) = Some W_730dc.
Proof. vm_refl. Qed.
Lemma D_730dc : decode_any W_730dc = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_730e0 : bv 32 := 0x00113c23.
Lemma F_730e0 : fetch_word Ubsan.M.loaded_segments (0x730e0 : word) = Some W_730e0.
Proof. vm_refl. Qed.
Lemma D_730e0 : decode_any W_730e0 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_730e4 : bv 32 := 0x00813823.
Lemma F_730e4 : fetch_word Ubsan.M.loaded_segments (0x730e4 : word) = Some W_730e4.
Proof. vm_refl. Qed.
Lemma D_730e4 : decode_any W_730e4 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_730e8 : bv 32 := 0x00913423.
Lemma F_730e8 : fetch_word Ubsan.M.loaded_segments (0x730e8 : word) = Some W_730e8.
Proof. vm_refl. Qed.
Lemma D_730e8 : decode_any W_730e8 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_730ec : bv 32 := 0x06050c63.
Lemma F_730ec : fetch_word Ubsan.M.loaded_segments (0x730ec : word) = Some W_730ec.
Proof. vm_refl. Qed.
Lemma D_730ec : decode_any W_730ec = Some (Branch BC_EQ 10 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_730f0 : bv 32 := 0x00050413.
Lemma F_730f0 : fetch_word Ubsan.M.loaded_segments (0x730f0 : word) = Some W_730f0.
Proof. vm_refl. Qed.
Lemma D_730f0 : decode_any W_730f0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_730f4 : bv 32 := 0x00410613.
Lemma F_730f4 : fetch_word Ubsan.M.loaded_segments (0x730f4 : word) = Some W_730f4.
Proof. vm_refl. Qed.
Lemma D_730f4 : decode_any W_730f4 = Some (OpImm ALU_ADD 12 2 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_730f8 : bv 32 := 0x00000593.
Lemma F_730f8 : fetch_word Ubsan.M.loaded_segments (0x730f8 : word) = Some W_730f8.
Proof. vm_refl. Qed.
Lemma D_730f8 : decode_any W_730f8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_730fc : bv 32 := 0x0f8000ef.
Lemma F_730fc : fetch_word Ubsan.M.loaded_segments (0x730fc : word) = Some W_730fc.
Proof. vm_refl. Qed.
Lemma D_730fc : decode_any W_730fc = Some (Jal 1 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_73100 : bv 32 := 0x00412503.
Lemma F_73100 : fetch_word Ubsan.M.loaded_segments (0x73100 : word) = Some W_73100.
Proof. vm_refl. Qed.
Lemma D_73100 : decode_any W_73100 = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_73104 : bv 32 := 0x08050e63.
Lemma F_73104 : fetch_word Ubsan.M.loaded_segments (0x73104 : word) = Some W_73104.
Proof. vm_refl. Qed.
Lemma D_73104 : decode_any W_73104 = Some (Branch BC_EQ 10 0 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_73108 : bv 32 := 0x00100513.
Lemma F_73108 : fetch_word Ubsan.M.loaded_segments (0x73108 : word) = Some W_73108.
Proof. vm_refl. Qed.
Lemma D_73108 : decode_any W_73108 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7310c : bv 32 := 0x01800593.
Lemma F_7310c : fetch_word Ubsan.M.loaded_segments (0x7310c : word) = Some W_7310c.
Proof. vm_refl. Qed.
Lemma D_7310c : decode_any W_7310c = Some (OpImm ALU_ADD 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_73110 : bv 32 := 0x5d09b0ef.
Lemma F_73110 : fetch_word Ubsan.M.loaded_segments (0x73110 : word) = Some W_73110.
Proof. vm_refl. Qed.
Lemma D_73110 : decode_any W_73110 = Some (Jal 1 636368, 4%Z).
Proof. vm_refl. Qed.

Definition W_73114 : bv 32 := 0x00747593.
Lemma F_73114 : fetch_word Ubsan.M.loaded_segments (0x73114 : word) = Some W_73114.
Proof. vm_refl. Qed.
Lemma D_73114 : decode_any W_73114 = Some (OpImm ALU_AND 11 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_73118 : bv 32 := 0x0c059c63.
Lemma F_73118 : fetch_word Ubsan.M.loaded_segments (0x73118 : word) = Some W_73118.
Proof. vm_refl. Qed.
Lemma D_73118 : decode_any W_73118 = Some (Branch BC_NE 11 0 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_7311c : bv 32 := 0x00050493.
Lemma F_7311c : fetch_word Ubsan.M.loaded_segments (0x7311c : word) = Some W_7311c.
Proof. vm_refl. Qed.
Lemma D_7311c : decode_any W_7311c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73120 : bv 32 := 0x00c42503.
Lemma F_73120 : fetch_word Ubsan.M.loaded_segments (0x73120 : word) = Some W_73120.
Proof. vm_refl. Qed.
Lemma D_73120 : decode_any W_73120 = Some (Load SZ4 true 10 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_73124 : bv 32 := 0x0025159b.
Lemma F_73124 : fetch_word Ubsan.M.loaded_segments (0x73124 : word) = Some W_73124.
Proof. vm_refl. Qed.
Lemma D_73124 : decode_any W_73124 = Some (ShiftImm32 ALU_SLL 11 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_73128 : bv 32 := 0x00100513.
Lemma F_73128 : fetch_word Ubsan.M.loaded_segments (0x73128 : word) = Some W_73128.
Proof. vm_refl. Qed.
Lemma D_73128 : decode_any W_73128 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7312c : bv 32 := 0x5b49b0ef.
Lemma F_7312c : fetch_word Ubsan.M.loaded_segments (0x7312c : word) = Some W_7312c.
Proof. vm_refl. Qed.
Lemma D_7312c : decode_any W_7312c = Some (Jal 1 636340, 4%Z).
Proof. vm_refl. Qed.

Definition W_73130 : bv 32 := 0x0c048063.
Lemma F_73130 : fetch_word Ubsan.M.loaded_segments (0x73130 : word) = Some W_73130.
Proof. vm_refl. Qed.
Lemma D_73130 : decode_any W_73130 = Some (Branch BC_EQ 9 0 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_73134 : bv 32 := 0x0074f593.
Lemma F_73134 : fetch_word Ubsan.M.loaded_segments (0x73134 : word) = Some W_73134.
Proof. vm_refl. Qed.
Lemma D_73134 : decode_any W_73134 = Some (OpImm ALU_AND 11 9 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_73138 : bv 32 := 0x0a059c63.
Lemma F_73138 : fetch_word Ubsan.M.loaded_segments (0x73138 : word) = Some W_73138.
Proof. vm_refl. Qed.
Lemma D_73138 : decode_any W_73138 = Some (Branch BC_NE 11 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_7313c : bv 32 := 0x00a4b023.
Lemma F_7313c : fetch_word Ubsan.M.loaded_segments (0x7313c : word) = Some W_7313c.
Proof. vm_refl. Qed.
Lemma D_7313c : decode_any W_7313c = Some (Store SZ8 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73140 : bv 32 := 0x01042603.
Lemma F_73140 : fetch_word Ubsan.M.loaded_segments (0x73140 : word) = Some W_73140.
Proof. vm_refl. Qed.
Lemma D_73140 : decode_any W_73140 = Some (Load SZ4 true 12 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_73144 : bv 32 := 0x00043583.
Lemma F_73144 : fetch_word Ubsan.M.loaded_segments (0x73144 : word) = Some W_73144.
Proof. vm_refl. Qed.
Lemma D_73144 : decode_any W_73144 = Some (Load SZ8 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73148 : bv 32 := 0x00261613.
Lemma F_73148 : fetch_word Ubsan.M.loaded_segments (0x73148 : word) = Some W_73148.
Proof. vm_refl. Qed.
Lemma D_73148 : decode_any W_73148 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7314c : bv 32 := 0x008ab0ef.
Lemma F_7314c : fetch_word Ubsan.M.loaded_segments (0x7314c : word) = Some W_7314c.
Proof. vm_refl. Qed.
Lemma D_7314c : decode_any W_7314c = Some (Jal 1 700424, 4%Z).
Proof. vm_refl. Qed.

Definition W_73150 : bv 32 := 0x01042503.
Lemma F_73150 : fetch_word Ubsan.M.loaded_segments (0x73150 : word) = Some W_73150.
Proof. vm_refl. Qed.
Lemma D_73150 : decode_any W_73150 = Some (Load SZ4 true 10 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_73154 : bv 32 := 0x00a4a823.
Lemma F_73154 : fetch_word Ubsan.M.loaded_segments (0x73154 : word) = Some W_73154.
Proof. vm_refl. Qed.
Lemma D_73154 : decode_any W_73154 = Some (Store SZ4 9 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_73158 : bv 32 := 0x00843503.
Lemma F_73158 : fetch_word Ubsan.M.loaded_segments (0x73158 : word) = Some W_73158.
Proof. vm_refl. Qed.
Lemma D_73158 : decode_any W_73158 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7315c : bv 32 := 0x00a4b423.
Lemma F_7315c : fetch_word Ubsan.M.loaded_segments (0x7315c : word) = Some W_7315c.
Proof. vm_refl. Qed.
Lemma D_7315c : decode_any W_7315c = Some (Store SZ8 9 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_73160 : bv 32 := 0x0780006f.
Lemma F_73160 : fetch_word Ubsan.M.loaded_segments (0x73160 : word) = Some W_73160.
Proof. vm_refl. Qed.
Lemma D_73160 : decode_any W_73160 = Some (Jal 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_731d8 : bv 32 := 0x00048513.
Lemma F_731d8 : fetch_word Ubsan.M.loaded_segments (0x731d8 : word) = Some W_731d8.
Proof. vm_refl. Qed.
Lemma D_731d8 : decode_any W_731d8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_731dc : bv 32 := 0x01813083.
Lemma F_731dc : fetch_word Ubsan.M.loaded_segments (0x731dc : word) = Some W_731dc.
Proof. vm_refl. Qed.
Lemma D_731dc : decode_any W_731dc = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_731e0 : bv 32 := 0x01013403.
Lemma F_731e0 : fetch_word Ubsan.M.loaded_segments (0x731e0 : word) = Some W_731e0.
Proof. vm_refl. Qed.
Lemma D_731e0 : decode_any W_731e0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_731e4 : bv 32 := 0x00813483.
Lemma F_731e4 : fetch_word Ubsan.M.loaded_segments (0x731e4 : word) = Some W_731e4.
Proof. vm_refl. Qed.
Lemma D_731e4 : decode_any W_731e4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_731e8 : bv 32 := 0x02010113.
Lemma F_731e8 : fetch_word Ubsan.M.loaded_segments (0x731e8 : word) = Some W_731e8.
Proof. vm_refl. Qed.
Lemma D_731e8 : decode_any W_731e8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_731ec : bv 32 := 0x00008067.
Lemma F_731ec : fetch_word Ubsan.M.loaded_segments (0x731ec : word) = Some W_731ec.
Proof. vm_refl. Qed.
Lemma D_731ec : decode_any W_731ec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
