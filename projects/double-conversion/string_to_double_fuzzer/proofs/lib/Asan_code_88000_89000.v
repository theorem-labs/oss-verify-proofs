(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation ASEGS_I := ImgA.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_890ac : bv 32 := 0x00155593.
Lemma F_890ac : fetch_word ASEGS_I (0x890ac : word) = Some W_890ac.
Proof. vm_refl. Qed.
Lemma D_890ac : decode_any W_890ac = Some (ShiftImm ALU_SRL 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_890b0 : bv 32 := 0x55555637.
Lemma F_890b0 : fetch_word ASEGS_I (0x890b0 : word) = Some W_890b0.
Proof. vm_refl. Qed.
Lemma D_890b0 : decode_any W_890b0 = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_890b4 : bv 32 := 0x333336b7.
Lemma F_890b4 : fetch_word ASEGS_I (0x890b4 : word) = Some W_890b4.
Proof. vm_refl. Qed.
Lemma D_890b4 : decode_any W_890b4 = Some (Lui 13 209715, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_890b8 : bv 32 := 0x0f0f1737.
Lemma F_890b8 : fetch_word ASEGS_I (0x890b8 : word) = Some W_890b8.
Proof. vm_refl. Qed.
Lemma D_890b8 : decode_any W_890b8 = Some (Lui 14 61681, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_890bc : bv 32 := 0x010107b7.
Lemma F_890bc : fetch_word ASEGS_I (0x890bc : word) = Some W_890bc.
Proof. vm_refl. Qed.
Lemma D_890bc : decode_any W_890bc = Some (Lui 15 4112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_890c0 : bv 32 := 0x00b56533.
Lemma F_890c0 : fetch_word ASEGS_I (0x890c0 : word) = Some W_890c0.
Proof. vm_refl. Qed.
Lemma D_890c0 : decode_any W_890c0 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_890c4 : bv 32 := 0x5556059b.
Lemma F_890c4 : fetch_word ASEGS_I (0x890c4 : word) = Some W_890c4.
Proof. vm_refl. Qed.
Lemma D_890c4 : decode_any W_890c4 = Some (OpImm32 11 12 1365, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_890c8 : bv 32 := 0x3336861b.
Lemma F_890c8 : fetch_word ASEGS_I (0x890c8 : word) = Some W_890c8.
Proof. vm_refl. Qed.
Lemma D_890c8 : decode_any W_890c8 = Some (OpImm32 12 13 819, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_890cc : bv 32 := 0xf0f7069b.
Lemma F_890cc : fetch_word ASEGS_I (0x890cc : word) = Some W_890cc.
Proof. vm_refl. Qed.
Lemma D_890cc : decode_any W_890cc = Some (OpImm32 13 14 3855, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_890d0 : bv 32 := 0x1017871b.
Lemma F_890d0 : fetch_word ASEGS_I (0x890d0 : word) = Some W_890d0.
Proof. vm_refl. Qed.
Lemma D_890d0 : decode_any W_890d0 = Some (OpImm32 14 15 257, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_890d4 : bv 32 := 0x00255793.
Lemma F_890d4 : fetch_word ASEGS_I (0x890d4 : word) = Some W_890d4.
Proof. vm_refl. Qed.
Lemma D_890d4 : decode_any W_890d4 = Some (ShiftImm ALU_SRL 15 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_890d8 : bv 32 := 0x00f56533.
Lemma F_890d8 : fetch_word ASEGS_I (0x890d8 : word) = Some W_890d8.
Proof. vm_refl. Qed.
Lemma D_890d8 : decode_any W_890d8 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_890dc : bv 32 := 0x02059793.
Lemma F_890dc : fetch_word ASEGS_I (0x890dc : word) = Some W_890dc.
Proof. vm_refl. Qed.
Lemma D_890dc : decode_any W_890dc = Some (ShiftImm ALU_SLL 15 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_890e0 : bv 32 := 0x00f585b3.
Lemma F_890e0 : fetch_word ASEGS_I (0x890e0 : word) = Some W_890e0.
Proof. vm_refl. Qed.
Lemma D_890e0 : decode_any W_890e0 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_890e4 : bv 32 := 0x02061793.
Lemma F_890e4 : fetch_word ASEGS_I (0x890e4 : word) = Some W_890e4.
Proof. vm_refl. Qed.
Lemma D_890e4 : decode_any W_890e4 = Some (ShiftImm ALU_SLL 15 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_890e8 : bv 32 := 0x00f60633.
Lemma F_890e8 : fetch_word ASEGS_I (0x890e8 : word) = Some W_890e8.
Proof. vm_refl. Qed.
Lemma D_890e8 : decode_any W_890e8 = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_890ec : bv 32 := 0x02069793.
Lemma F_890ec : fetch_word ASEGS_I (0x890ec : word) = Some W_890ec.
Proof. vm_refl. Qed.
Lemma D_890ec : decode_any W_890ec = Some (ShiftImm ALU_SLL 15 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_890f0 : bv 32 := 0x00f686b3.
Lemma F_890f0 : fetch_word ASEGS_I (0x890f0 : word) = Some W_890f0.
Proof. vm_refl. Qed.
Lemma D_890f0 : decode_any W_890f0 = Some (Op ALU_ADD 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_890f4 : bv 32 := 0x02071793.
Lemma F_890f4 : fetch_word ASEGS_I (0x890f4 : word) = Some W_890f4.
Proof. vm_refl. Qed.
Lemma D_890f4 : decode_any W_890f4 = Some (ShiftImm ALU_SLL 15 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_890f8 : bv 32 := 0x00f70733.
Lemma F_890f8 : fetch_word ASEGS_I (0x890f8 : word) = Some W_890f8.
Proof. vm_refl. Qed.
Lemma D_890f8 : decode_any W_890f8 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_890fc : bv 32 := 0x00455793.
Lemma F_890fc : fetch_word ASEGS_I (0x890fc : word) = Some W_890fc.
Proof. vm_refl. Qed.
Lemma D_890fc : decode_any W_890fc = Some (ShiftImm ALU_SRL 15 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89100 : bv 32 := 0x00f56533.
Lemma F_89100 : fetch_word ASEGS_I (0x89100 : word) = Some W_89100.
Proof. vm_refl. Qed.
Lemma D_89100 : decode_any W_89100 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89104 : bv 32 := 0x00855793.
Lemma F_89104 : fetch_word ASEGS_I (0x89104 : word) = Some W_89104.
Proof. vm_refl. Qed.
Lemma D_89104 : decode_any W_89104 = Some (ShiftImm ALU_SRL 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89108 : bv 32 := 0x00f56533.
Lemma F_89108 : fetch_word ASEGS_I (0x89108 : word) = Some W_89108.
Proof. vm_refl. Qed.
Lemma D_89108 : decode_any W_89108 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8910c : bv 32 := 0x01055793.
Lemma F_8910c : fetch_word ASEGS_I (0x8910c : word) = Some W_8910c.
Proof. vm_refl. Qed.
Lemma D_8910c : decode_any W_8910c = Some (ShiftImm ALU_SRL 15 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89110 : bv 32 := 0x00f56533.
Lemma F_89110 : fetch_word ASEGS_I (0x89110 : word) = Some W_89110.
Proof. vm_refl. Qed.
Lemma D_89110 : decode_any W_89110 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89114 : bv 32 := 0x02055793.
Lemma F_89114 : fetch_word ASEGS_I (0x89114 : word) = Some W_89114.
Proof. vm_refl. Qed.
Lemma D_89114 : decode_any W_89114 = Some (ShiftImm ALU_SRL 15 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89118 : bv 32 := 0x00f56533.
Lemma F_89118 : fetch_word ASEGS_I (0x89118 : word) = Some W_89118.
Proof. vm_refl. Qed.
Lemma D_89118 : decode_any W_89118 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8911c : bv 32 := 0xfff54513.
Lemma F_8911c : fetch_word ASEGS_I (0x8911c : word) = Some W_8911c.
Proof. vm_refl. Qed.
Lemma D_8911c : decode_any W_8911c = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.
