(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation BSEGS_I := ImgB.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_891f0 : bv 32 := 0x00155593.
Lemma F_891f0 : fetch_word BSEGS_I (0x891f0 : word) = Some W_891f0.
Proof. vm_refl. Qed.
Lemma D_891f0 : decode_any W_891f0 = Some (ShiftImm ALU_SRL 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_891f4 : bv 32 := 0x55555637.
Lemma F_891f4 : fetch_word BSEGS_I (0x891f4 : word) = Some W_891f4.
Proof. vm_refl. Qed.
Lemma D_891f4 : decode_any W_891f4 = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_891f8 : bv 32 := 0x333336b7.
Lemma F_891f8 : fetch_word BSEGS_I (0x891f8 : word) = Some W_891f8.
Proof. vm_refl. Qed.
Lemma D_891f8 : decode_any W_891f8 = Some (Lui 13 209715, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_891fc : bv 32 := 0x0f0f1737.
Lemma F_891fc : fetch_word BSEGS_I (0x891fc : word) = Some W_891fc.
Proof. vm_refl. Qed.
Lemma D_891fc : decode_any W_891fc = Some (Lui 14 61681, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89200 : bv 32 := 0x010107b7.
Lemma F_89200 : fetch_word BSEGS_I (0x89200 : word) = Some W_89200.
Proof. vm_refl. Qed.
Lemma D_89200 : decode_any W_89200 = Some (Lui 15 4112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89204 : bv 32 := 0x00b56533.
Lemma F_89204 : fetch_word BSEGS_I (0x89204 : word) = Some W_89204.
Proof. vm_refl. Qed.
Lemma D_89204 : decode_any W_89204 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89208 : bv 32 := 0x5556059b.
Lemma F_89208 : fetch_word BSEGS_I (0x89208 : word) = Some W_89208.
Proof. vm_refl. Qed.
Lemma D_89208 : decode_any W_89208 = Some (OpImm32 11 12 1365, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8920c : bv 32 := 0x3336861b.
Lemma F_8920c : fetch_word BSEGS_I (0x8920c : word) = Some W_8920c.
Proof. vm_refl. Qed.
Lemma D_8920c : decode_any W_8920c = Some (OpImm32 12 13 819, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89210 : bv 32 := 0xf0f7069b.
Lemma F_89210 : fetch_word BSEGS_I (0x89210 : word) = Some W_89210.
Proof. vm_refl. Qed.
Lemma D_89210 : decode_any W_89210 = Some (OpImm32 13 14 3855, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89214 : bv 32 := 0x1017871b.
Lemma F_89214 : fetch_word BSEGS_I (0x89214 : word) = Some W_89214.
Proof. vm_refl. Qed.
Lemma D_89214 : decode_any W_89214 = Some (OpImm32 14 15 257, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89218 : bv 32 := 0x00255793.
Lemma F_89218 : fetch_word BSEGS_I (0x89218 : word) = Some W_89218.
Proof. vm_refl. Qed.
Lemma D_89218 : decode_any W_89218 = Some (ShiftImm ALU_SRL 15 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8921c : bv 32 := 0x00f56533.
Lemma F_8921c : fetch_word BSEGS_I (0x8921c : word) = Some W_8921c.
Proof. vm_refl. Qed.
Lemma D_8921c : decode_any W_8921c = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89220 : bv 32 := 0x02059793.
Lemma F_89220 : fetch_word BSEGS_I (0x89220 : word) = Some W_89220.
Proof. vm_refl. Qed.
Lemma D_89220 : decode_any W_89220 = Some (ShiftImm ALU_SLL 15 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89224 : bv 32 := 0x00f585b3.
Lemma F_89224 : fetch_word BSEGS_I (0x89224 : word) = Some W_89224.
Proof. vm_refl. Qed.
Lemma D_89224 : decode_any W_89224 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89228 : bv 32 := 0x02061793.
Lemma F_89228 : fetch_word BSEGS_I (0x89228 : word) = Some W_89228.
Proof. vm_refl. Qed.
Lemma D_89228 : decode_any W_89228 = Some (ShiftImm ALU_SLL 15 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8922c : bv 32 := 0x00f60633.
Lemma F_8922c : fetch_word BSEGS_I (0x8922c : word) = Some W_8922c.
Proof. vm_refl. Qed.
Lemma D_8922c : decode_any W_8922c = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89230 : bv 32 := 0x02069793.
Lemma F_89230 : fetch_word BSEGS_I (0x89230 : word) = Some W_89230.
Proof. vm_refl. Qed.
Lemma D_89230 : decode_any W_89230 = Some (ShiftImm ALU_SLL 15 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89234 : bv 32 := 0x00f686b3.
Lemma F_89234 : fetch_word BSEGS_I (0x89234 : word) = Some W_89234.
Proof. vm_refl. Qed.
Lemma D_89234 : decode_any W_89234 = Some (Op ALU_ADD 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89238 : bv 32 := 0x02071793.
Lemma F_89238 : fetch_word BSEGS_I (0x89238 : word) = Some W_89238.
Proof. vm_refl. Qed.
Lemma D_89238 : decode_any W_89238 = Some (ShiftImm ALU_SLL 15 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8923c : bv 32 := 0x00f70733.
Lemma F_8923c : fetch_word BSEGS_I (0x8923c : word) = Some W_8923c.
Proof. vm_refl. Qed.
Lemma D_8923c : decode_any W_8923c = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89240 : bv 32 := 0x00455793.
Lemma F_89240 : fetch_word BSEGS_I (0x89240 : word) = Some W_89240.
Proof. vm_refl. Qed.
Lemma D_89240 : decode_any W_89240 = Some (ShiftImm ALU_SRL 15 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89244 : bv 32 := 0x00f56533.
Lemma F_89244 : fetch_word BSEGS_I (0x89244 : word) = Some W_89244.
Proof. vm_refl. Qed.
Lemma D_89244 : decode_any W_89244 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89248 : bv 32 := 0x00855793.
Lemma F_89248 : fetch_word BSEGS_I (0x89248 : word) = Some W_89248.
Proof. vm_refl. Qed.
Lemma D_89248 : decode_any W_89248 = Some (ShiftImm ALU_SRL 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8924c : bv 32 := 0x00f56533.
Lemma F_8924c : fetch_word BSEGS_I (0x8924c : word) = Some W_8924c.
Proof. vm_refl. Qed.
Lemma D_8924c : decode_any W_8924c = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89250 : bv 32 := 0x01055793.
Lemma F_89250 : fetch_word BSEGS_I (0x89250 : word) = Some W_89250.
Proof. vm_refl. Qed.
Lemma D_89250 : decode_any W_89250 = Some (ShiftImm ALU_SRL 15 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89254 : bv 32 := 0x00f56533.
Lemma F_89254 : fetch_word BSEGS_I (0x89254 : word) = Some W_89254.
Proof. vm_refl. Qed.
Lemma D_89254 : decode_any W_89254 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89258 : bv 32 := 0x02055793.
Lemma F_89258 : fetch_word BSEGS_I (0x89258 : word) = Some W_89258.
Proof. vm_refl. Qed.
Lemma D_89258 : decode_any W_89258 = Some (ShiftImm ALU_SRL 15 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8925c : bv 32 := 0x00f56533.
Lemma F_8925c : fetch_word BSEGS_I (0x8925c : word) = Some W_8925c.
Proof. vm_refl. Qed.
Lemma D_8925c : decode_any W_8925c = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89260 : bv 32 := 0xfff54513.
Lemma F_89260 : fetch_word BSEGS_I (0x89260 : word) = Some W_89260.
Proof. vm_refl. Qed.
Lemma D_89260 : decode_any W_89260 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.
