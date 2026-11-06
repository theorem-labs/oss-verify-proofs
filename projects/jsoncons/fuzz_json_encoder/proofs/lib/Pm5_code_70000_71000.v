(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_702e4 : bv 32 := 0x104240ef.
Lemma F_702e4 : fetch_word AsanUbsan.M.loaded_segments (0x7032c : word) = Some W_702e4.
Proof. vm_refl. Qed.
Lemma D_702e4 : decode_any W_702e4 = Some (Jal 1 147716, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_702e8 : bv 32 := 0x00150b93.
Lemma F_702e8 : fetch_word AsanUbsan.M.loaded_segments (0x70330 : word) = Some W_702e8.
Proof. vm_refl. Qed.
Lemma D_702e8 : decode_any W_702e8 = Some (OpImm ALU_ADD 23 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_702ec : bv 32 := 0xfffb4513.
Lemma F_702ec : fetch_word AsanUbsan.M.loaded_segments (0x70334 : word) = Some W_702ec.
Proof. vm_refl. Qed.
Lemma D_702ec : decode_any W_702ec = Some (OpImm ALU_XOR 10 22 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_702f0 : bv 32 := 0x25756e63.
Lemma F_702f0 : fetch_word AsanUbsan.M.loaded_segments (0x70338 : word) = Some W_702f0.
Proof. vm_refl. Qed.
Lemma D_702f0 : decode_any W_702f0 = Some (Branch BC_LTU 10 23 604, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_702f4 : bv 32 := 0xfbfb8513.
Lemma F_702f4 : fetch_word AsanUbsan.M.loaded_segments (0x7033c : word) = Some W_702f4.
Proof. vm_refl. Qed.
Lemma D_702f4 : decode_any W_702f4 = Some (OpImm ALU_ADD 10 23 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_702f8 : bv 32 := 0xfbf00593.
Lemma F_702f8 : fetch_word AsanUbsan.M.loaded_segments (0x70340 : word) = Some W_702f8.
Proof. vm_refl. Qed.
Lemma D_702f8 : decode_any W_702f8 = Some (OpImm ALU_ADD 11 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_702fc : bv 32 := 0x2ca5f063.
Lemma F_702fc : fetch_word AsanUbsan.M.loaded_segments (0x70344 : word) = Some W_702fc.
Proof. vm_refl. Qed.
Lemma D_702fc : decode_any W_702fc = Some (Branch BC_GEU 11 10 704, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70300 : bv 32 := 0x000f4517.
Lemma F_70300 : fetch_word AsanUbsan.M.loaded_segments (0x70348 : word) = Some W_70300.
Proof. vm_refl. Qed.
Lemma D_70300 : decode_any W_70300 = Some (Auipc 10 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70304 : bv 32 := 0x1d053503.
Lemma F_70304 : fetch_word AsanUbsan.M.loaded_segments (0x7034c : word) = Some W_70304.
Proof. vm_refl. Qed.
Lemma D_70304 : decode_any W_70304 = Some (Load SZ8 true 10 10 464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70308 : bv 32 := 0x017b0633.
Lemma F_70308 : fetch_word AsanUbsan.M.loaded_segments (0x70350 : word) = Some W_70308.
Proof. vm_refl. Qed.
Lemma D_70308 : decode_any W_70308 = Some (Op ALU_ADD 12 22 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7030c : bv 32 := 0x00053583.
Lemma F_7030c : fetch_word AsanUbsan.M.loaded_segments (0x70354 : word) = Some W_7030c.
Proof. vm_refl. Qed.
Lemma D_7030c : decode_any W_7030c = Some (Load SZ8 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70310 : bv 32 := 0x003b5513.
Lemma F_70310 : fetch_word AsanUbsan.M.loaded_segments (0x70358 : word) = Some W_70310.
Proof. vm_refl. Qed.
Lemma D_70310 : decode_any W_70310 = Some (ShiftImm ALU_SRL 10 22 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70314 : bv 32 := 0xfff60613.
Lemma F_70314 : fetch_word AsanUbsan.M.loaded_segments (0x7035c : word) = Some W_70314.
Proof. vm_refl. Qed.
Lemma D_70314 : decode_any W_70314 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70318 : bv 32 := 0x00365693.
Lemma F_70318 : fetch_word AsanUbsan.M.loaded_segments (0x70360 : word) = Some W_70318.
Proof. vm_refl. Qed.
Lemma D_70318 : decode_any W_70318 = Some (ShiftImm ALU_SRL 13 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7031c : bv 32 := 0x00a58533.
Lemma F_7031c : fetch_word AsanUbsan.M.loaded_segments (0x70364 : word) = Some W_7031c.
Proof. vm_refl. Qed.
Lemma D_7031c : decode_any W_7031c = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70320 : bv 32 := 0x00d585b3.
Lemma F_70320 : fetch_word AsanUbsan.M.loaded_segments (0x70368 : word) = Some W_70320.
Proof. vm_refl. Qed.
Lemma D_70320 : decode_any W_70320 = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70324 : bv 32 := 0xff857693.
Lemma F_70324 : fetch_word AsanUbsan.M.loaded_segments (0x7036c : word) = Some W_70324.
Proof. vm_refl. Qed.
Lemma D_70324 : decode_any W_70324 = Some (OpImm ALU_AND 13 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70328 : bv 32 := 0xff85f713.
Lemma F_70328 : fetch_word AsanUbsan.M.loaded_segments (0x70370 : word) = Some W_70328.
Proof. vm_refl. Qed.
Lemma D_70328 : decode_any W_70328 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7032c : bv 32 := 0x0006b683.
Lemma F_7032c : fetch_word AsanUbsan.M.loaded_segments (0x70374 : word) = Some W_7032c.
Proof. vm_refl. Qed.
Lemma D_7032c : decode_any W_7032c = Some (Load SZ8 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70330 : bv 32 := 0x00073703.
Lemma F_70330 : fetch_word AsanUbsan.M.loaded_segments (0x70378 : word) = Some W_70330.
Proof. vm_refl. Qed.
Lemma D_70330 : decode_any W_70330 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70334 : bv 32 := 0x00d766b3.
Lemma F_70334 : fetch_word AsanUbsan.M.loaded_segments (0x7037c : word) = Some W_70334.
Proof. vm_refl. Qed.
Lemma D_70334 : decode_any W_70334 = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70338 : bv 32 := 0xf00688e3.
Lemma F_70338 : fetch_word AsanUbsan.M.loaded_segments (0x70380 : word) = Some W_70338.
Proof. vm_refl. Qed.
Lemma D_70338 : decode_any W_70338 = Some (Branch BC_EQ 13 0 7952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70370 : bv 32 := 0x000b0513.
Lemma F_70370 : fetch_word AsanUbsan.M.loaded_segments (0x703b8 : word) = Some W_70370.
Proof. vm_refl. Qed.
Lemma D_70370 : decode_any W_70370 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70374 : bv 32 := 0x000b8593.
Lemma F_70374 : fetch_word AsanUbsan.M.loaded_segments (0x703bc : word) = Some W_70374.
Proof. vm_refl. Qed.
Lemma D_70374 : decode_any W_70374 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70378 : bv 32 := 0x77d130ef.
Lemma F_70378 : fetch_word AsanUbsan.M.loaded_segments (0x703c0 : word) = Some W_70378.
Proof. vm_refl. Qed.
Lemma D_70378 : decode_any W_70378 = Some (Jal 1 81788, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7037c : bv 32 := 0xec0506e3.
Lemma F_7037c : fetch_word AsanUbsan.M.loaded_segments (0x703c4 : word) = Some W_7037c.
Proof. vm_refl. Qed.
Lemma D_7037c : decode_any W_7037c = Some (Branch BC_EQ 10 0 7884, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_705bc : bv 32 := 0xda0b9ae3.
Lemma F_705bc : fetch_word AsanUbsan.M.loaded_segments (0x70604 : word) = Some W_705bc.
Proof. vm_refl. Qed.
Lemma D_705bc : decode_any W_705bc = Some (Branch BC_NE 23 0 7604, 4%Z).
Proof. vm_refl. Qed.

