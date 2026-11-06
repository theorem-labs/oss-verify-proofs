(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgU.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_32a5c : bv 32 := 0x00091517.
Lemma F_32a5c : fetch_word ImgU.M.loaded_segments (0x32a5c : word) = Some W_32a5c.
Proof. vm_refl. Qed.
Lemma D_32a5c : decode_any W_32a5c = Some (Auipc 10 145, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32a60 : bv 32 := 0xb9854503.
Lemma F_32a60 : fetch_word ImgU.M.loaded_segments (0x32a60 : word) = Some W_32a60.
Proof. vm_refl. Qed.
Lemma D_32a60 : decode_any W_32a60 = Some (Load SZ1 false 10 10 2968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32a64 : bv 32 := 0x00051463.
Lemma F_32a64 : fetch_word ImgU.M.loaded_segments (0x32a64 : word) = Some W_32a64.
Proof. vm_refl. Qed.
Lemma D_32a64 : decode_any W_32a64 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32a68 : bv 32 := 0x00008067.
Lemma F_32a68 : fetch_word ImgU.M.loaded_segments (0x32a68 : word) = Some W_32a68.
Proof. vm_refl. Qed.
Lemma D_32a68 : decode_any W_32a68 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96514 : bv 32 := 0x00892583.
Lemma F_96514 : fetch_word ImgU.M.loaded_segments (0x96514 : word) = Some W_96514.
Proof. vm_refl. Qed.
Lemma D_96514 : decode_any W_96514 = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96518 : bv 32 := 0x0180006f.
Lemma F_96518 : fetch_word ImgU.M.loaded_segments (0x96518 : word) = Some W_96518.
Proof. vm_refl. Qed.
Lemma D_96518 : decode_any W_96518 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9651c : bv 32 := 0x00053503.
Lemma F_9651c : fetch_word ImgU.M.loaded_segments (0x9651c : word) = Some W_9651c.
Proof. vm_refl. Qed.
Lemma D_9651c : decode_any W_9651c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96520 : bv 32 := 0x02000593.
Lemma F_96520 : fetch_word ImgU.M.loaded_segments (0x96520 : word) = Some W_96520.
Proof. vm_refl. Qed.
Lemma D_96520 : decode_any W_96520 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96524 : bv 32 := 0x00b92423.
Lemma F_96524 : fetch_word ImgU.M.loaded_segments (0x96524 : word) = Some W_96524.
Proof. vm_refl. Qed.
Lemma D_96524 : decode_any W_96524 = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96528 : bv 32 := 0x00a93823.
Lemma F_96528 : fetch_word ImgU.M.loaded_segments (0x96528 : word) = Some W_96528.
Proof. vm_refl. Qed.
Lemma D_96528 : decode_any W_96528 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9652c : bv 32 := 0x04050a63.
Lemma F_9652c : fetch_word ImgU.M.loaded_segments (0x9652c : word) = Some W_9652c.
Proof. vm_refl. Qed.
Lemma D_9652c : decode_any W_9652c = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96530 : bv 32 := 0xfff5861b.
Lemma F_96530 : fetch_word ImgU.M.loaded_segments (0x96530 : word) = Some W_96530.
Proof. vm_refl. Qed.
Lemma D_96530 : decode_any W_96530 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96534 : bv 32 := 0x00c92423.
Lemma F_96534 : fetch_word ImgU.M.loaded_segments (0x96534 : word) = Some W_96534.
Proof. vm_refl. Qed.
Lemma D_96534 : decode_any W_96534 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96538 : bv 32 := 0xfeb052e3.
Lemma F_96538 : fetch_word ImgU.M.loaded_segments (0x96538 : word) = Some W_96538.
Proof. vm_refl. Qed.
Lemma D_96538 : decode_any W_96538 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9653c : bv 32 := 0x01093503.
Lemma F_9653c : fetch_word ImgU.M.loaded_segments (0x9653c : word) = Some W_9653c.
Proof. vm_refl. Qed.
Lemma D_9653c : decode_any W_9653c = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96540 : bv 32 := 0x00361613.
Lemma F_96540 : fetch_word ImgU.M.loaded_segments (0x96540 : word) = Some W_96540.
Proof. vm_refl. Qed.
Lemma D_96540 : decode_any W_96540 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96544 : bv 32 := 0x00c50533.
Lemma F_96544 : fetch_word ImgU.M.loaded_segments (0x96544 : word) = Some W_96544.
Proof. vm_refl. Qed.
Lemma D_96544 : decode_any W_96544 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96548 : bv 32 := 0x00853983.
Lemma F_96548 : fetch_word ImgU.M.loaded_segments (0x96548 : word) = Some W_96548.
Proof. vm_refl. Qed.
Lemma D_96548 : decode_any W_96548 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9654c : bv 32 := 0x10853483.
Lemma F_9654c : fetch_word ImgU.M.loaded_segments (0x9654c : word) = Some W_9654c.
Proof. vm_refl. Qed.
Lemma D_9654c : decode_any W_9654c = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96550 : bv 32 := 0x00040513.
Lemma F_96550 : fetch_word ImgU.M.loaded_segments (0x96550 : word) = Some W_96550.
Proof. vm_refl. Qed.
Lemma D_96550 : decode_any W_96550 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96554 : bv 32 := 0x74c110ef.
Lemma F_96554 : fetch_word ImgU.M.loaded_segments (0x96554 : word) = Some W_96554.
Proof. vm_refl. Qed.
Lemma D_96554 : decode_any W_96554 = Some (Jal 1 71500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96558 : bv 32 := 0x00048513.
Lemma F_96558 : fetch_word ImgU.M.loaded_segments (0x96558 : word) = Some W_96558.
Proof. vm_refl. Qed.
Lemma D_96558 : decode_any W_96558 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9655c : bv 32 := 0x000980e7.
Lemma F_9655c : fetch_word ImgU.M.loaded_segments (0x9655c : word) = Some W_9655c.
Proof. vm_refl. Qed.
Lemma D_9655c : decode_any W_9655c = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96560 : bv 32 := 0x00040513.
Lemma F_96560 : fetch_word ImgU.M.loaded_segments (0x96560 : word) = Some W_96560.
Proof. vm_refl. Qed.
Lemma D_96560 : decode_any W_96560 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96564 : bv 32 := 0x4b4110ef.
Lemma F_96564 : fetch_word ImgU.M.loaded_segments (0x96564 : word) = Some W_96564.
Proof. vm_refl. Qed.
Lemma D_96564 : decode_any W_96564 = Some (Jal 1 70836, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96568 : bv 32 := 0x00892503.
Lemma F_96568 : fetch_word ImgU.M.loaded_segments (0x96568 : word) = Some W_96568.
Proof. vm_refl. Qed.
Lemma D_96568 : decode_any W_96568 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9656c : bv 32 := 0xfff5061b.
Lemma F_9656c : fetch_word ImgU.M.loaded_segments (0x9656c : word) = Some W_9656c.
Proof. vm_refl. Qed.
Lemma D_9656c : decode_any W_9656c = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96570 : bv 32 := 0x00c92423.
Lemma F_96570 : fetch_word ImgU.M.loaded_segments (0x96570 : word) = Some W_96570.
Proof. vm_refl. Qed.
Lemma D_96570 : decode_any W_96570 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96574 : bv 32 := 0xfca044e3.
Lemma F_96574 : fetch_word ImgU.M.loaded_segments (0x96574 : word) = Some W_96574.
Proof. vm_refl. Qed.
Lemma D_96574 : decode_any W_96574 = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96578 : bv 32 := 0x01093503.
Lemma F_96578 : fetch_word ImgU.M.loaded_segments (0x96578 : word) = Some W_96578.
Proof. vm_refl. Qed.
Lemma D_96578 : decode_any W_96578 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9657c : bv 32 := 0xfa1ff06f.
Lemma F_9657c : fetch_word ImgU.M.loaded_segments (0x9657c : word) = Some W_9657c.
Proof. vm_refl. Qed.
Lemma D_9657c : decode_any W_9657c = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96738 : bv 32 := 0x00050067.
Lemma F_96738 : fetch_word ImgU.M.loaded_segments (0x96738 : word) = Some W_96738.
Proof. vm_refl. Qed.
Lemma D_96738 : decode_any W_96738 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.
