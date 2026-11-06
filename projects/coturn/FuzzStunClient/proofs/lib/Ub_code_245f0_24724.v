(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.


(* [comment removed for export] *)
Definition W_24628 : bv 32 := 0x00050213.
Lemma F_24628 : fetch_word Ubsan.M.loaded_segments (0x24628 : word) = Some W_24628.
Proof. vm_refl. Qed.
Lemma D_24628 : decode_any W_24628 = Some (OpImm ALU_ADD 4 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2462c : bv 32 := 0x00000513.
Lemma F_2462c : fetch_word Ubsan.M.loaded_segments (0x2462c : word) = Some W_2462c.
Proof. vm_refl. Qed.
Lemma D_2462c : decode_any W_2462c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24630 : bv 32 := 0x00008067.
Lemma F_24630 : fetch_word Ubsan.M.loaded_segments (0x24630 : word) = Some W_24630.
Proof. vm_refl. Qed.
Lemma D_24630 : decode_any W_24630 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24690 : bv 32 := 0xff010113.
Lemma F_24690 : fetch_word Ubsan.M.loaded_segments (0x24690 : word) = Some W_24690.
Proof. vm_refl. Qed.
Lemma D_24690 : decode_any W_24690 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24694 : bv 32 := 0x00113423.
Lemma F_24694 : fetch_word Ubsan.M.loaded_segments (0x24694 : word) = Some W_24694.
Proof. vm_refl. Qed.
Lemma D_24694 : decode_any W_24694 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24698 : bv 32 := 0xe58f90ef.
Lemma F_24698 : fetch_word Ubsan.M.loaded_segments (0x24698 : word) = Some W_24698.
Proof. vm_refl. Qed.
Lemma D_24698 : decode_any W_24698 = Some (Jal 1 2070104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2469c : bv 32 := 0x00050593.
Lemma F_2469c : fetch_word Ubsan.M.loaded_segments (0x2469c : word) = Some W_2469c.
Proof. vm_refl. Qed.
Lemma D_2469c : decode_any W_2469c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_246a0 : bv 32 := 0x03900513.
Lemma F_246a0 : fetch_word Ubsan.M.loaded_segments (0x246a0 : word) = Some W_246a0.
Proof. vm_refl. Qed.
Lemma D_246a0 : decode_any W_246a0 = Some (OpImm ALU_ADD 10 0 57, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_246a4 : bv 32 := 0x00000613.
Lemma F_246a4 : fetch_word Ubsan.M.loaded_segments (0x246a4 : word) = Some W_246a4.
Proof. vm_refl. Qed.
Lemma D_246a4 : decode_any W_246a4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_246a8 : bv 32 := 0x00000693.
Lemma F_246a8 : fetch_word Ubsan.M.loaded_segments (0x246a8 : word) = Some W_246a8.
Proof. vm_refl. Qed.
Lemma D_246a8 : decode_any W_246a8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_246ac : bv 32 := 0x00000713.
Lemma F_246ac : fetch_word Ubsan.M.loaded_segments (0x246ac : word) = Some W_246ac.
Proof. vm_refl. Qed.
Lemma D_246ac : decode_any W_246ac = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_246b0 : bv 32 := 0x00000793.
Lemma F_246b0 : fetch_word Ubsan.M.loaded_segments (0x246b0 : word) = Some W_246b0.
Proof. vm_refl. Qed.
Lemma D_246b0 : decode_any W_246b0 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_246b4 : bv 32 := 0x00000813.
Lemma F_246b4 : fetch_word Ubsan.M.loaded_segments (0x246b4 : word) = Some W_246b4.
Proof. vm_refl. Qed.
Lemma D_246b4 : decode_any W_246b4 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_246b8 : bv 32 := 0xe91ff0ef.
Lemma F_246b8 : fetch_word Ubsan.M.loaded_segments (0x246b8 : word) = Some W_246b8.
Proof. vm_refl. Qed.
Lemma D_246b8 : decode_any W_246b8 = Some (Jal 1 2096784, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_246bc : bv 32 := 0x0005051b.
Lemma F_246bc : fetch_word Ubsan.M.loaded_segments (0x246bc : word) = Some W_246bc.
Proof. vm_refl. Qed.
Lemma D_246bc : decode_any W_246bc = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_246c0 : bv 32 := 0x00450593.
Lemma F_246c0 : fetch_word Ubsan.M.loaded_segments (0x246c0 : word) = Some W_246c0.
Proof. vm_refl. Qed.
Lemma D_246c0 : decode_any W_246c0 = Some (OpImm ALU_ADD 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_246c4 : bv 32 := 0x0015b593.
Lemma F_246c4 : fetch_word Ubsan.M.loaded_segments (0x246c4 : word) = Some W_246c4.
Proof. vm_refl. Qed.
Lemma D_246c4 : decode_any W_246c4 = Some (OpImm ALU_SLTU 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_246c8 : bv 32 := 0xfff58593.
Lemma F_246c8 : fetch_word Ubsan.M.loaded_segments (0x246c8 : word) = Some W_246c8.
Proof. vm_refl. Qed.
Lemma D_246c8 : decode_any W_246c8 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_246cc : bv 32 := 0x00a5f533.
Lemma F_246cc : fetch_word Ubsan.M.loaded_segments (0x246cc : word) = Some W_246cc.
Proof. vm_refl. Qed.
Lemma D_246cc : decode_any W_246cc = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_246d0 : bv 32 := 0xa29f70ef.
Lemma F_246d0 : fetch_word Ubsan.M.loaded_segments (0x246d0 : word) = Some W_246d0.
Proof. vm_refl. Qed.
Lemma D_246d0 : decode_any W_246d0 = Some (Jal 1 2062888, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_246d4 : bv 32 := 0x0005051b.
Lemma F_246d4 : fetch_word Ubsan.M.loaded_segments (0x246d4 : word) = Some W_246d4.
Proof. vm_refl. Qed.
Lemma D_246d4 : decode_any W_246d4 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_246d8 : bv 32 := 0x00813083.
Lemma F_246d8 : fetch_word Ubsan.M.loaded_segments (0x246d8 : word) = Some W_246d8.
Proof. vm_refl. Qed.
Lemma D_246d8 : decode_any W_246d8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_246dc : bv 32 := 0x01010113.
Lemma F_246dc : fetch_word Ubsan.M.loaded_segments (0x246dc : word) = Some W_246dc.
Proof. vm_refl. Qed.
Lemma D_246dc : decode_any W_246dc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_246e0 : bv 32 := 0x00008067.
Lemma F_246e0 : fetch_word Ubsan.M.loaded_segments (0x246e0 : word) = Some W_246e0.
Proof. vm_refl. Qed.
Lemma D_246e0 : decode_any W_246e0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_246f0 : bv 32 := 0xff010113.
Lemma F_246f0 : fetch_word Ubsan.M.loaded_segments (0x246f0 : word) = Some W_246f0.
Proof. vm_refl. Qed.
Lemma D_246f0 : decode_any W_246f0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_246f4 : bv 32 := 0x00113423.
Lemma F_246f4 : fetch_word Ubsan.M.loaded_segments (0x246f4 : word) = Some W_246f4.
Proof. vm_refl. Qed.
Lemma D_246f4 : decode_any W_246f4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_246f8 : bv 32 := 0x00060693.
Lemma F_246f8 : fetch_word Ubsan.M.loaded_segments (0x246f8 : word) = Some W_246f8.
Proof. vm_refl. Qed.
Lemma D_246f8 : decode_any W_246f8 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_246fc : bv 32 := 0x00058613.
Lemma F_246fc : fetch_word Ubsan.M.loaded_segments (0x246fc : word) = Some W_246fc.
Proof. vm_refl. Qed.
Lemma D_246fc : decode_any W_246fc = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24700 : bv 32 := 0x00050593.
Lemma F_24700 : fetch_word Ubsan.M.loaded_segments (0x24700 : word) = Some W_24700.
Proof. vm_refl. Qed.
Lemma D_24700 : decode_any W_24700 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24704 : bv 32 := 0x03f00513.
Lemma F_24704 : fetch_word Ubsan.M.loaded_segments (0x24704 : word) = Some W_24704.
Proof. vm_refl. Qed.
Lemma D_24704 : decode_any W_24704 = Some (OpImm ALU_ADD 10 0 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24708 : bv 32 := 0x00000713.
Lemma F_24708 : fetch_word Ubsan.M.loaded_segments (0x24708 : word) = Some W_24708.
Proof. vm_refl. Qed.
Lemma D_24708 : decode_any W_24708 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2470c : bv 32 := 0x00000793.
Lemma F_2470c : fetch_word Ubsan.M.loaded_segments (0x2470c : word) = Some W_2470c.
Proof. vm_refl. Qed.
Lemma D_2470c : decode_any W_2470c = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24710 : bv 32 := 0x00000813.
Lemma F_24710 : fetch_word Ubsan.M.loaded_segments (0x24710 : word) = Some W_24710.
Proof. vm_refl. Qed.
Lemma D_24710 : decode_any W_24710 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24714 : bv 32 := 0xe35ff0ef.
Lemma F_24714 : fetch_word Ubsan.M.loaded_segments (0x24714 : word) = Some W_24714.
Proof. vm_refl. Qed.
Lemma D_24714 : decode_any W_24714 = Some (Jal 1 2096692, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24718 : bv 32 := 0x00813083.
Lemma F_24718 : fetch_word Ubsan.M.loaded_segments (0x24718 : word) = Some W_24718.
Proof. vm_refl. Qed.
Lemma D_24718 : decode_any W_24718 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2471c : bv 32 := 0x01010113.
Lemma F_2471c : fetch_word Ubsan.M.loaded_segments (0x2471c : word) = Some W_2471c.
Proof. vm_refl. Qed.
Lemma D_2471c : decode_any W_2471c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24720 : bv 32 := 0x9d9f706f.
Lemma F_24720 : fetch_word Ubsan.M.loaded_segments (0x24720 : word) = Some W_24720.
Proof. vm_refl. Qed.
Lemma D_24720 : decode_any W_24720 = Some (Jal 0 2062808, 4%Z).
Proof. vm_refl. Qed.
