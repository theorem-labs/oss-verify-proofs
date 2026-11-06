(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_26e688 : bv 32 := 0x00008067.
Lemma F_26e688 : fetch_word Plain.M.loaded_segments (0x26e6d0 : word) = Some W_26e688.
Proof. vm_refl. Qed.
Lemma D_26e688 : decode_any W_26e688 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e68c : bv 32 := 0xe8010113.
Lemma F_26e68c : fetch_word Plain.M.loaded_segments (0x26e6d4 : word) = Some W_26e68c.
Proof. vm_refl. Qed.
Lemma D_26e68c : decode_any W_26e68c = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e690 : bv 32 := 0x16113c23.
Lemma F_26e690 : fetch_word Plain.M.loaded_segments (0x26e6d8 : word) = Some W_26e690.
Proof. vm_refl. Qed.
Lemma D_26e690 : decode_any W_26e690 = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e694 : bv 32 := 0x16813823.
Lemma F_26e694 : fetch_word Plain.M.loaded_segments (0x26e6dc : word) = Some W_26e694.
Proof. vm_refl. Qed.
Lemma D_26e694 : decode_any W_26e694 = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e698 : bv 32 := 0x16913423.
Lemma F_26e698 : fetch_word Plain.M.loaded_segments (0x26e6e0 : word) = Some W_26e698.
Proof. vm_refl. Qed.
Lemma D_26e698 : decode_any W_26e698 = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e69c : bv 32 := 0x17213023.
Lemma F_26e69c : fetch_word Plain.M.loaded_segments (0x26e6e4 : word) = Some W_26e69c.
Proof. vm_refl. Qed.
Lemma D_26e69c : decode_any W_26e69c = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6a0 : bv 32 := 0x00058413.
Lemma F_26e6a0 : fetch_word Plain.M.loaded_segments (0x26e6e8 : word) = Some W_26e6a0.
Proof. vm_refl. Qed.
Lemma D_26e6a0 : decode_any W_26e6a0 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6a4 : bv 32 := 0x00050493.
Lemma F_26e6a4 : fetch_word Plain.M.loaded_segments (0x26e6ec : word) = Some W_26e6a4.
Proof. vm_refl. Qed.
Lemma D_26e6a4 : decode_any W_26e6a4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6a8 : bv 32 := 0x03010513.
Lemma F_26e6a8 : fetch_word Plain.M.loaded_segments (0x26e6f0 : word) = Some W_26e6a8.
Proof. vm_refl. Qed.
Lemma D_26e6a8 : decode_any W_26e6a8 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6ac : bv 32 := 0x13000613.
Lemma F_26e6ac : fetch_word Plain.M.loaded_segments (0x26e6f4 : word) = Some W_26e6ac.
Proof. vm_refl. Qed.
Lemma D_26e6ac : decode_any W_26e6ac = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6b0 : bv 32 := 0x00000593.
Lemma F_26e6b0 : fetch_word Plain.M.loaded_segments (0x26e6f8 : word) = Some W_26e6b0.
Proof. vm_refl. Qed.
Lemma D_26e6b0 : decode_any W_26e6b0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6b4 : bv 32 := 0x7400b0ef.
Lemma F_26e6b4 : fetch_word Plain.M.loaded_segments (0x26e6fc : word) = Some W_26e6b4.
Proof. vm_refl. Qed.
Lemma D_26e6b4 : decode_any W_26e6b4 = Some (Jal 1 46912, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6b8 : bv 32 := 0x0006d517.
Lemma F_26e6b8 : fetch_word Plain.M.loaded_segments (0x26e700 : word) = Some W_26e6b8.
Proof. vm_refl. Qed.
Lemma D_26e6b8 : decode_any W_26e6b8 = Some (Auipc 10 109, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6bc : bv 32 := 0xa2853503.
Lemma F_26e6bc : fetch_word Plain.M.loaded_segments (0x26e704 : word) = Some W_26e6bc.
Proof. vm_refl. Qed.
Lemma D_26e6bc : decode_any W_26e6bc = Some (Load SZ8 true 10 10 2600, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6c0 : bv 32 := 0x00953023.
Lemma F_26e6c0 : fetch_word Plain.M.loaded_segments (0x26e708 : word) = Some W_26e6c0.
Proof. vm_refl. Qed.
Lemma D_26e6c0 : decode_any W_26e6c0 = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6c4 : bv 32 := 0x0004b503.
Lemma F_26e6c4 : fetch_word Plain.M.loaded_segments (0x26e70c : word) = Some W_26e6c4.
Proof. vm_refl. Qed.
Lemma D_26e6c4 : decode_any W_26e6c4 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6c8 : bv 32 := 0x00848493.
Lemma F_26e6c8 : fetch_word Plain.M.loaded_segments (0x26e710 : word) = Some W_26e6c8.
Proof. vm_refl. Qed.
Lemma D_26e6c8 : decode_any W_26e6c8 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6cc : bv 32 := 0xfe051ce3.
Lemma F_26e6cc : fetch_word Plain.M.loaded_segments (0x26e714 : word) = Some W_26e6cc.
Proof. vm_refl. Qed.
Lemma D_26e6cc : decode_any W_26e6cc = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6d0 : bv 32 := 0x000a1517.
Lemma F_26e6d0 : fetch_word Plain.M.loaded_segments (0x26e718 : word) = Some W_26e6d0.
Proof. vm_refl. Qed.
Lemma D_26e6d0 : decode_any W_26e6d0 = Some (Auipc 10 161, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6d4 : bv 32 := 0xff050913.
Lemma F_26e6d4 : fetch_word Plain.M.loaded_segments (0x26e71c : word) = Some W_26e6d4.
Proof. vm_refl. Qed.
Lemma D_26e6d4 : decode_any W_26e6d4 = Some (OpImm ALU_ADD 18 10 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6d8 : bv 32 := 0x00993423.
Lemma F_26e6d8 : fetch_word Plain.M.loaded_segments (0x26e720 : word) = Some W_26e6d8.
Proof. vm_refl. Qed.
Lemma D_26e6d8 : decode_any W_26e6d8 = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6dc : bv 32 := 0x0004b583.
Lemma F_26e6dc : fetch_word Plain.M.loaded_segments (0x26e724 : word) = Some W_26e6dc.
Proof. vm_refl. Qed.
Lemma D_26e6dc : decode_any W_26e6dc = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6e0 : bv 32 := 0x04058c63.
Lemma F_26e6e0 : fetch_word Plain.M.loaded_segments (0x26e728 : word) = Some W_26e6e0.
Proof. vm_refl. Qed.
Lemma D_26e6e0 : decode_any W_26e6e0 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6e4 : bv 32 := 0x01048493.
Lemma F_26e6e4 : fetch_word Plain.M.loaded_segments (0x26e72c : word) = Some W_26e6e4.
Proof. vm_refl. Qed.
Lemma D_26e6e4 : decode_any W_26e6e4 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6e8 : bv 32 := 0x02500513.
Lemma F_26e6e8 : fetch_word Plain.M.loaded_segments (0x26e730 : word) = Some W_26e6e8.
Proof. vm_refl. Qed.
Lemma D_26e6e8 : decode_any W_26e6e8 = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6ec : bv 32 := 0x03010613.
Lemma F_26e6ec : fetch_word Plain.M.loaded_segments (0x26e734 : word) = Some W_26e6ec.
Proof. vm_refl. Qed.
Lemma D_26e6ec : decode_any W_26e6ec = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6f0 : bv 32 := 0x0100006f.
Lemma F_26e6f0 : fetch_word Plain.M.loaded_segments (0x26e738 : word) = Some W_26e6f0.
Proof. vm_refl. Qed.
Lemma D_26e6f0 : decode_any W_26e6f0 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6f4 : bv 32 := 0x0004b583.
Lemma F_26e6f4 : fetch_word Plain.M.loaded_segments (0x26e73c : word) = Some W_26e6f4.
Proof. vm_refl. Qed.
Lemma D_26e6f4 : decode_any W_26e6f4 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6f8 : bv 32 := 0x01048493.
Lemma F_26e6f8 : fetch_word Plain.M.loaded_segments (0x26e740 : word) = Some W_26e6f8.
Proof. vm_refl. Qed.
Lemma D_26e6f8 : decode_any W_26e6f8 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6fc : bv 32 := 0x00058e63.
Lemma F_26e6fc : fetch_word Plain.M.loaded_segments (0x26e744 : word) = Some W_26e6fc.
Proof. vm_refl. Qed.
Lemma D_26e6fc : decode_any W_26e6fc = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e700 : bv 32 := 0xfeb56ae3.
Lemma F_26e700 : fetch_word Plain.M.loaded_segments (0x26e748 : word) = Some W_26e700.
Proof. vm_refl. Qed.
Lemma D_26e700 : decode_any W_26e700 = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e704 : bv 32 := 0xff84b683.
Lemma F_26e704 : fetch_word Plain.M.loaded_segments (0x26e74c : word) = Some W_26e704.
Proof. vm_refl. Qed.
Lemma D_26e704 : decode_any W_26e704 = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e708 : bv 32 := 0x00359593.
Lemma F_26e708 : fetch_word Plain.M.loaded_segments (0x26e750 : word) = Some W_26e708.
Proof. vm_refl. Qed.
Lemma D_26e708 : decode_any W_26e708 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e70c : bv 32 := 0x00b605b3.
Lemma F_26e70c : fetch_word Plain.M.loaded_segments (0x26e754 : word) = Some W_26e70c.
Proof. vm_refl. Qed.
Lemma D_26e70c : decode_any W_26e70c = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e710 : bv 32 := 0x00d5b023.
Lemma F_26e710 : fetch_word Plain.M.loaded_segments (0x26e758 : word) = Some W_26e710.
Proof. vm_refl. Qed.
Lemma D_26e710 : decode_any W_26e710 = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e714 : bv 32 := 0xfe1ff06f.
Lemma F_26e714 : fetch_word Plain.M.loaded_segments (0x26e75c : word) = Some W_26e714.
Proof. vm_refl. Qed.
Lemma D_26e714 : decode_any W_26e714 = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e718 : bv 32 := 0x0b013583.
Lemma F_26e718 : fetch_word Plain.M.loaded_segments (0x26e760 : word) = Some W_26e718.
Proof. vm_refl. Qed.
Lemma D_26e718 : decode_any W_26e718 = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e71c : bv 32 := 0x13013503.
Lemma F_26e71c : fetch_word Plain.M.loaded_segments (0x26e764 : word) = Some W_26e71c.
Proof. vm_refl. Qed.
Lemma D_26e71c : decode_any W_26e71c = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e720 : bv 32 := 0x000a1617.
Lemma F_26e720 : fetch_word Plain.M.loaded_segments (0x26e768 : word) = Some W_26e720.
Proof. vm_refl. Qed.
Lemma D_26e720 : decode_any W_26e720 = Some (Auipc 12 161, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e724 : bv 32 := 0x00b63423.
Lemma F_26e724 : fetch_word Plain.M.loaded_segments (0x26e76c : word) = Some W_26e724.
Proof. vm_refl. Qed.
Lemma D_26e724 : decode_any W_26e724 = Some (Store SZ8 12 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e728 : bv 32 := 0x00050c63.
Lemma F_26e728 : fetch_word Plain.M.loaded_segments (0x26e770 : word) = Some W_26e728.
Proof. vm_refl. Qed.
Lemma D_26e728 : decode_any W_26e728 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e72c : bv 32 := 0x000a1597.
Lemma F_26e72c : fetch_word Plain.M.loaded_segments (0x26e774 : word) = Some W_26e72c.
Proof. vm_refl. Qed.
Lemma D_26e72c : decode_any W_26e72c = Some (Auipc 11 161, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e730 : bv 32 := 0xf6a5be23.
Lemma F_26e730 : fetch_word Plain.M.loaded_segments (0x26e778 : word) = Some W_26e730.
Proof. vm_refl. Qed.
Lemma D_26e730 : decode_any W_26e730 = Some (Store SZ8 11 10 3964, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e734 : bv 32 := 0x00c0006f.
Lemma F_26e734 : fetch_word Plain.M.loaded_segments (0x26e77c : word) = Some W_26e734.
Proof. vm_refl. Qed.
Lemma D_26e734 : decode_any W_26e734 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e738 : bv 32 := 0x000a1517.
Lemma F_26e738 : fetch_word Plain.M.loaded_segments (0x26e780 : word) = Some W_26e738.
Proof. vm_refl. Qed.
Lemma D_26e738 : decode_any W_26e738 = Some (Auipc 10 161, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e73c : bv 32 := 0xfe053823.
Lemma F_26e73c : fetch_word Plain.M.loaded_segments (0x26e784 : word) = Some W_26e73c.
Proof. vm_refl. Qed.
Lemma D_26e73c : decode_any W_26e73c = Some (Store SZ8 10 0 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e740 : bv 32 := 0x06013503.
Lemma F_26e740 : fetch_word Plain.M.loaded_segments (0x26e788 : word) = Some W_26e740.
Proof. vm_refl. Qed.
Lemma D_26e740 : decode_any W_26e740 = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e744 : bv 32 := 0x02a93823.
Lemma F_26e744 : fetch_word Plain.M.loaded_segments (0x26e78c : word) = Some W_26e744.
Proof. vm_refl. Qed.
Lemma D_26e744 : decode_any W_26e744 = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e748 : bv 32 := 0x00041463.
Lemma F_26e748 : fetch_word Plain.M.loaded_segments (0x26e790 : word) = Some W_26e748.
Proof. vm_refl. Qed.
Lemma D_26e748 : decode_any W_26e748 = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e74c : bv 32 := 0x12813403.
Lemma F_26e74c : fetch_word Plain.M.loaded_segments (0x26e794 : word) = Some W_26e74c.
Proof. vm_refl. Qed.
Lemma D_26e74c : decode_any W_26e74c = Some (Load SZ8 true 8 2 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e750 : bv 32 := 0x00041663.
Lemma F_26e750 : fetch_word Plain.M.loaded_segments (0x26e798 : word) = Some W_26e750.
Proof. vm_refl. Qed.
Lemma D_26e750 : decode_any W_26e750 = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e754 : bv 32 := 0xffdab517.
Lemma F_26e754 : fetch_word Plain.M.loaded_segments (0x26e79c : word) = Some W_26e754.
Proof. vm_refl. Qed.
Lemma D_26e754 : decode_any W_26e754 = Some (Auipc 10 1047979, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e758 : bv 32 := 0xdf650413.
Lemma F_26e758 : fetch_word Plain.M.loaded_segments (0x26e7a0 : word) = Some W_26e758.
Proof. vm_refl. Qed.
Lemma D_26e758 : decode_any W_26e758 = Some (OpImm ALU_ADD 8 10 3574, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e75c : bv 32 := 0x0006d517.
Lemma F_26e75c : fetch_word Plain.M.loaded_segments (0x26e7a4 : word) = Some W_26e75c.
Proof. vm_refl. Qed.
Lemma D_26e75c : decode_any W_26e75c = Some (Auipc 10 109, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e760 : bv 32 := 0x98c53583.
Lemma F_26e760 : fetch_word Plain.M.loaded_segments (0x26e7a8 : word) = Some W_26e760.
Proof. vm_refl. Qed.
Lemma D_26e760 : decode_any W_26e760 = Some (Load SZ8 true 11 10 2444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e764 : bv 32 := 0x0006d517.
Lemma F_26e764 : fetch_word Plain.M.loaded_segments (0x26e7ac : word) = Some W_26e764.
Proof. vm_refl. Qed.
Lemma D_26e764 : decode_any W_26e764 = Some (Auipc 10 109, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e768 : bv 32 := 0x98c53503.
Lemma F_26e768 : fetch_word Plain.M.loaded_segments (0x26e7b0 : word) = Some W_26e768.
Proof. vm_refl. Qed.
Lemma D_26e768 : decode_any W_26e768 = Some (Load SZ8 true 10 10 2444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e76c : bv 32 := 0x0085b023.
Lemma F_26e76c : fetch_word Plain.M.loaded_segments (0x26e7b4 : word) = Some W_26e76c.
Proof. vm_refl. Qed.
Lemma D_26e76c : decode_any W_26e76c = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e770 : bv 32 := 0x00140593.
Lemma F_26e770 : fetch_word Plain.M.loaded_segments (0x26e7b8 : word) = Some W_26e770.
Proof. vm_refl. Qed.
Lemma D_26e770 : decode_any W_26e770 = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e774 : bv 32 := 0x00853023.
Lemma F_26e774 : fetch_word Plain.M.loaded_segments (0x26e7bc : word) = Some W_26e774.
Proof. vm_refl. Qed.
Lemma D_26e774 : decode_any W_26e774 = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e778 : bv 32 := 0x02f00613.
Lemma F_26e778 : fetch_word Plain.M.loaded_segments (0x26e7c0 : word) = Some W_26e778.
Proof. vm_refl. Qed.
Lemma D_26e778 : decode_any W_26e778 = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e77c : bv 32 := 0x00c0006f.
Lemma F_26e77c : fetch_word Plain.M.loaded_segments (0x26e7c4 : word) = Some W_26e77c.
Proof. vm_refl. Qed.
Lemma D_26e77c : decode_any W_26e77c = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e780 : bv 32 := 0x00b53023.
Lemma F_26e780 : fetch_word Plain.M.loaded_segments (0x26e7c8 : word) = Some W_26e780.
Proof. vm_refl. Qed.
Lemma D_26e780 : decode_any W_26e780 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e784 : bv 32 := 0x00158593.
Lemma F_26e784 : fetch_word Plain.M.loaded_segments (0x26e7cc : word) = Some W_26e784.
Proof. vm_refl. Qed.
Lemma D_26e784 : decode_any W_26e784 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e788 : bv 32 := 0xfff5c683.
Lemma F_26e788 : fetch_word Plain.M.loaded_segments (0x26e7d0 : word) = Some W_26e788.
Proof. vm_refl. Qed.
Lemma D_26e788 : decode_any W_26e788 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e78c : bv 32 := 0xfec68ae3.
Lemma F_26e78c : fetch_word Plain.M.loaded_segments (0x26e7d4 : word) = Some W_26e78c.
Proof. vm_refl. Qed.
Lemma D_26e78c : decode_any W_26e78c = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e790 : bv 32 := 0xfe069ae3.
Lemma F_26e790 : fetch_word Plain.M.loaded_segments (0x26e7d8 : word) = Some W_26e790.
Proof. vm_refl. Qed.
Lemma D_26e790 : decode_any W_26e790 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e794 : bv 32 := 0x03010513.
Lemma F_26e794 : fetch_word Plain.M.loaded_segments (0x26e7dc : word) = Some W_26e794.
Proof. vm_refl. Qed.
Lemma D_26e794 : decode_any W_26e794 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e798 : bv 32 := 0x2ec000ef.
Lemma F_26e798 : fetch_word Plain.M.loaded_segments (0x26e7e0 : word) = Some W_26e798.
Proof. vm_refl. Qed.
Lemma D_26e798 : decode_any W_26e798 = Some (Jal 1 748, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e79c : bv 32 := 0x0f813503.
Lemma F_26e79c : fetch_word Plain.M.loaded_segments (0x26e7e4 : word) = Some W_26e79c.
Proof. vm_refl. Qed.
Lemma D_26e79c : decode_any W_26e79c = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e7a0 : bv 32 := 0x594000ef.
Lemma F_26e7a0 : fetch_word Plain.M.loaded_segments (0x26e7e8 : word) = Some W_26e7a0.
Proof. vm_refl. Qed.
Lemma D_26e7a0 : decode_any W_26e7a0 = Some (Jal 1 1428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e7a4 : bv 32 := 0x08813503.
Lemma F_26e7a4 : fetch_word Plain.M.loaded_segments (0x26e7ec : word) = Some W_26e7a4.
Proof. vm_refl. Qed.
Lemma D_26e7a4 : decode_any W_26e7a4 = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e7a8 : bv 32 := 0x09013583.
Lemma F_26e7a8 : fetch_word Plain.M.loaded_segments (0x26e7f0 : word) = Some W_26e7a8.
Proof. vm_refl. Qed.
Lemma D_26e7a8 : decode_any W_26e7a8 = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e7ac : bv 32 := 0x00b51c63.
Lemma F_26e7ac : fetch_word Plain.M.loaded_segments (0x26e7f4 : word) = Some W_26e7ac.
Proof. vm_refl. Qed.
Lemma D_26e7ac : decode_any W_26e7ac = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e7b0 : bv 32 := 0x09813503.
Lemma F_26e7b0 : fetch_word Plain.M.loaded_segments (0x26e7f8 : word) = Some W_26e7b0.
Proof. vm_refl. Qed.
Lemma D_26e7b0 : decode_any W_26e7b0 = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e7b4 : bv 32 := 0x0a013583.
Lemma F_26e7b4 : fetch_word Plain.M.loaded_segments (0x26e7fc : word) = Some W_26e7b4.
Proof. vm_refl. Qed.
Lemma D_26e7b4 : decode_any W_26e7b4 = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e7b8 : bv 32 := 0x00b51663.
Lemma F_26e7b8 : fetch_word Plain.M.loaded_segments (0x26e800 : word) = Some W_26e7b8.
Proof. vm_refl. Qed.
Lemma D_26e7b8 : decode_any W_26e7b8 = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e7bc : bv 32 := 0x0e813503.
Lemma F_26e7bc : fetch_word Plain.M.loaded_segments (0x26e804 : word) = Some W_26e7bc.
Proof. vm_refl. Qed.
Lemma D_26e7bc : decode_any W_26e7bc = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e7c0 : bv 32 := 0x0e050063.
Lemma F_26e7c0 : fetch_word Plain.M.loaded_segments (0x26e808 : word) = Some W_26e7c0.
Proof. vm_refl. Qed.
Lemma D_26e7c0 : decode_any W_26e7c0 = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e7c4 : bv 32 := 0x00200693.
Lemma F_26e7c4 : fetch_word Plain.M.loaded_segments (0x26e80c : word) = Some W_26e7c4.
Proof. vm_refl. Qed.
Lemma D_26e7c4 : decode_any W_26e7c4 = Some (OpImm ALU_ADD 13 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e7c8 : bv 32 := 0x00100793.
Lemma F_26e7c8 : fetch_word Plain.M.loaded_segments (0x26e810 : word) = Some W_26e7c8.
Proof. vm_refl. Qed.
Lemma D_26e7c8 : decode_any W_26e7c8 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e7cc : bv 32 := 0x00013423.
Lemma F_26e7cc : fetch_word Plain.M.loaded_segments (0x26e814 : word) = Some W_26e7cc.
Proof. vm_refl. Qed.
Lemma D_26e7cc : decode_any W_26e7cc = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e7d0 : bv 32 := 0x00013823.
Lemma F_26e7d0 : fetch_word Plain.M.loaded_segments (0x26e818 : word) = Some W_26e7d0.
Proof. vm_refl. Qed.
Lemma D_26e7d0 : decode_any W_26e7d0 = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e7d4 : bv 32 := 0x04900893.
Lemma F_26e7d4 : fetch_word Plain.M.loaded_segments (0x26e81c : word) = Some W_26e7d4.
Proof. vm_refl. Qed.
Lemma D_26e7d4 : decode_any W_26e7d4 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e7d8 : bv 32 := 0x01810513.
Lemma F_26e7d8 : fetch_word Plain.M.loaded_segments (0x26e820 : word) = Some W_26e7d8.
Proof. vm_refl. Qed.
Lemma D_26e7d8 : decode_any W_26e7d8 = Some (OpImm ALU_ADD 10 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e7dc : bv 32 := 0x00300593.
Lemma F_26e7dc : fetch_word Plain.M.loaded_segments (0x26e824 : word) = Some W_26e7dc.
Proof. vm_refl. Qed.
Lemma D_26e7dc : decode_any W_26e7dc = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e7e0 : bv 32 := 0x00810613.
Lemma F_26e7e0 : fetch_word Plain.M.loaded_segments (0x26e828 : word) = Some W_26e7e0.
Proof. vm_refl. Qed.
Lemma D_26e7e0 : decode_any W_26e7e0 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e7e4 : bv 32 := 0x00800713.
Lemma F_26e7e4 : fetch_word Plain.M.loaded_segments (0x26e82c : word) = Some W_26e7e4.
Proof. vm_refl. Qed.
Lemma D_26e7e4 : decode_any W_26e7e4 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e7e8 : bv 32 := 0x00013c23.
Lemma F_26e7e8 : fetch_word Plain.M.loaded_segments (0x26e830 : word) = Some W_26e7e8.
Proof. vm_refl. Qed.
Lemma D_26e7e8 : decode_any W_26e7e8 = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e7ec : bv 32 := 0x02f13023.
Lemma F_26e7ec : fetch_word Plain.M.loaded_segments (0x26e834 : word) = Some W_26e7ec.
Proof. vm_refl. Qed.
Lemma D_26e7ec : decode_any W_26e7ec = Some (Store SZ8 2 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e7f0 : bv 32 := 0x02d13423.
Lemma F_26e7f0 : fetch_word Plain.M.loaded_segments (0x26e838 : word) = Some W_26e7f0.
Proof. vm_refl. Qed.
Lemma D_26e7f0 : decode_any W_26e7f0 = Some (Store SZ8 2 13 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e7f4 : bv 32 := 0x00000693.
Lemma F_26e7f4 : fetch_word Plain.M.loaded_segments (0x26e83c : word) = Some W_26e7f4.
Proof. vm_refl. Qed.
Lemma D_26e7f4 : decode_any W_26e7f4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e7f8 : bv 32 := 0x00000073.
Lemma F_26e7f8 : fetch_word Plain.M.loaded_segments (0x26e840 : word) = Some W_26e7f8.
Proof. vm_refl. Qed.
Lemma D_26e7f8 : decode_any W_26e7f8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_26e7f8 : is_ecall W_26e7f8 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26e7fc : bv 32 := 0x02051513.
Lemma F_26e7fc : fetch_word Plain.M.loaded_segments (0x26e844 : word) = Some W_26e7fc.
Proof. vm_refl. Qed.
Lemma D_26e7fc : decode_any W_26e7fc = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e800 : bv 32 := 0x00055463.
Lemma F_26e800 : fetch_word Plain.M.loaded_segments (0x26e848 : word) = Some W_26e800.
Proof. vm_refl. Qed.
Lemma D_26e800 : decode_any W_26e800 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e804 : bv 32 := 0x00000023.
Lemma F_26e804 : fetch_word Plain.M.loaded_segments (0x26e84c : word) = Some W_26e804.
Proof. vm_refl. Qed.
Lemma D_26e804 : decode_any W_26e804 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e808 : bv 32 := 0x01e15503.
Lemma F_26e808 : fetch_word Plain.M.loaded_segments (0x26e850 : word) = Some W_26e808.
Proof. vm_refl. Qed.
Lemma D_26e808 : decode_any W_26e808 = Some (Load SZ2 false 10 2 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e80c : bv 32 := 0x02057513.
Lemma F_26e80c : fetch_word Plain.M.loaded_segments (0x26e854 : word) = Some W_26e80c.
Proof. vm_refl. Qed.
Lemma D_26e80c : decode_any W_26e80c = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e810 : bv 32 := 0x02050463.
Lemma F_26e810 : fetch_word Plain.M.loaded_segments (0x26e858 : word) = Some W_26e810.
Proof. vm_refl. Qed.
Lemma D_26e810 : decode_any W_26e810 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e814 : bv 32 := 0xffdcc517.
Lemma F_26e814 : fetch_word Plain.M.loaded_segments (0x26e85c : word) = Some W_26e814.
Proof. vm_refl. Qed.
Lemma D_26e814 : decode_any W_26e814 = Some (Auipc 10 1048012, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e818 : bv 32 := 0x00008637.
Lemma F_26e818 : fetch_word Plain.M.loaded_segments (0x26e860 : word) = Some W_26e818.
Proof. vm_refl. Qed.
Lemma D_26e818 : decode_any W_26e818 = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e81c : bv 32 := 0x03800893.
Lemma F_26e81c : fetch_word Plain.M.loaded_segments (0x26e864 : word) = Some W_26e81c.
Proof. vm_refl. Qed.
Lemma D_26e81c : decode_any W_26e81c = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e820 : bv 32 := 0xe2d50593.
Lemma F_26e820 : fetch_word Plain.M.loaded_segments (0x26e868 : word) = Some W_26e820.
Proof. vm_refl. Qed.
Lemma D_26e820 : decode_any W_26e820 = Some (OpImm ALU_ADD 11 10 3629, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e824 : bv 32 := 0x0026061b.
Lemma F_26e824 : fetch_word Plain.M.loaded_segments (0x26e86c : word) = Some W_26e824.
Proof. vm_refl. Qed.
Lemma D_26e824 : decode_any W_26e824 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e828 : bv 32 := 0xf9c00513.
Lemma F_26e828 : fetch_word Plain.M.loaded_segments (0x26e870 : word) = Some W_26e828.
Proof. vm_refl. Qed.
Lemma D_26e828 : decode_any W_26e828 = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e82c : bv 32 := 0x00000073.
Lemma F_26e82c : fetch_word Plain.M.loaded_segments (0x26e874 : word) = Some W_26e82c.
Proof. vm_refl. Qed.
Lemma D_26e82c : decode_any W_26e82c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_26e82c : is_ecall W_26e82c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26e830 : bv 32 := 0x00055463.
Lemma F_26e830 : fetch_word Plain.M.loaded_segments (0x26e878 : word) = Some W_26e830.
Proof. vm_refl. Qed.
Lemma D_26e830 : decode_any W_26e830 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e834 : bv 32 := 0x00000023.
Lemma F_26e834 : fetch_word Plain.M.loaded_segments (0x26e87c : word) = Some W_26e834.
Proof. vm_refl. Qed.
Lemma D_26e834 : decode_any W_26e834 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e838 : bv 32 := 0x02615503.
Lemma F_26e838 : fetch_word Plain.M.loaded_segments (0x26e880 : word) = Some W_26e838.
Proof. vm_refl. Qed.
Lemma D_26e838 : decode_any W_26e838 = Some (Load SZ2 false 10 2 38, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e83c : bv 32 := 0x02057513.
Lemma F_26e83c : fetch_word Plain.M.loaded_segments (0x26e884 : word) = Some W_26e83c.
Proof. vm_refl. Qed.
Lemma D_26e83c : decode_any W_26e83c = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e840 : bv 32 := 0x02050463.
Lemma F_26e840 : fetch_word Plain.M.loaded_segments (0x26e888 : word) = Some W_26e840.
Proof. vm_refl. Qed.
Lemma D_26e840 : decode_any W_26e840 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e844 : bv 32 := 0xffdcc517.
Lemma F_26e844 : fetch_word Plain.M.loaded_segments (0x26e88c : word) = Some W_26e844.
Proof. vm_refl. Qed.
Lemma D_26e844 : decode_any W_26e844 = Some (Auipc 10 1048012, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e848 : bv 32 := 0x00008637.
Lemma F_26e848 : fetch_word Plain.M.loaded_segments (0x26e890 : word) = Some W_26e848.
Proof. vm_refl. Qed.
Lemma D_26e848 : decode_any W_26e848 = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e84c : bv 32 := 0x03800893.
Lemma F_26e84c : fetch_word Plain.M.loaded_segments (0x26e894 : word) = Some W_26e84c.
Proof. vm_refl. Qed.
Lemma D_26e84c : decode_any W_26e84c = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e850 : bv 32 := 0xdfd50593.
Lemma F_26e850 : fetch_word Plain.M.loaded_segments (0x26e898 : word) = Some W_26e850.
Proof. vm_refl. Qed.
Lemma D_26e850 : decode_any W_26e850 = Some (OpImm ALU_ADD 11 10 3581, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e854 : bv 32 := 0x0026061b.
Lemma F_26e854 : fetch_word Plain.M.loaded_segments (0x26e89c : word) = Some W_26e854.
Proof. vm_refl. Qed.
Lemma D_26e854 : decode_any W_26e854 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e858 : bv 32 := 0xf9c00513.
Lemma F_26e858 : fetch_word Plain.M.loaded_segments (0x26e8a0 : word) = Some W_26e858.
Proof. vm_refl. Qed.
Lemma D_26e858 : decode_any W_26e858 = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e85c : bv 32 := 0x00000073.
Lemma F_26e85c : fetch_word Plain.M.loaded_segments (0x26e8a4 : word) = Some W_26e85c.
Proof. vm_refl. Qed.
Lemma D_26e85c : decode_any W_26e85c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_26e85c : is_ecall W_26e85c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26e860 : bv 32 := 0x00055463.
Lemma F_26e860 : fetch_word Plain.M.loaded_segments (0x26e8a8 : word) = Some W_26e860.
Proof. vm_refl. Qed.
Lemma D_26e860 : decode_any W_26e860 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e864 : bv 32 := 0x00000023.
Lemma F_26e864 : fetch_word Plain.M.loaded_segments (0x26e8ac : word) = Some W_26e864.
Proof. vm_refl. Qed.
Lemma D_26e864 : decode_any W_26e864 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e868 : bv 32 := 0x02e15503.
Lemma F_26e868 : fetch_word Plain.M.loaded_segments (0x26e8b0 : word) = Some W_26e868.
Proof. vm_refl. Qed.
Lemma D_26e868 : decode_any W_26e868 = Some (Load SZ2 false 10 2 46, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e86c : bv 32 := 0x02057513.
Lemma F_26e86c : fetch_word Plain.M.loaded_segments (0x26e8b4 : word) = Some W_26e86c.
Proof. vm_refl. Qed.
Lemma D_26e86c : decode_any W_26e86c = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e870 : bv 32 := 0x02050463.
Lemma F_26e870 : fetch_word Plain.M.loaded_segments (0x26e8b8 : word) = Some W_26e870.
Proof. vm_refl. Qed.
Lemma D_26e870 : decode_any W_26e870 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e874 : bv 32 := 0xffdcc517.
Lemma F_26e874 : fetch_word Plain.M.loaded_segments (0x26e8bc : word) = Some W_26e874.
Proof. vm_refl. Qed.
Lemma D_26e874 : decode_any W_26e874 = Some (Auipc 10 1048012, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e878 : bv 32 := 0x00008637.
Lemma F_26e878 : fetch_word Plain.M.loaded_segments (0x26e8c0 : word) = Some W_26e878.
Proof. vm_refl. Qed.
Lemma D_26e878 : decode_any W_26e878 = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e87c : bv 32 := 0x03800893.
Lemma F_26e87c : fetch_word Plain.M.loaded_segments (0x26e8c4 : word) = Some W_26e87c.
Proof. vm_refl. Qed.
Lemma D_26e87c : decode_any W_26e87c = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e880 : bv 32 := 0xdcd50593.
Lemma F_26e880 : fetch_word Plain.M.loaded_segments (0x26e8c8 : word) = Some W_26e880.
Proof. vm_refl. Qed.
Lemma D_26e880 : decode_any W_26e880 = Some (OpImm ALU_ADD 11 10 3533, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e884 : bv 32 := 0x0026061b.
Lemma F_26e884 : fetch_word Plain.M.loaded_segments (0x26e8cc : word) = Some W_26e884.
Proof. vm_refl. Qed.
Lemma D_26e884 : decode_any W_26e884 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e888 : bv 32 := 0xf9c00513.
Lemma F_26e888 : fetch_word Plain.M.loaded_segments (0x26e8d0 : word) = Some W_26e888.
Proof. vm_refl. Qed.
Lemma D_26e888 : decode_any W_26e888 = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e88c : bv 32 := 0x00000073.
Lemma F_26e88c : fetch_word Plain.M.loaded_segments (0x26e8d4 : word) = Some W_26e88c.
Proof. vm_refl. Qed.
Lemma D_26e88c : decode_any W_26e88c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_26e88c : is_ecall W_26e88c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26e890 : bv 32 := 0x00055463.
Lemma F_26e890 : fetch_word Plain.M.loaded_segments (0x26e8d8 : word) = Some W_26e890.
Proof. vm_refl. Qed.
Lemma D_26e890 : decode_any W_26e890 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e894 : bv 32 := 0x00000023.
Lemma F_26e894 : fetch_word Plain.M.loaded_segments (0x26e8dc : word) = Some W_26e894.
Proof. vm_refl. Qed.
Lemma D_26e894 : decode_any W_26e894 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e898 : bv 32 := 0x00100513.
Lemma F_26e898 : fetch_word Plain.M.loaded_segments (0x26e8e0 : word) = Some W_26e898.
Proof. vm_refl. Qed.
Lemma D_26e898 : decode_any W_26e898 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e89c : bv 32 := 0x00a90123.
Lemma F_26e89c : fetch_word Plain.M.loaded_segments (0x26e8e4 : word) = Some W_26e89c.
Proof. vm_refl. Qed.
Lemma D_26e89c : decode_any W_26e89c = Some (Store SZ1 18 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e8a0 : bv 32 := 0x17813083.
Lemma F_26e8a0 : fetch_word Plain.M.loaded_segments (0x26e8e8 : word) = Some W_26e8a0.
Proof. vm_refl. Qed.
Lemma D_26e8a0 : decode_any W_26e8a0 = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e8a4 : bv 32 := 0x17013403.
Lemma F_26e8a4 : fetch_word Plain.M.loaded_segments (0x26e8ec : word) = Some W_26e8a4.
Proof. vm_refl. Qed.
Lemma D_26e8a4 : decode_any W_26e8a4 = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e8a8 : bv 32 := 0x16813483.
Lemma F_26e8a8 : fetch_word Plain.M.loaded_segments (0x26e8f0 : word) = Some W_26e8a8.
Proof. vm_refl. Qed.
Lemma D_26e8a8 : decode_any W_26e8a8 = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e8ac : bv 32 := 0x16013903.
Lemma F_26e8ac : fetch_word Plain.M.loaded_segments (0x26e8f4 : word) = Some W_26e8ac.
Proof. vm_refl. Qed.
Lemma D_26e8ac : decode_any W_26e8ac = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e8b0 : bv 32 := 0x18010113.
Lemma F_26e8b0 : fetch_word Plain.M.loaded_segments (0x26e8f8 : word) = Some W_26e8b0.
Proof. vm_refl. Qed.
Lemma D_26e8b0 : decode_any W_26e8b0 = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e8b4 : bv 32 := 0x00008067.
Lemma F_26e8b4 : fetch_word Plain.M.loaded_segments (0x26e8fc : word) = Some W_26e8b4.
Proof. vm_refl. Qed.
Lemma D_26e8b4 : decode_any W_26e8b4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e8b8 : bv 32 := 0xfe010113.
Lemma F_26e8b8 : fetch_word Plain.M.loaded_segments (0x26e900 : word) = Some W_26e8b8.
Proof. vm_refl. Qed.
Lemma D_26e8b8 : decode_any W_26e8b8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e8bc : bv 32 := 0x00113c23.
Lemma F_26e8bc : fetch_word Plain.M.loaded_segments (0x26e904 : word) = Some W_26e8bc.
Proof. vm_refl. Qed.
Lemma D_26e8bc : decode_any W_26e8bc = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e8c0 : bv 32 := 0x00813823.
Lemma F_26e8c0 : fetch_word Plain.M.loaded_segments (0x26e908 : word) = Some W_26e8c0.
Proof. vm_refl. Qed.
Lemma D_26e8c0 : decode_any W_26e8c0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e8c4 : bv 32 := 0x00913423.
Lemma F_26e8c4 : fetch_word Plain.M.loaded_segments (0x26e90c : word) = Some W_26e8c4.
Proof. vm_refl. Qed.
Lemma D_26e8c4 : decode_any W_26e8c4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e8c8 : bv 32 := 0xdc1ff0ef.
Lemma F_26e8c8 : fetch_word Plain.M.loaded_segments (0x26e910 : word) = Some W_26e8c8.
Proof. vm_refl. Qed.
Lemma D_26e8c8 : decode_any W_26e8c8 = Some (Jal 1 2096576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e8cc : bv 32 := 0x0006d517.
Lemma F_26e8cc : fetch_word Plain.M.loaded_segments (0x26e914 : word) = Some W_26e8cc.
Proof. vm_refl. Qed.
Lemma D_26e8cc : decode_any W_26e8cc = Some (Auipc 10 109, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e8d0 : bv 32 := 0x0006d597.
Lemma F_26e8d0 : fetch_word Plain.M.loaded_segments (0x26e918 : word) = Some W_26e8d0.
Proof. vm_refl. Qed.
Lemma D_26e8d0 : decode_any W_26e8d0 = Some (Auipc 11 109, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e8d4 : bv 32 := 0x82c53403.
Lemma F_26e8d4 : fetch_word Plain.M.loaded_segments (0x26e91c : word) = Some W_26e8d4.
Proof. vm_refl. Qed.
Lemma D_26e8d4 : decode_any W_26e8d4 = Some (Load SZ8 true 8 10 2092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e8d8 : bv 32 := 0x8305b483.
Lemma F_26e8d8 : fetch_word Plain.M.loaded_segments (0x26e920 : word) = Some W_26e8d8.
Proof. vm_refl. Qed.
Lemma D_26e8d8 : decode_any W_26e8d8 = Some (Load SZ8 true 9 11 2096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e8dc : bv 32 := 0x0084fa63.
Lemma F_26e8dc : fetch_word Plain.M.loaded_segments (0x26e924 : word) = Some W_26e8dc.
Proof. vm_refl. Qed.
Lemma D_26e8dc : decode_any W_26e8dc = Some (Branch BC_GEU 9 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e8e0 : bv 32 := 0x0004b503.
Lemma F_26e8e0 : fetch_word Plain.M.loaded_segments (0x26e928 : word) = Some W_26e8e0.
Proof. vm_refl. Qed.
Lemma D_26e8e0 : decode_any W_26e8e0 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e8e4 : bv 32 := 0x000500e7.
Lemma F_26e8e4 : fetch_word Plain.M.loaded_segments (0x26e92c : word) = Some W_26e8e4.
Proof. vm_refl. Qed.
Lemma D_26e8e4 : decode_any W_26e8e4 = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e8e8 : bv 32 := 0x00848493.
Lemma F_26e8e8 : fetch_word Plain.M.loaded_segments (0x26e930 : word) = Some W_26e8e8.
Proof. vm_refl. Qed.
Lemma D_26e8e8 : decode_any W_26e8e8 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e8ec : bv 32 := 0xfe84eae3.
Lemma F_26e8ec : fetch_word Plain.M.loaded_segments (0x26e934 : word) = Some W_26e8ec.
Proof. vm_refl. Qed.
Lemma D_26e8ec : decode_any W_26e8ec = Some (Branch BC_LTU 9 8 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e8f0 : bv 32 := 0x01813083.
Lemma F_26e8f0 : fetch_word Plain.M.loaded_segments (0x26e938 : word) = Some W_26e8f0.
Proof. vm_refl. Qed.
Lemma D_26e8f0 : decode_any W_26e8f0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e8f4 : bv 32 := 0x01013403.
Lemma F_26e8f4 : fetch_word Plain.M.loaded_segments (0x26e93c : word) = Some W_26e8f4.
Proof. vm_refl. Qed.
Lemma D_26e8f4 : decode_any W_26e8f4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e8f8 : bv 32 := 0x00813483.
Lemma F_26e8f8 : fetch_word Plain.M.loaded_segments (0x26e940 : word) = Some W_26e8f8.
Proof. vm_refl. Qed.
Lemma D_26e8f8 : decode_any W_26e8f8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e8fc : bv 32 := 0x02010113.
Lemma F_26e8fc : fetch_word Plain.M.loaded_segments (0x26e944 : word) = Some W_26e8fc.
Proof. vm_refl. Qed.
Lemma D_26e8fc : decode_any W_26e8fc = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e900 : bv 32 := 0x00008067.
Lemma F_26e900 : fetch_word Plain.M.loaded_segments (0x26e948 : word) = Some W_26e900.
Proof. vm_refl. Qed.
Lemma D_26e900 : decode_any W_26e900 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e904 : bv 32 := 0xfe010113.
Lemma F_26e904 : fetch_word Plain.M.loaded_segments (0x26e94c : word) = Some W_26e904.
Proof. vm_refl. Qed.
Lemma D_26e904 : decode_any W_26e904 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e908 : bv 32 := 0x00113c23.
Lemma F_26e908 : fetch_word Plain.M.loaded_segments (0x26e950 : word) = Some W_26e908.
Proof. vm_refl. Qed.
Lemma D_26e908 : decode_any W_26e908 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e90c : bv 32 := 0x00813823.
Lemma F_26e90c : fetch_word Plain.M.loaded_segments (0x26e954 : word) = Some W_26e90c.
Proof. vm_refl. Qed.
Lemma D_26e90c : decode_any W_26e90c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e910 : bv 32 := 0x00913423.
Lemma F_26e910 : fetch_word Plain.M.loaded_segments (0x26e958 : word) = Some W_26e910.
Proof. vm_refl. Qed.
Lemma D_26e910 : decode_any W_26e910 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e914 : bv 32 := 0x01213023.
Lemma F_26e914 : fetch_word Plain.M.loaded_segments (0x26e95c : word) = Some W_26e914.
Proof. vm_refl. Qed.
Lemma D_26e914 : decode_any W_26e914 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e918 : bv 32 := 0x00060413.
Lemma F_26e918 : fetch_word Plain.M.loaded_segments (0x26e960 : word) = Some W_26e918.
Proof. vm_refl. Qed.
Lemma D_26e918 : decode_any W_26e918 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e91c : bv 32 := 0x00058493.
Lemma F_26e91c : fetch_word Plain.M.loaded_segments (0x26e964 : word) = Some W_26e91c.
Proof. vm_refl. Qed.
Lemma D_26e91c : decode_any W_26e91c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e920 : bv 32 := 0x00050913.
Lemma F_26e920 : fetch_word Plain.M.loaded_segments (0x26e968 : word) = Some W_26e920.
Proof. vm_refl. Qed.
Lemma D_26e920 : decode_any W_26e920 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e924 : bv 32 := 0x00063583.
Lemma F_26e924 : fetch_word Plain.M.loaded_segments (0x26e96c : word) = Some W_26e924.
Proof. vm_refl. Qed.
Lemma D_26e924 : decode_any W_26e924 = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e928 : bv 32 := 0x00349513.
Lemma F_26e928 : fetch_word Plain.M.loaded_segments (0x26e970 : word) = Some W_26e928.
Proof. vm_refl. Qed.
Lemma D_26e928 : decode_any W_26e928 = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e92c : bv 32 := 0x00a60533.
Lemma F_26e92c : fetch_word Plain.M.loaded_segments (0x26e974 : word) = Some W_26e92c.
Proof. vm_refl. Qed.
Lemma D_26e92c : decode_any W_26e92c = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e930 : bv 32 := 0x00850513.
Lemma F_26e930 : fetch_word Plain.M.loaded_segments (0x26e978 : word) = Some W_26e930.
Proof. vm_refl. Qed.
Lemma D_26e930 : decode_any W_26e930 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e934 : bv 32 := 0xd59ff0ef.
Lemma F_26e934 : fetch_word Plain.M.loaded_segments (0x26e97c : word) = Some W_26e934.
Proof. vm_refl. Qed.
Lemma D_26e934 : decode_any W_26e934 = Some (Jal 1 2096472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e938 : bv 32 := 0x00000517.
Lemma F_26e938 : fetch_word Plain.M.loaded_segments (0x26e980 : word) = Some W_26e938.
Proof. vm_refl. Qed.
Lemma D_26e938 : decode_any W_26e938 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e93c : bv 32 := 0x02c50313.
Lemma F_26e93c : fetch_word Plain.M.loaded_segments (0x26e984 : word) = Some W_26e93c.
Proof. vm_refl. Qed.
Lemma D_26e93c : decode_any W_26e93c = Some (OpImm ALU_ADD 6 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e940 : bv 32 := 0x00090513.
Lemma F_26e940 : fetch_word Plain.M.loaded_segments (0x26e988 : word) = Some W_26e940.
Proof. vm_refl. Qed.
Lemma D_26e940 : decode_any W_26e940 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e944 : bv 32 := 0x00048593.
Lemma F_26e944 : fetch_word Plain.M.loaded_segments (0x26e98c : word) = Some W_26e944.
Proof. vm_refl. Qed.
Lemma D_26e944 : decode_any W_26e944 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e948 : bv 32 := 0x00040613.
Lemma F_26e948 : fetch_word Plain.M.loaded_segments (0x26e990 : word) = Some W_26e948.
Proof. vm_refl. Qed.
Lemma D_26e948 : decode_any W_26e948 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e94c : bv 32 := 0x01813083.
Lemma F_26e94c : fetch_word Plain.M.loaded_segments (0x26e994 : word) = Some W_26e94c.
Proof. vm_refl. Qed.
Lemma D_26e94c : decode_any W_26e94c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e950 : bv 32 := 0x01013403.
Lemma F_26e950 : fetch_word Plain.M.loaded_segments (0x26e998 : word) = Some W_26e950.
Proof. vm_refl. Qed.
Lemma D_26e950 : decode_any W_26e950 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e954 : bv 32 := 0x00813483.
Lemma F_26e954 : fetch_word Plain.M.loaded_segments (0x26e99c : word) = Some W_26e954.
Proof. vm_refl. Qed.
Lemma D_26e954 : decode_any W_26e954 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e958 : bv 32 := 0x00013903.
Lemma F_26e958 : fetch_word Plain.M.loaded_segments (0x26e9a0 : word) = Some W_26e958.
Proof. vm_refl. Qed.
Lemma D_26e958 : decode_any W_26e958 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e95c : bv 32 := 0x02010113.
Lemma F_26e95c : fetch_word Plain.M.loaded_segments (0x26e9a4 : word) = Some W_26e95c.
Proof. vm_refl. Qed.
Lemma D_26e95c : decode_any W_26e95c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e960 : bv 32 := 0x00030067.
Lemma F_26e960 : fetch_word Plain.M.loaded_segments (0x26e9a8 : word) = Some W_26e960.
Proof. vm_refl. Qed.
Lemma D_26e960 : decode_any W_26e960 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e964 : bv 32 := 0xfd010113.
Lemma F_26e964 : fetch_word Plain.M.loaded_segments (0x26e9ac : word) = Some W_26e964.
Proof. vm_refl. Qed.
Lemma D_26e964 : decode_any W_26e964 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e968 : bv 32 := 0x02113423.
Lemma F_26e968 : fetch_word Plain.M.loaded_segments (0x26e9b0 : word) = Some W_26e968.
Proof. vm_refl. Qed.
Lemma D_26e968 : decode_any W_26e968 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e96c : bv 32 := 0x02813023.
Lemma F_26e96c : fetch_word Plain.M.loaded_segments (0x26e9b4 : word) = Some W_26e96c.
Proof. vm_refl. Qed.
Lemma D_26e96c : decode_any W_26e96c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e970 : bv 32 := 0x00913c23.
Lemma F_26e970 : fetch_word Plain.M.loaded_segments (0x26e9b8 : word) = Some W_26e970.
Proof. vm_refl. Qed.
Lemma D_26e970 : decode_any W_26e970 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e974 : bv 32 := 0x01213823.
Lemma F_26e974 : fetch_word Plain.M.loaded_segments (0x26e9bc : word) = Some W_26e974.
Proof. vm_refl. Qed.
Lemma D_26e974 : decode_any W_26e974 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e978 : bv 32 := 0x01313423.
Lemma F_26e978 : fetch_word Plain.M.loaded_segments (0x26e9c0 : word) = Some W_26e978.
Proof. vm_refl. Qed.
Lemma D_26e978 : decode_any W_26e978 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e97c : bv 32 := 0x00060413.
Lemma F_26e97c : fetch_word Plain.M.loaded_segments (0x26e9c4 : word) = Some W_26e97c.
Proof. vm_refl. Qed.
Lemma D_26e97c : decode_any W_26e97c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e980 : bv 32 := 0x00058493.
Lemma F_26e980 : fetch_word Plain.M.loaded_segments (0x26e9c8 : word) = Some W_26e980.
Proof. vm_refl. Qed.
Lemma D_26e980 : decode_any W_26e980 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e984 : bv 32 := 0x00050913.
Lemma F_26e984 : fetch_word Plain.M.loaded_segments (0x26e9cc : word) = Some W_26e984.
Proof. vm_refl. Qed.
Lemma D_26e984 : decode_any W_26e984 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e988 : bv 32 := 0x00359513.
Lemma F_26e988 : fetch_word Plain.M.loaded_segments (0x26e9d0 : word) = Some W_26e988.
Proof. vm_refl. Qed.
Lemma D_26e988 : decode_any W_26e988 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e98c : bv 32 := 0x00a60533.
Lemma F_26e98c : fetch_word Plain.M.loaded_segments (0x26e9d4 : word) = Some W_26e98c.
Proof. vm_refl. Qed.
Lemma D_26e98c : decode_any W_26e98c = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e990 : bv 32 := 0x00850993.
Lemma F_26e990 : fetch_word Plain.M.loaded_segments (0x26e9d8 : word) = Some W_26e990.
Proof. vm_refl. Qed.
Lemma D_26e990 : decode_any W_26e990 = Some (OpImm ALU_ADD 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e994 : bv 32 := 0xf25ff0ef.
Lemma F_26e994 : fetch_word Plain.M.loaded_segments (0x26e9dc : word) = Some W_26e994.
Proof. vm_refl. Qed.
Lemma D_26e994 : decode_any W_26e994 = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e998 : bv 32 := 0x00048513.
Lemma F_26e998 : fetch_word Plain.M.loaded_segments (0x26e9e0 : word) = Some W_26e998.
Proof. vm_refl. Qed.
Lemma D_26e998 : decode_any W_26e998 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e99c : bv 32 := 0x00040593.
Lemma F_26e99c : fetch_word Plain.M.loaded_segments (0x26e9e4 : word) = Some W_26e99c.
Proof. vm_refl. Qed.
Lemma D_26e99c : decode_any W_26e99c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e9a0 : bv 32 := 0x00098613.
Lemma F_26e9a0 : fetch_word Plain.M.loaded_segments (0x26e9e8 : word) = Some W_26e9a0.
Proof. vm_refl. Qed.
Lemma D_26e9a0 : decode_any W_26e9a0 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e9a4 : bv 32 := 0x000900e7.
Lemma F_26e9a4 : fetch_word Plain.M.loaded_segments (0x26e9ec : word) = Some W_26e9a4.
Proof. vm_refl. Qed.
Lemma D_26e9a4 : decode_any W_26e9a4 = Some (Jalr 1 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e9a8 : bv 32 := 0x694000ef.
Lemma F_26e9a8 : fetch_word Plain.M.loaded_segments (0x26e9f0 : word) = Some W_26e9a8.
Proof. vm_refl. Qed.
Lemma D_26e9a8 : decode_any W_26e9a8 = Some (Jal 1 1684, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e9ac : bv 32 := 0xfc010113.
Lemma F_26e9ac : fetch_word Plain.M.loaded_segments (0x26e9f4 : word) = Some W_26e9ac.
Proof. vm_refl. Qed.
Lemma D_26e9ac : decode_any W_26e9ac = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e9b0 : bv 32 := 0x02113c23.
Lemma F_26e9b0 : fetch_word Plain.M.loaded_segments (0x26e9f8 : word) = Some W_26e9b0.
Proof. vm_refl. Qed.
Lemma D_26e9b0 : decode_any W_26e9b0 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e9b4 : bv 32 := 0x02813823.
Lemma F_26e9b4 : fetch_word Plain.M.loaded_segments (0x26e9fc : word) = Some W_26e9b4.
Proof. vm_refl. Qed.
Lemma D_26e9b4 : decode_any W_26e9b4 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e9b8 : bv 32 := 0x02913423.
Lemma F_26e9b8 : fetch_word Plain.M.loaded_segments (0x26ea00 : word) = Some W_26e9b8.
Proof. vm_refl. Qed.
Lemma D_26e9b8 : decode_any W_26e9b8 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e9bc : bv 32 := 0x03213023.
Lemma F_26e9bc : fetch_word Plain.M.loaded_segments (0x26ea04 : word) = Some W_26e9bc.
Proof. vm_refl. Qed.
Lemma D_26e9bc : decode_any W_26e9bc = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e9c0 : bv 32 := 0x01313c23.
Lemma F_26e9c0 : fetch_word Plain.M.loaded_segments (0x26ea08 : word) = Some W_26e9c0.
Proof. vm_refl. Qed.
Lemma D_26e9c0 : decode_any W_26e9c0 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e9c4 : bv 32 := 0x01413823.
Lemma F_26e9c4 : fetch_word Plain.M.loaded_segments (0x26ea0c : word) = Some W_26e9c4.
Proof. vm_refl. Qed.
Lemma D_26e9c4 : decode_any W_26e9c4 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e9c8 : bv 32 := 0x01513423.
Lemma F_26e9c8 : fetch_word Plain.M.loaded_segments (0x26ea10 : word) = Some W_26e9c8.
Proof. vm_refl. Qed.
Lemma D_26e9c8 : decode_any W_26e9c8 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e9cc : bv 32 := 0x000a1597.
Lemma F_26e9cc : fetch_word Plain.M.loaded_segments (0x26ea14 : word) = Some W_26e9cc.
Proof. vm_refl. Qed.
Lemma D_26e9cc : decode_any W_26e9cc = Some (Auipc 11 161, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e9d0 : bv 32 := 0xf3800693.
Lemma F_26e9d0 : fetch_word Plain.M.loaded_segments (0x26ea18 : word) = Some W_26e9d0.
Proof. vm_refl. Qed.
Lemma D_26e9d0 : decode_any W_26e9d0 = Some (OpImm ALU_ADD 13 0 3896, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e9d4 : bv 32 := 0xcf458493.
Lemma F_26e9d4 : fetch_word Plain.M.loaded_segments (0x26ea1c : word) = Some W_26e9d4.
Proof. vm_refl. Qed.
Lemma D_26e9d4 : decode_any W_26e9d4 = Some (OpImm ALU_ADD 9 11 3316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e9d8 : bv 32 := 0x0104b903.
Lemma F_26e9d8 : fetch_word Plain.M.loaded_segments (0x26ea20 : word) = Some W_26e9d8.
Proof. vm_refl. Qed.
Lemma D_26e9d8 : decode_any W_26e9d8 = Some (Load SZ8 true 18 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e9dc : bv 32 := 0x0184b603.
Lemma F_26e9dc : fetch_word Plain.M.loaded_segments (0x26ea24 : word) = Some W_26e9dc.
Proof. vm_refl. Qed.
Lemma D_26e9dc : decode_any W_26e9dc = Some (Load SZ8 true 12 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e9e0 : bv 32 := 0x0204b703.
Lemma F_26e9e0 : fetch_word Plain.M.loaded_segments (0x26ea28 : word) = Some W_26e9e0.
Proof. vm_refl. Qed.
Lemma D_26e9e0 : decode_any W_26e9e0 = Some (Load SZ8 true 14 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e9e4 : bv 32 := 0x40a686b3.
Lemma F_26e9e4 : fetch_word Plain.M.loaded_segments (0x26ea2c : word) = Some W_26e9e4.
Proof. vm_refl. Qed.
Lemma D_26e9e4 : decode_any W_26e9e4 = Some (Op ALU_SUB 13 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e9e8 : bv 32 := 0x0284b583.
Lemma F_26e9e8 : fetch_word Plain.M.loaded_segments (0x26ea30 : word) = Some W_26e9e8.
Proof. vm_refl. Qed.
Lemma D_26e9e8 : decode_any W_26e9e8 = Some (Load SZ8 true 11 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e9ec : bv 32 := 0x00c509b3.
Lemma F_26e9ec : fetch_word Plain.M.loaded_segments (0x26ea34 : word) = Some W_26e9ec.
Proof. vm_refl. Qed.
Lemma D_26e9ec : decode_any W_26e9ec = Some (Op ALU_ADD 19 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e9f0 : bv 32 := 0xfff70713.
Lemma F_26e9f0 : fetch_word Plain.M.loaded_segments (0x26ea38 : word) = Some W_26e9f0.
Proof. vm_refl. Qed.
Lemma D_26e9f0 : decode_any W_26e9f0 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e9f4 : bv 32 := 0x00d776b3.
Lemma F_26e9f4 : fetch_word Plain.M.loaded_segments (0x26ea3c : word) = Some W_26e9f4.
Proof. vm_refl. Qed.
Lemma D_26e9f4 : decode_any W_26e9f4 = Some (Op ALU_AND 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e9f8 : bv 32 := 0xfff5c713.
Lemma F_26e9f8 : fetch_word Plain.M.loaded_segments (0x26ea40 : word) = Some W_26e9f8.
Proof. vm_refl. Qed.
Lemma D_26e9f8 : decode_any W_26e9f8 = Some (OpImm ALU_XOR 14 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e9fc : bv 32 := 0x00371713.
Lemma F_26e9fc : fetch_word Plain.M.loaded_segments (0x26ea44 : word) = Some W_26e9fc.
Proof. vm_refl. Qed.
Lemma D_26e9fc : decode_any W_26e9fc = Some (ShiftImm ALU_SLL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea00 : bv 32 := 0x00e989b3.
Lemma F_26ea00 : fetch_word Plain.M.loaded_segments (0x26ea48 : word) = Some W_26ea00.
Proof. vm_refl. Qed.
Lemma D_26ea00 : decode_any W_26ea00 = Some (Op ALU_ADD 19 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea04 : bv 32 := 0x00d50433.
Lemma F_26ea04 : fetch_word Plain.M.loaded_segments (0x26ea4c : word) = Some W_26ea04.
Proof. vm_refl. Qed.
Lemma D_26ea04 : decode_any W_26ea04 = Some (Op ALU_ADD 8 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea08 : bv 32 := 0x04090663.
Lemma F_26ea08 : fetch_word Plain.M.loaded_segments (0x26ea50 : word) = Some W_26ea08.
Proof. vm_refl. Qed.
Lemma D_26ea08 : decode_any W_26ea08 = Some (Branch BC_EQ 18 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea0c : bv 32 := 0x0c840a13.
Lemma F_26ea0c : fetch_word Plain.M.loaded_segments (0x26ea54 : word) = Some W_26ea0c.
Proof. vm_refl. Qed.
Lemma D_26ea0c : decode_any W_26ea0c = Some (OpImm ALU_ADD 20 8 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea10 : bv 32 := 0x00359593.
Lemma F_26ea10 : fetch_word Plain.M.loaded_segments (0x26ea58 : word) = Some W_26ea10.
Proof. vm_refl. Qed.
Lemma D_26ea10 : decode_any W_26ea10 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea14 : bv 32 := 0x00c50533.
Lemma F_26ea14 : fetch_word Plain.M.loaded_segments (0x26ea5c : word) = Some W_26ea14.
Proof. vm_refl. Qed.
Lemma D_26ea14 : decode_any W_26ea14 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea18 : bv 32 := 0x40b50ab3.
Lemma F_26ea18 : fetch_word Plain.M.loaded_segments (0x26ea60 : word) = Some W_26ea18.
Proof. vm_refl. Qed.
Lemma D_26ea18 : decode_any W_26ea18 = Some (Op ALU_SUB 21 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea1c : bv 32 := 0x02893503.
Lemma F_26ea1c : fetch_word Plain.M.loaded_segments (0x26ea64 : word) = Some W_26ea1c.
Proof. vm_refl. Qed.
Lemma D_26ea1c : decode_any W_26ea1c = Some (Load SZ8 true 10 18 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea20 : bv 32 := 0x00aa0533.
Lemma F_26ea20 : fetch_word Plain.M.loaded_segments (0x26ea68 : word) = Some W_26ea20.
Proof. vm_refl. Qed.
Lemma D_26ea20 : decode_any W_26ea20 = Some (Op ALU_ADD 10 20 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea24 : bv 32 := 0x7ff50513.
Lemma F_26ea24 : fetch_word Plain.M.loaded_segments (0x26ea6c : word) = Some W_26ea24.
Proof. vm_refl. Qed.
Lemma D_26ea24 : decode_any W_26ea24 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea28 : bv 32 := 0x00150513.
Lemma F_26ea28 : fetch_word Plain.M.loaded_segments (0x26ea70 : word) = Some W_26ea28.
Proof. vm_refl. Qed.
Lemma D_26ea28 : decode_any W_26ea28 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea2c : bv 32 := 0x00aab023.
Lemma F_26ea2c : fetch_word Plain.M.loaded_segments (0x26ea74 : word) = Some W_26ea2c.
Proof. vm_refl. Qed.
Lemma D_26ea2c : decode_any W_26ea2c = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea30 : bv 32 := 0x02893503.
Lemma F_26ea30 : fetch_word Plain.M.loaded_segments (0x26ea78 : word) = Some W_26ea30.
Proof. vm_refl. Qed.
Lemma D_26ea30 : decode_any W_26ea30 = Some (Load SZ8 true 10 18 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea34 : bv 32 := 0x00893583.
Lemma F_26ea34 : fetch_word Plain.M.loaded_segments (0x26ea7c : word) = Some W_26ea34.
Proof. vm_refl. Qed.
Lemma D_26ea34 : decode_any W_26ea34 = Some (Load SZ8 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea38 : bv 32 := 0x01093603.
Lemma F_26ea38 : fetch_word Plain.M.loaded_segments (0x26ea80 : word) = Some W_26ea38.
Proof. vm_refl. Qed.
Lemma D_26ea38 : decode_any W_26ea38 = Some (Load SZ8 true 12 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea3c : bv 32 := 0x00aa0533.
Lemma F_26ea3c : fetch_word Plain.M.loaded_segments (0x26ea84 : word) = Some W_26ea3c.
Proof. vm_refl. Qed.
Lemma D_26ea3c : decode_any W_26ea3c = Some (Op ALU_ADD 10 20 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea40 : bv 32 := 0x6350a0ef.
Lemma F_26ea40 : fetch_word Plain.M.loaded_segments (0x26ea88 : word) = Some W_26ea40.
Proof. vm_refl. Qed.
Lemma D_26ea40 : decode_any W_26ea40 = Some (Jal 1 44596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea44 : bv 32 := 0x00093903.
Lemma F_26ea44 : fetch_word Plain.M.loaded_segments (0x26ea8c : word) = Some W_26ea44.
Proof. vm_refl. Qed.
Lemma D_26ea44 : decode_any W_26ea44 = Some (Load SZ8 true 18 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea48 : bv 32 := 0x008a8a93.
Lemma F_26ea48 : fetch_word Plain.M.loaded_segments (0x26ea90 : word) = Some W_26ea48.
Proof. vm_refl. Qed.
Lemma D_26ea48 : decode_any W_26ea48 = Some (OpImm ALU_ADD 21 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea4c : bv 32 := 0xfc0918e3.
Lemma F_26ea4c : fetch_word Plain.M.loaded_segments (0x26ea94 : word) = Some W_26ea4c.
Proof. vm_refl. Qed.
Lemma D_26ea4c : decode_any W_26ea4c = Some (Branch BC_NE 18 0 8144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea50 : bv 32 := 0x0284b583.
Lemma F_26ea50 : fetch_word Plain.M.loaded_segments (0x26ea98 : word) = Some W_26ea50.
Proof. vm_refl. Qed.
Lemma D_26ea50 : decode_any W_26ea50 = Some (Load SZ8 true 11 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea54 : bv 32 := 0x00b9b023.
Lemma F_26ea54 : fetch_word Plain.M.loaded_segments (0x26ea9c : word) = Some W_26ea54.
Proof. vm_refl. Qed.
Lemma D_26ea54 : decode_any W_26ea54 = Some (Store SZ8 19 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea58 : bv 32 := 0x0d343023.
Lemma F_26ea58 : fetch_word Plain.M.loaded_segments (0x26eaa0 : word) = Some W_26ea58.
Proof. vm_refl. Qed.
Lemma D_26ea58 : decode_any W_26ea58 = Some (Store SZ8 8 19 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea5c : bv 32 := 0x00040513.
Lemma F_26ea5c : fetch_word Plain.M.loaded_segments (0x26eaa4 : word) = Some W_26ea5c.
Proof. vm_refl. Qed.
Lemma D_26ea5c : decode_any W_26ea5c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea60 : bv 32 := 0x03813083.
Lemma F_26ea60 : fetch_word Plain.M.loaded_segments (0x26eaa8 : word) = Some W_26ea60.
Proof. vm_refl. Qed.
Lemma D_26ea60 : decode_any W_26ea60 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea64 : bv 32 := 0x03013403.
Lemma F_26ea64 : fetch_word Plain.M.loaded_segments (0x26eaac : word) = Some W_26ea64.
Proof. vm_refl. Qed.
Lemma D_26ea64 : decode_any W_26ea64 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea68 : bv 32 := 0x02813483.
Lemma F_26ea68 : fetch_word Plain.M.loaded_segments (0x26eab0 : word) = Some W_26ea68.
Proof. vm_refl. Qed.
Lemma D_26ea68 : decode_any W_26ea68 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea6c : bv 32 := 0x02013903.
Lemma F_26ea6c : fetch_word Plain.M.loaded_segments (0x26eab4 : word) = Some W_26ea6c.
Proof. vm_refl. Qed.
Lemma D_26ea6c : decode_any W_26ea6c = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea70 : bv 32 := 0x01813983.
Lemma F_26ea70 : fetch_word Plain.M.loaded_segments (0x26eab8 : word) = Some W_26ea70.
Proof. vm_refl. Qed.
Lemma D_26ea70 : decode_any W_26ea70 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea74 : bv 32 := 0x01013a03.
Lemma F_26ea74 : fetch_word Plain.M.loaded_segments (0x26eabc : word) = Some W_26ea74.
Proof. vm_refl. Qed.
Lemma D_26ea74 : decode_any W_26ea74 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea78 : bv 32 := 0x00813a83.
Lemma F_26ea78 : fetch_word Plain.M.loaded_segments (0x26eac0 : word) = Some W_26ea78.
Proof. vm_refl. Qed.
Lemma D_26ea78 : decode_any W_26ea78 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea7c : bv 32 := 0x04010113.
Lemma F_26ea7c : fetch_word Plain.M.loaded_segments (0x26eac4 : word) = Some W_26ea7c.
Proof. vm_refl. Qed.
Lemma D_26ea7c : decode_any W_26ea7c = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea80 : bv 32 := 0x00008067.
Lemma F_26ea80 : fetch_word Plain.M.loaded_segments (0x26eac8 : word) = Some W_26ea80.
Proof. vm_refl. Qed.
Lemma D_26ea80 : decode_any W_26ea80 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea84 : bv 32 := 0xfc010113.
Lemma F_26ea84 : fetch_word Plain.M.loaded_segments (0x26eacc : word) = Some W_26ea84.
Proof. vm_refl. Qed.
Lemma D_26ea84 : decode_any W_26ea84 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea88 : bv 32 := 0x02113c23.
Lemma F_26ea88 : fetch_word Plain.M.loaded_segments (0x26ead0 : word) = Some W_26ea88.
Proof. vm_refl. Qed.
Lemma D_26ea88 : decode_any W_26ea88 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea8c : bv 32 := 0x02813823.
Lemma F_26ea8c : fetch_word Plain.M.loaded_segments (0x26ead4 : word) = Some W_26ea8c.
Proof. vm_refl. Qed.
Lemma D_26ea8c : decode_any W_26ea8c = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea90 : bv 32 := 0x02913423.
Lemma F_26ea90 : fetch_word Plain.M.loaded_segments (0x26ead8 : word) = Some W_26ea90.
Proof. vm_refl. Qed.
Lemma D_26ea90 : decode_any W_26ea90 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea94 : bv 32 := 0x03213023.
Lemma F_26ea94 : fetch_word Plain.M.loaded_segments (0x26eadc : word) = Some W_26ea94.
Proof. vm_refl. Qed.
Lemma D_26ea94 : decode_any W_26ea94 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea98 : bv 32 := 0x01313c23.
Lemma F_26ea98 : fetch_word Plain.M.loaded_segments (0x26eae0 : word) = Some W_26ea98.
Proof. vm_refl. Qed.
Lemma D_26ea98 : decode_any W_26ea98 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ea9c : bv 32 := 0x01413823.
Lemma F_26ea9c : fetch_word Plain.M.loaded_segments (0x26eae4 : word) = Some W_26ea9c.
Proof. vm_refl. Qed.
Lemma D_26ea9c : decode_any W_26ea9c = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eaa0 : bv 32 := 0x01513423.
Lemma F_26eaa0 : fetch_word Plain.M.loaded_segments (0x26eae8 : word) = Some W_26eaa0.
Proof. vm_refl. Qed.
Lemma D_26eaa0 : decode_any W_26eaa0 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eaa4 : bv 32 := 0x02853683.
Lemma F_26eaa4 : fetch_word Plain.M.loaded_segments (0x26eaec : word) = Some W_26eaa4.
Proof. vm_refl. Qed.
Lemma D_26eaa4 : decode_any W_26eaa4 = Some (Load SZ8 true 13 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eaa8 : bv 32 := 0x000a1597.
Lemma F_26eaa8 : fetch_word Plain.M.loaded_segments (0x26eaf0 : word) = Some W_26eaa8.
Proof. vm_refl. Qed.
Lemma D_26eaa8 : decode_any W_26eaa8 = Some (Auipc 11 161, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eaac : bv 32 := 0x99058593.
Lemma F_26eaac : fetch_word Plain.M.loaded_segments (0x26eaf4 : word) = Some W_26eaac.
Proof. vm_refl. Qed.
Lemma D_26eaac : decode_any W_26eaac = Some (OpImm ALU_ADD 11 11 2448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eab0 : bv 32 := 0x000a1617.
Lemma F_26eab0 : fetch_word Plain.M.loaded_segments (0x26eaf8 : word) = Some W_26eab0.
Proof. vm_refl. Qed.
Lemma D_26eab0 : decode_any W_26eab0 = Some (Auipc 12 161, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eab4 : bv 32 := 0xc1060493.
Lemma F_26eab4 : fetch_word Plain.M.loaded_segments (0x26eafc : word) = Some W_26eab4.
Proof. vm_refl. Qed.
Lemma D_26eab4 : decode_any W_26eab4 = Some (OpImm ALU_ADD 9 12 3088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eab8 : bv 32 := 0x0c068e63.
Lemma F_26eab8 : fetch_word Plain.M.loaded_segments (0x26eb00 : word) = Some W_26eab8.
Proof. vm_refl. Qed.
Lemma D_26eab8 : decode_any W_26eab8 = Some (Branch BC_EQ 13 0 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eabc : bv 32 := 0x00000613.
Lemma F_26eabc : fetch_word Plain.M.loaded_segments (0x26eb04 : word) = Some W_26eabc.
Proof. vm_refl. Qed.
Lemma D_26eabc : decode_any W_26eabc = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eac0 : bv 32 := 0x00000893.
Lemma F_26eac0 : fetch_word Plain.M.loaded_segments (0x26eb08 : word) = Some W_26eac0.
Proof. vm_refl. Qed.
Lemma D_26eac0 : decode_any W_26eac0 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eac4 : bv 32 := 0x0006e717.
Lemma F_26eac4 : fetch_word Plain.M.loaded_segments (0x26eb0c : word) = Some W_26eac4.
Proof. vm_refl. Qed.
Lemma D_26eac4 : decode_any W_26eac4 = Some (Auipc 14 110, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eac8 : bv 32 := 0x01853783.
Lemma F_26eac8 : fetch_word Plain.M.loaded_segments (0x26eb10 : word) = Some W_26eac8.
Proof. vm_refl. Qed.
Lemma D_26eac8 : decode_any W_26eac8 = Some (Load SZ8 true 15 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eacc : bv 32 := 0x02053503.
Lemma F_26eacc : fetch_word Plain.M.loaded_segments (0x26eb14 : word) = Some W_26eacc.
Proof. vm_refl. Qed.
Lemma D_26eacc : decode_any W_26eacc = Some (Load SZ8 true 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ead0 : bv 32 := 0x00600813.
Lemma F_26ead0 : fetch_word Plain.M.loaded_segments (0x26eb18 : word) = Some W_26ead0.
Proof. vm_refl. Qed.
Lemma D_26ead0 : decode_any W_26ead0 = Some (OpImm ALU_ADD 16 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ead4 : bv 32 := 0x0006c297.
Lemma F_26ead4 : fetch_word Plain.M.loaded_segments (0x26eb1c : word) = Some W_26ead4.
Proof. vm_refl. Qed.
Lemma D_26ead4 : decode_any W_26ead4 = Some (Auipc 5 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ead8 : bv 32 := 0xd8476f03.
Lemma F_26ead8 : fetch_word Plain.M.loaded_segments (0x26eb20 : word) = Some W_26ead8.
Proof. vm_refl. Qed.
Lemma D_26ead8 : decode_any W_26ead8 = Some (Load SZ4 false 30 14 3460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eadc : bv 32 := 0x00c2b283.
Lemma F_26eadc : fetch_word Plain.M.loaded_segments (0x26eb24 : word) = Some W_26eadc.
Proof. vm_refl. Qed.
Lemma D_26eadc : decode_any W_26eadc = Some (Load SZ8 true 5 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eae0 : bv 32 := 0x00200313.
Lemma F_26eae0 : fetch_word Plain.M.loaded_segments (0x26eb28 : word) = Some W_26eae0.
Proof. vm_refl. Qed.
Lemma D_26eae0 : decode_any W_26eae0 = Some (OpImm ALU_ADD 6 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eae4 : bv 32 := 0x00700393.
Lemma F_26eae4 : fetch_word Plain.M.loaded_segments (0x26eb2c : word) = Some W_26eae4.
Proof. vm_refl. Qed.
Lemma D_26eae4 : decode_any W_26eae4 = Some (OpImm ALU_ADD 7 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eae8 : bv 32 := 0x6474ee37.
Lemma F_26eae8 : fetch_word Plain.M.loaded_segments (0x26eb30 : word) = Some W_26eae8.
Proof. vm_refl. Qed.
Lemma D_26eae8 : decode_any W_26eae8 = Some (Lui 28 411470, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eaec : bv 32 := 0x551e0e1b.
Lemma F_26eaec : fetch_word Plain.M.loaded_segments (0x26eb34 : word) = Some W_26eaec.
Proof. vm_refl. Qed.
Lemma D_26eaec : decode_any W_26eaec = Some (OpImm32 28 28 1361, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eaf0 : bv 32 := 0x00078e93.
Lemma F_26eaf0 : fetch_word Plain.M.loaded_segments (0x26eb38 : word) = Some W_26eaf0.
Proof. vm_refl. Qed.
Lemma D_26eaf0 : decode_any W_26eaf0 = Some (OpImm ALU_ADD 29 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eaf4 : bv 32 := 0x0180006f.
Lemma F_26eaf4 : fetch_word Plain.M.loaded_segments (0x26eb3c : word) = Some W_26eaf4.
Proof. vm_refl. Qed.
Lemma D_26eaf4 : decode_any W_26eaf4 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eaf8 : bv 32 := 0x010eb603.
Lemma F_26eaf8 : fetch_word Plain.M.loaded_segments (0x26eb40 : word) = Some W_26eaf8.
Proof. vm_refl. Qed.
Lemma D_26eaf8 : decode_any W_26eaf8 = Some (Load SZ8 true 12 29 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eafc : bv 32 := 0x40c78633.
Lemma F_26eafc : fetch_word Plain.M.loaded_segments (0x26eb44 : word) = Some W_26eafc.
Proof. vm_refl. Qed.
Lemma D_26eafc : decode_any W_26eafc = Some (Op ALU_SUB 12 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb00 : bv 32 := 0xfff68693.
Lemma F_26eb00 : fetch_word Plain.M.loaded_segments (0x26eb48 : word) = Some W_26eb00.
Proof. vm_refl. Qed.
Lemma D_26eb00 : decode_any W_26eb00 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb04 : bv 32 := 0x00ae8eb3.
Lemma F_26eb04 : fetch_word Plain.M.loaded_segments (0x26eb4c : word) = Some W_26eb04.
Proof. vm_refl. Qed.
Lemma D_26eb04 : decode_any W_26eb04 = Some (Op ALU_ADD 29 29 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb08 : bv 32 := 0x04068a63.
Lemma F_26eb08 : fetch_word Plain.M.loaded_segments (0x26eb50 : word) = Some W_26eb08.
Proof. vm_refl. Qed.
Lemma D_26eb08 : decode_any W_26eb08 = Some (Branch BC_EQ 13 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb0c : bv 32 := 0x000ea403.
Lemma F_26eb0c : fetch_word Plain.M.loaded_segments (0x26eb54 : word) = Some W_26eb0c.
Proof. vm_refl. Qed.
Lemma D_26eb0c : decode_any W_26eb0c = Some (Load SZ4 true 8 29 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb10 : bv 32 := 0xff0404e3.
Lemma F_26eb10 : fetch_word Plain.M.loaded_segments (0x26eb58 : word) = Some W_26eb10.
Proof. vm_refl. Qed.
Lemma D_26eb10 : decode_any W_26eb10 = Some (Branch BC_EQ 8 16 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb14 : bv 32 := 0x00028a63.
Lemma F_26eb14 : fetch_word Plain.M.loaded_segments (0x26eb5c : word) = Some W_26eb14.
Proof. vm_refl. Qed.
Lemma D_26eb14 : decode_any W_26eb14 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb18 : bv 32 := 0x00641863.
Lemma F_26eb18 : fetch_word Plain.M.loaded_segments (0x26eb60 : word) = Some W_26eb18.
Proof. vm_refl. Qed.
Lemma D_26eb18 : decode_any W_26eb18 = Some (Branch BC_NE 8 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb1c : bv 32 := 0x010eb603.
Lemma F_26eb1c : fetch_word Plain.M.loaded_segments (0x26eb64 : word) = Some W_26eb1c.
Proof. vm_refl. Qed.
Lemma D_26eb1c : decode_any W_26eb1c = Some (Load SZ8 true 12 29 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb20 : bv 32 := 0x40c28633.
Lemma F_26eb20 : fetch_word Plain.M.loaded_segments (0x26eb68 : word) = Some W_26eb20.
Proof. vm_refl. Qed.
Lemma D_26eb20 : decode_any W_26eb20 = Some (Op ALU_SUB 12 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb24 : bv 32 := 0xfddff06f.
Lemma F_26eb24 : fetch_word Plain.M.loaded_segments (0x26eb6c : word) = Some W_26eb24.
Proof. vm_refl. Qed.
Lemma D_26eb24 : decode_any W_26eb24 = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb28 : bv 32 := 0x000e8f93.
Lemma F_26eb28 : fetch_word Plain.M.loaded_segments (0x26eb70 : word) = Some W_26eb28.
Proof. vm_refl. Qed.
Lemma D_26eb28 : decode_any W_26eb28 = Some (OpImm ALU_ADD 31 29 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb2c : bv 32 := 0x00740463.
Lemma F_26eb2c : fetch_word Plain.M.loaded_segments (0x26eb74 : word) = Some W_26eb2c.
Proof. vm_refl. Qed.
Lemma D_26eb2c : decode_any W_26eb2c = Some (Branch BC_EQ 8 7 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb30 : bv 32 := 0x00088f93.
Lemma F_26eb30 : fetch_word Plain.M.loaded_segments (0x26eb78 : word) = Some W_26eb30.
Proof. vm_refl. Qed.
Lemma D_26eb30 : decode_any W_26eb30 = Some (OpImm ALU_ADD 31 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb34 : bv 32 := 0x03c41063.
Lemma F_26eb34 : fetch_word Plain.M.loaded_segments (0x26eb7c : word) = Some W_26eb34.
Proof. vm_refl. Qed.
Lemma D_26eb34 : decode_any W_26eb34 = Some (Branch BC_NE 8 28 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb38 : bv 32 := 0x028eb883.
Lemma F_26eb38 : fetch_word Plain.M.loaded_segments (0x26eb80 : word) = Some W_26eb38.
Proof. vm_refl. Qed.
Lemma D_26eb38 : decode_any W_26eb38 = Some (Load SZ8 true 17 29 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb3c : bv 32 := 0x011f7c63.
Lemma F_26eb3c : fetch_word Plain.M.loaded_segments (0x26eb84 : word) = Some W_26eb3c.
Proof. vm_refl. Qed.
Lemma D_26eb3c : decode_any W_26eb3c = Some (Branch BC_GEU 30 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb40 : bv 32 := 0x00800f37.
Lemma F_26eb40 : fetch_word Plain.M.loaded_segments (0x26eb88 : word) = Some W_26eb40.
Proof. vm_refl. Qed.
Lemma D_26eb40 : decode_any W_26eb40 = Some (Lui 30 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb44 : bv 32 := 0x01e8e463.
Lemma F_26eb44 : fetch_word Plain.M.loaded_segments (0x26eb8c : word) = Some W_26eb44.
Proof. vm_refl. Qed.
Lemma D_26eb44 : decode_any W_26eb44 = Some (Branch BC_LTU 17 30 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb48 : bv 32 := 0x008008b7.
Lemma F_26eb48 : fetch_word Plain.M.loaded_segments (0x26eb90 : word) = Some W_26eb48.
Proof. vm_refl. Qed.
Lemma D_26eb48 : decode_any W_26eb48 = Some (Lui 17 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb4c : bv 32 := 0xd9172223.
Lemma F_26eb4c : fetch_word Plain.M.loaded_segments (0x26eb94 : word) = Some W_26eb4c.
Proof. vm_refl. Qed.
Lemma D_26eb4c : decode_any W_26eb4c = Some (Store SZ4 14 17 3460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb50 : bv 32 := 0x00088f13.
Lemma F_26eb50 : fetch_word Plain.M.loaded_segments (0x26eb98 : word) = Some W_26eb50.
Proof. vm_refl. Qed.
Lemma D_26eb50 : decode_any W_26eb50 = Some (OpImm ALU_ADD 30 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb54 : bv 32 := 0x000f8893.
Lemma F_26eb54 : fetch_word Plain.M.loaded_segments (0x26eb9c : word) = Some W_26eb54.
Proof. vm_refl. Qed.
Lemma D_26eb54 : decode_any W_26eb54 = Some (OpImm ALU_ADD 17 31 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb58 : bv 32 := 0xfa9ff06f.
Lemma F_26eb58 : fetch_word Plain.M.loaded_segments (0x26eba0 : word) = Some W_26eb58.
Proof. vm_refl. Qed.
Lemma D_26eb58 : decode_any W_26eb58 = Some (Jal 0 2097064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb5c : bv 32 := 0x02088c63.
Lemma F_26eb5c : fetch_word Plain.M.loaded_segments (0x26eba4 : word) = Some W_26eb5c.
Proof. vm_refl. Qed.
Lemma D_26eb5c : decode_any W_26eb5c = Some (Branch BC_EQ 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb60 : bv 32 := 0x00858713.
Lemma F_26eb60 : fetch_word Plain.M.loaded_segments (0x26eba8 : word) = Some W_26eb60.
Proof. vm_refl. Qed.
Lemma D_26eb60 : decode_any W_26eb60 = Some (OpImm ALU_ADD 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb64 : bv 32 := 0x0108b783.
Lemma F_26eb64 : fetch_word Plain.M.loaded_segments (0x26ebac : word) = Some W_26eb64.
Proof. vm_refl. Qed.
Lemma D_26eb64 : decode_any W_26eb64 = Some (Load SZ8 true 15 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb68 : bv 32 := 0x0208b803.
Lemma F_26eb68 : fetch_word Plain.M.loaded_segments (0x26ebb0 : word) = Some W_26eb68.
Proof. vm_refl. Qed.
Lemma D_26eb68 : decode_any W_26eb68 = Some (Load SZ8 true 16 17 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb6c : bv 32 := 0x0288b683.
Lemma F_26eb6c : fetch_word Plain.M.loaded_segments (0x26ebb4 : word) = Some W_26eb6c.
Proof. vm_refl. Qed.
Lemma D_26eb6c : decode_any W_26eb6c = Some (Load SZ8 true 13 17 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb70 : bv 32 := 0x0308b503.
Lemma F_26eb70 : fetch_word Plain.M.loaded_segments (0x26ebb8 : word) = Some W_26eb70.
Proof. vm_refl. Qed.
Lemma D_26eb70 : decode_any W_26eb70 = Some (Load SZ8 true 10 17 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb74 : bv 32 := 0x00c78633.
Lemma F_26eb74 : fetch_word Plain.M.loaded_segments (0x26ebbc : word) = Some W_26eb74.
Proof. vm_refl. Qed.
Lemma D_26eb74 : decode_any W_26eb74 = Some (Op ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb78 : bv 32 := 0x00100793.
Lemma F_26eb78 : fetch_word Plain.M.loaded_segments (0x26ebc0 : word) = Some W_26eb78.
Proof. vm_refl. Qed.
Lemma D_26eb78 : decode_any W_26eb78 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb7c : bv 32 := 0x00c5b823.
Lemma F_26eb7c : fetch_word Plain.M.loaded_segments (0x26ebc4 : word) = Some W_26eb7c.
Proof. vm_refl. Qed.
Lemma D_26eb7c : decode_any W_26eb7c = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb80 : bv 32 := 0x0105bc23.
Lemma F_26eb80 : fetch_word Plain.M.loaded_segments (0x26ebc8 : word) = Some W_26eb80.
Proof. vm_refl. Qed.
Lemma D_26eb80 : decode_any W_26eb80 = Some (Store SZ8 11 16 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb84 : bv 32 := 0x02a5b423.
Lemma F_26eb84 : fetch_word Plain.M.loaded_segments (0x26ebcc : word) = Some W_26eb84.
Proof. vm_refl. Qed.
Lemma D_26eb84 : decode_any W_26eb84 = Some (Store SZ8 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb88 : bv 32 := 0x00e4b823.
Lemma F_26eb88 : fetch_word Plain.M.loaded_segments (0x26ebd0 : word) = Some W_26eb88.
Proof. vm_refl. Qed.
Lemma D_26eb88 : decode_any W_26eb88 = Some (Store SZ8 9 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb8c : bv 32 := 0x02f4b423.
Lemma F_26eb8c : fetch_word Plain.M.loaded_segments (0x26ebd4 : word) = Some W_26eb8c.
Proof. vm_refl. Qed.
Lemma D_26eb8c : decode_any W_26eb8c = Some (Store SZ8 9 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb90 : bv 32 := 0x0100006f.
Lemma F_26eb90 : fetch_word Plain.M.loaded_segments (0x26ebd8 : word) = Some W_26eb90.
Proof. vm_refl. Qed.
Lemma D_26eb90 : decode_any W_26eb90 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb94 : bv 32 := 0x0105b603.
Lemma F_26eb94 : fetch_word Plain.M.loaded_segments (0x26ebdc : word) = Some W_26eb94.
Proof. vm_refl. Qed.
Lemma D_26eb94 : decode_any W_26eb94 = Some (Load SZ8 true 12 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb98 : bv 32 := 0x0205b683.
Lemma F_26eb98 : fetch_word Plain.M.loaded_segments (0x26ebe0 : word) = Some W_26eb98.
Proof. vm_refl. Qed.
Lemma D_26eb98 : decode_any W_26eb98 = Some (Load SZ8 true 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eb9c : bv 32 := 0x0285b503.
Lemma F_26eb9c : fetch_word Plain.M.loaded_segments (0x26ebe4 : word) = Some W_26eb9c.
Proof. vm_refl. Qed.
Lemma D_26eb9c : decode_any W_26eb9c = Some (Load SZ8 true 10 11 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eba0 : bv 32 := 0x00c68733.
Lemma F_26eba0 : fetch_word Plain.M.loaded_segments (0x26ebe8 : word) = Some W_26eba0.
Proof. vm_refl. Qed.
Lemma D_26eba0 : decode_any W_26eba0 = Some (Op ALU_ADD 14 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eba4 : bv 32 := 0xfff50793.
Lemma F_26eba4 : fetch_word Plain.M.loaded_segments (0x26ebec : word) = Some W_26eba4.
Proof. vm_refl. Qed.
Lemma D_26eba4 : decode_any W_26eba4 = Some (OpImm ALU_ADD 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eba8 : bv 32 := 0x40e00733.
Lemma F_26eba8 : fetch_word Plain.M.loaded_segments (0x26ebf0 : word) = Some W_26eba8.
Proof. vm_refl. Qed.
Lemma D_26eba8 : decode_any W_26eba8 = Some (Op ALU_SUB 14 0 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebac : bv 32 := 0x00c7f633.
Lemma F_26ebac : fetch_word Plain.M.loaded_segments (0x26ebf4 : word) = Some W_26ebac.
Proof. vm_refl. Qed.
Lemma D_26ebac : decode_any W_26ebac = Some (Op ALU_AND 12 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebb0 : bv 32 := 0x00e7f733.
Lemma F_26ebb0 : fetch_word Plain.M.loaded_segments (0x26ebf8 : word) = Some W_26ebb0.
Proof. vm_refl. Qed.
Lemma D_26ebb0 : decode_any W_26ebb0 = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebb4 : bv 32 := 0x00700793.
Lemma F_26ebb4 : fetch_word Plain.M.loaded_segments (0x26ebfc : word) = Some W_26ebb4.
Proof. vm_refl. Qed.
Lemma D_26ebb4 : decode_any W_26ebb4 = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebb8 : bv 32 := 0x00d706b3.
Lemma F_26ebb8 : fetch_word Plain.M.loaded_segments (0x26ec00 : word) = Some W_26ebb8.
Proof. vm_refl. Qed.
Lemma D_26ebb8 : decode_any W_26ebb8 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebbc : bv 32 := 0x02d5b023.
Lemma F_26ebbc : fetch_word Plain.M.loaded_segments (0x26ec04 : word) = Some W_26ebbc.
Proof. vm_refl. Qed.
Lemma D_26ebbc : decode_any W_26ebbc = Some (Store SZ8 11 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebc0 : bv 32 := 0x02c5b823.
Lemma F_26ebc0 : fetch_word Plain.M.loaded_segments (0x26ec08 : word) = Some W_26ebc0.
Proof. vm_refl. Qed.
Lemma D_26ebc0 : decode_any W_26ebc0 = Some (Store SZ8 11 12 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebc4 : bv 32 := 0x00a7e663.
Lemma F_26ebc4 : fetch_word Plain.M.loaded_segments (0x26ec0c : word) = Some W_26ebc4.
Proof. vm_refl. Qed.
Lemma D_26ebc4 : decode_any W_26ebc4 = Some (Branch BC_LTU 15 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebc8 : bv 32 := 0x00800513.
Lemma F_26ebc8 : fetch_word Plain.M.loaded_segments (0x26ec10 : word) = Some W_26ebc8.
Proof. vm_refl. Qed.
Lemma D_26ebc8 : decode_any W_26ebc8 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebcc : bv 32 := 0x02a5b423.
Lemma F_26ebcc : fetch_word Plain.M.loaded_segments (0x26ec14 : word) = Some W_26ebcc.
Proof. vm_refl. Qed.
Lemma D_26ebcc : decode_any W_26ebcc = Some (Store SZ8 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebd0 : bv 32 := 0x00d60633.
Lemma F_26ebd0 : fetch_word Plain.M.loaded_segments (0x26ec18 : word) = Some W_26ebd0.
Proof. vm_refl. Qed.
Lemma D_26ebd0 : decode_any W_26ebd0 = Some (Op ALU_ADD 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebd4 : bv 32 := 0x000205b7.
Lemma F_26ebd4 : fetch_word Plain.M.loaded_segments (0x26ec1c : word) = Some W_26ebd4.
Proof. vm_refl. Qed.
Lemma D_26ebd4 : decode_any W_26ebd4 = Some (Lui 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebd8 : bv 32 := 0x00a60633.
Lemma F_26ebd8 : fetch_word Plain.M.loaded_segments (0x26ec20 : word) = Some W_26ebd8.
Proof. vm_refl. Qed.
Lemma D_26ebd8 : decode_any W_26ebd8 = Some (Op ALU_ADD 12 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebdc : bv 32 := 0x0d15869b.
Lemma F_26ebdc : fetch_word Plain.M.loaded_segments (0x26ec24 : word) = Some W_26ebdc.
Proof. vm_refl. Qed.
Lemma D_26ebdc : decode_any W_26ebdc = Some (OpImm32 13 11 209, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebe0 : bv 32 := 0x0df60593.
Lemma F_26ebe0 : fetch_word Plain.M.loaded_segments (0x26ec28 : word) = Some W_26ebe0.
Proof. vm_refl. Qed.
Lemma D_26ebe0 : decode_any W_26ebe0 = Some (OpImm ALU_ADD 11 12 223, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebe4 : bv 32 := 0xff85f593.
Lemma F_26ebe4 : fetch_word Plain.M.loaded_segments (0x26ec2c : word) = Some W_26ebe4.
Proof. vm_refl. Qed.
Lemma D_26ebe4 : decode_any W_26ebe4 = Some (OpImm ALU_AND 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebe8 : bv 32 := 0x00b4bc23.
Lemma F_26ebe8 : fetch_word Plain.M.loaded_segments (0x26ec30 : word) = Some W_26ebe8.
Proof. vm_refl. Qed.
Lemma D_26ebe8 : decode_any W_26ebe8 = Some (Store SZ8 9 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebec : bv 32 := 0x02a4b023.
Lemma F_26ebec : fetch_word Plain.M.loaded_segments (0x26ec34 : word) = Some W_26ebec.
Proof. vm_refl. Qed.
Lemma D_26ebec : decode_any W_26ebec = Some (Store SZ8 9 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebf0 : bv 32 := 0x02d5ea63.
Lemma F_26ebf0 : fetch_word Plain.M.loaded_segments (0x26ec38 : word) = Some W_26ebf0.
Proof. vm_refl. Qed.
Lemma D_26ebf0 : decode_any W_26ebf0 = Some (Branch BC_LTU 11 13 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebf4 : bv 32 := 0xffe03597.
Lemma F_26ebf4 : fetch_word Plain.M.loaded_segments (0x26ec3c : word) = Some W_26ebf4.
Proof. vm_refl. Qed.
Lemma D_26ebf4 : decode_any W_26ebf4 = Some (Auipc 11 1048067, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebf8 : bv 32 := 0x04000893.
Lemma F_26ebf8 : fetch_word Plain.M.loaded_segments (0x26ec40 : word) = Some W_26ebf8.
Proof. vm_refl. Qed.
Lemma D_26ebf8 : decode_any W_26ebf8 = Some (OpImm ALU_ADD 17 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebfc : bv 32 := 0x00200513.
Lemma F_26ebfc : fetch_word Plain.M.loaded_segments (0x26ec44 : word) = Some W_26ebfc.
Proof. vm_refl. Qed.
Lemma D_26ebfc : decode_any W_26ebfc = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec00 : bv 32 := 0x27058593.
Lemma F_26ec00 : fetch_word Plain.M.loaded_segments (0x26ec48 : word) = Some W_26ec00.
Proof. vm_refl. Qed.
Lemma D_26ec00 : decode_any W_26ec00 = Some (OpImm ALU_ADD 11 11 624, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec04 : bv 32 := 0x05b00613.
Lemma F_26ec04 : fetch_word Plain.M.loaded_segments (0x26ec4c : word) = Some W_26ec04.
Proof. vm_refl. Qed.
Lemma D_26ec04 : decode_any W_26ec04 = Some (OpImm ALU_ADD 12 0 91, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec08 : bv 32 := 0x00000073.
Lemma F_26ec08 : fetch_word Plain.M.loaded_segments (0x26ec50 : word) = Some W_26ec08.
Proof. vm_refl. Qed.
Lemma D_26ec08 : decode_any W_26ec08 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_26ec08 : is_ecall W_26ec08 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26ec0c : bv 32 := 0x00000023.
Lemma F_26ec0c : fetch_word Plain.M.loaded_segments (0x26ec54 : word) = Some W_26ec0c.
Proof. vm_refl. Qed.
Lemma D_26ec0c : decode_any W_26ec0c = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec10 : bv 32 := 0x05e00893.
Lemma F_26ec10 : fetch_word Plain.M.loaded_segments (0x26ec58 : word) = Some W_26ec10.
Proof. vm_refl. Qed.
Lemma D_26ec10 : decode_any W_26ec10 = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec14 : bv 32 := 0x07f00513.
Lemma F_26ec14 : fetch_word Plain.M.loaded_segments (0x26ec5c : word) = Some W_26ec14.
Proof. vm_refl. Qed.
Lemma D_26ec14 : decode_any W_26ec14 = Some (OpImm ALU_ADD 10 0 127, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec18 : bv 32 := 0x00000073.
Lemma F_26ec18 : fetch_word Plain.M.loaded_segments (0x26ec60 : word) = Some W_26ec18.
Proof. vm_refl. Qed.
Lemma D_26ec18 : decode_any W_26ec18 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_26ec18 : is_ecall W_26ec18 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26ec1c : bv 32 := 0x0184b583.
Lemma F_26ec1c : fetch_word Plain.M.loaded_segments (0x26ec64 : word) = Some W_26ec1c.
Proof. vm_refl. Qed.
Lemma D_26ec1c : decode_any W_26ec1c = Some (Load SZ8 true 11 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec20 : bv 32 := 0x0204b503.
Lemma F_26ec20 : fetch_word Plain.M.loaded_segments (0x26ec68 : word) = Some W_26ec20.
Proof. vm_refl. Qed.
Lemma D_26ec20 : decode_any W_26ec20 = Some (Load SZ8 true 10 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec24 : bv 32 := 0x00080697.
Lemma F_26ec24 : fetch_word Plain.M.loaded_segments (0x26ec6c : word) = Some W_26ec24.
Proof. vm_refl. Qed.
Lemma D_26ec24 : decode_any W_26ec24 = Some (Auipc 13 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec28 : bv 32 := 0x0104b983.
Lemma F_26ec28 : fetch_word Plain.M.loaded_segments (0x26ec70 : word) = Some W_26ec28.
Proof. vm_refl. Qed.
Lemma D_26ec28 : decode_any W_26ec28 = Some (Load SZ8 true 19 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec2c : bv 32 := 0x0284b603.
Lemma F_26ec2c : fetch_word Plain.M.loaded_segments (0x26ec74 : word) = Some W_26ec2c.
Proof. vm_refl. Qed.
Lemma D_26ec2c : decode_any W_26ec2c = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec30 : bv 32 := 0xfff50713.
Lemma F_26ec30 : fetch_word Plain.M.loaded_segments (0x26ec78 : word) = Some W_26ec30.
Proof. vm_refl. Qed.
Lemma D_26ec30 : decode_any W_26ec30 = Some (OpImm ALU_ADD 14 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec34 : bv 32 := 0xf3800793.
Lemma F_26ec34 : fetch_word Plain.M.loaded_segments (0x26ec7c : word) = Some W_26ec34.
Proof. vm_refl. Qed.
Lemma D_26ec34 : decode_any W_26ec34 = Some (OpImm ALU_ADD 15 0 3896, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec38 : bv 32 := 0x74468513.
Lemma F_26ec38 : fetch_word Plain.M.loaded_segments (0x26ec80 : word) = Some W_26ec38.
Proof. vm_refl. Qed.
Lemma D_26ec38 : decode_any W_26ec38 = Some (OpImm ALU_ADD 10 13 1860, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec3c : bv 32 := 0x40a787b3.
Lemma F_26ec3c : fetch_word Plain.M.loaded_segments (0x26ec84 : word) = Some W_26ec3c.
Proof. vm_refl. Qed.
Lemma D_26ec3c : decode_any W_26ec3c = Some (Op ALU_SUB 15 15 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec40 : bv 32 := 0x00f77733.
Lemma F_26ec40 : fetch_word Plain.M.loaded_segments (0x26ec88 : word) = Some W_26ec40.
Proof. vm_refl. Qed.
Lemma D_26ec40 : decode_any W_26ec40 = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec44 : bv 32 := 0xfff64693.
Lemma F_26ec44 : fetch_word Plain.M.loaded_segments (0x26ec8c : word) = Some W_26ec44.
Proof. vm_refl. Qed.
Lemma D_26ec44 : decode_any W_26ec44 = Some (OpImm ALU_XOR 13 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec48 : bv 32 := 0x00e50933.
Lemma F_26ec48 : fetch_word Plain.M.loaded_segments (0x26ec90 : word) = Some W_26ec48.
Proof. vm_refl. Qed.
Lemma D_26ec48 : decode_any W_26ec48 = Some (Op ALU_ADD 18 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec4c : bv 32 := 0x00369693.
Lemma F_26ec4c : fetch_word Plain.M.loaded_segments (0x26ec94 : word) = Some W_26ec4c.
Proof. vm_refl. Qed.
Lemma D_26ec4c : decode_any W_26ec4c = Some (ShiftImm ALU_SLL 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec50 : bv 32 := 0x00d506b3.
Lemma F_26ec50 : fetch_word Plain.M.loaded_segments (0x26ec98 : word) = Some W_26ec50.
Proof. vm_refl. Qed.
Lemma D_26ec50 : decode_any W_26ec50 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec54 : bv 32 := 0x00b68a33.
Lemma F_26ec54 : fetch_word Plain.M.loaded_segments (0x26ec9c : word) = Some W_26ec54.
Proof. vm_refl. Qed.
Lemma D_26ec54 : decode_any W_26ec54 = Some (Op ALU_ADD 20 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec58 : bv 32 := 0x0c890413.
Lemma F_26ec58 : fetch_word Plain.M.loaded_segments (0x26eca0 : word) = Some W_26ec58.
Proof. vm_refl. Qed.
Lemma D_26ec58 : decode_any W_26ec58 = Some (OpImm ALU_ADD 8 18 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec5c : bv 32 := 0x04098463.
Lemma F_26ec5c : fetch_word Plain.M.loaded_segments (0x26eca4 : word) = Some W_26ec5c.
Proof. vm_refl. Qed.
Lemma D_26ec5c : decode_any W_26ec5c = Some (Branch BC_EQ 19 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec60 : bv 32 := 0x00361613.
Lemma F_26ec60 : fetch_word Plain.M.loaded_segments (0x26eca8 : word) = Some W_26ec60.
Proof. vm_refl. Qed.
Lemma D_26ec60 : decode_any W_26ec60 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec64 : bv 32 := 0x40c50533.
Lemma F_26ec64 : fetch_word Plain.M.loaded_segments (0x26ecac : word) = Some W_26ec64.
Proof. vm_refl. Qed.
Lemma D_26ec64 : decode_any W_26ec64 = Some (Op ALU_SUB 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec68 : bv 32 := 0x00b50ab3.
Lemma F_26ec68 : fetch_word Plain.M.loaded_segments (0x26ecb0 : word) = Some W_26ec68.
Proof. vm_refl. Qed.
Lemma D_26ec68 : decode_any W_26ec68 = Some (Op ALU_ADD 21 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec6c : bv 32 := 0x0289b503.
Lemma F_26ec6c : fetch_word Plain.M.loaded_segments (0x26ecb4 : word) = Some W_26ec6c.
Proof. vm_refl. Qed.
Lemma D_26ec6c : decode_any W_26ec6c = Some (Load SZ8 true 10 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec70 : bv 32 := 0x00a40533.
Lemma F_26ec70 : fetch_word Plain.M.loaded_segments (0x26ecb8 : word) = Some W_26ec70.
Proof. vm_refl. Qed.
Lemma D_26ec70 : decode_any W_26ec70 = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec74 : bv 32 := 0x7ff50513.
Lemma F_26ec74 : fetch_word Plain.M.loaded_segments (0x26ecbc : word) = Some W_26ec74.
Proof. vm_refl. Qed.
Lemma D_26ec74 : decode_any W_26ec74 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec78 : bv 32 := 0x00150513.
Lemma F_26ec78 : fetch_word Plain.M.loaded_segments (0x26ecc0 : word) = Some W_26ec78.
Proof. vm_refl. Qed.
Lemma D_26ec78 : decode_any W_26ec78 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec7c : bv 32 := 0x00aab023.
Lemma F_26ec7c : fetch_word Plain.M.loaded_segments (0x26ecc4 : word) = Some W_26ec7c.
Proof. vm_refl. Qed.
Lemma D_26ec7c : decode_any W_26ec7c = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec80 : bv 32 := 0x0289b503.
Lemma F_26ec80 : fetch_word Plain.M.loaded_segments (0x26ecc8 : word) = Some W_26ec80.
Proof. vm_refl. Qed.
Lemma D_26ec80 : decode_any W_26ec80 = Some (Load SZ8 true 10 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec84 : bv 32 := 0x0089b583.
Lemma F_26ec84 : fetch_word Plain.M.loaded_segments (0x26eccc : word) = Some W_26ec84.
Proof. vm_refl. Qed.
Lemma D_26ec84 : decode_any W_26ec84 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec88 : bv 32 := 0x0109b603.
Lemma F_26ec88 : fetch_word Plain.M.loaded_segments (0x26ecd0 : word) = Some W_26ec88.
Proof. vm_refl. Qed.
Lemma D_26ec88 : decode_any W_26ec88 = Some (Load SZ8 true 12 19 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec8c : bv 32 := 0x00a40533.
Lemma F_26ec8c : fetch_word Plain.M.loaded_segments (0x26ecd4 : word) = Some W_26ec8c.
Proof. vm_refl. Qed.
Lemma D_26ec8c : decode_any W_26ec8c = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec90 : bv 32 := 0x3e50a0ef.
Lemma F_26ec90 : fetch_word Plain.M.loaded_segments (0x26ecd8 : word) = Some W_26ec90.
Proof. vm_refl. Qed.
Lemma D_26ec90 : decode_any W_26ec90 = Some (Jal 1 44004, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec94 : bv 32 := 0x0009b983.
Lemma F_26ec94 : fetch_word Plain.M.loaded_segments (0x26ecdc : word) = Some W_26ec94.
Proof. vm_refl. Qed.
Lemma D_26ec94 : decode_any W_26ec94 = Some (Load SZ8 true 19 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec98 : bv 32 := 0x008a8a93.
Lemma F_26ec98 : fetch_word Plain.M.loaded_segments (0x26ece0 : word) = Some W_26ec98.
Proof. vm_refl. Qed.
Lemma D_26ec98 : decode_any W_26ec98 = Some (OpImm ALU_ADD 21 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ec9c : bv 32 := 0xfc0998e3.
Lemma F_26ec9c : fetch_word Plain.M.loaded_segments (0x26ece4 : word) = Some W_26ec9c.
Proof. vm_refl. Qed.
Lemma D_26ec9c : decode_any W_26ec9c = Some (Branch BC_NE 19 0 8144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eca0 : bv 32 := 0x0284b603.
Lemma F_26eca0 : fetch_word Plain.M.loaded_segments (0x26ece8 : word) = Some W_26eca0.
Proof. vm_refl. Qed.
Lemma D_26eca0 : decode_any W_26eca0 = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eca4 : bv 32 := 0x00ca3023.
Lemma F_26eca4 : fetch_word Plain.M.loaded_segments (0x26ecec : word) = Some W_26eca4.
Proof. vm_refl. Qed.
Lemma D_26eca4 : decode_any W_26eca4 = Some (Store SZ8 20 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eca8 : bv 32 := 0x0d493023.
Lemma F_26eca8 : fetch_word Plain.M.loaded_segments (0x26ecf0 : word) = Some W_26eca8.
Proof. vm_refl. Qed.
Lemma D_26eca8 : decode_any W_26eca8 = Some (Store SZ8 18 20 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ecac : bv 32 := 0x01293023.
Lemma F_26ecac : fetch_word Plain.M.loaded_segments (0x26ecf4 : word) = Some W_26ecac.
Proof. vm_refl. Qed.
Lemma D_26ecac : decode_any W_26ecac = Some (Store SZ8 18 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ecb0 : bv 32 := 0x00040513.
Lemma F_26ecb0 : fetch_word Plain.M.loaded_segments (0x26ecf8 : word) = Some W_26ecb0.
Proof. vm_refl. Qed.
Lemma D_26ecb0 : decode_any W_26ecb0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ecb4 : bv 32 := 0x2f50e0ef.
Lemma F_26ecb4 : fetch_word Plain.M.loaded_segments (0x26ecfc : word) = Some W_26ecb4.
Proof. vm_refl. Qed.
Lemma D_26ecb4 : decode_any W_26ecb4 = Some (Jal 1 60148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ecb8 : bv 32 := 0x04054a63.
Lemma F_26ecb8 : fetch_word Plain.M.loaded_segments (0x26ed00 : word) = Some W_26ecb8.
Proof. vm_refl. Qed.
Lemma D_26ecb8 : decode_any W_26ecb8 = Some (Branch BC_LT 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ecbc : bv 32 := 0x00051663.
Lemma F_26ecbc : fetch_word Plain.M.loaded_segments (0x26ed04 : word) = Some W_26ecbc.
Proof. vm_refl. Qed.
Lemma D_26ecbc : decode_any W_26ecbc = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ecc0 : bv 32 := 0x00100513.
Lemma F_26ecc0 : fetch_word Plain.M.loaded_segments (0x26ed08 : word) = Some W_26ecc0.
Proof. vm_refl. Qed.
Lemma D_26ecc0 : decode_any W_26ecc0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ecc4 : bv 32 := 0x00a48023.
Lemma F_26ecc4 : fetch_word Plain.M.loaded_segments (0x26ed0c : word) = Some W_26ecc4.
Proof. vm_refl. Qed.
Lemma D_26ecc4 : decode_any W_26ecc4 = Some (Store SZ1 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ecc8 : bv 32 := 0x00200513.
Lemma F_26ecc8 : fetch_word Plain.M.loaded_segments (0x26ed10 : word) = Some W_26ecc8.
Proof. vm_refl. Qed.
Lemma D_26ecc8 : decode_any W_26ecc8 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eccc : bv 32 := 0x000a0597.
Lemma F_26eccc : fetch_word Plain.M.loaded_segments (0x26ed14 : word) = Some W_26eccc.
Proof. vm_refl. Qed.
Lemma D_26eccc : decode_any W_26eccc = Some (Auipc 11 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ecd0 : bv 32 := 0x02a92423.
Lemma F_26ecd0 : fetch_word Plain.M.loaded_segments (0x26ed18 : word) = Some W_26ecd0.
Proof. vm_refl. Qed.
Lemma D_26ecd0 : decode_any W_26ecd0 = Some (Store SZ4 18 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ecd4 : bv 32 := 0x06000893.
Lemma F_26ecd4 : fetch_word Plain.M.loaded_segments (0x26ed1c : word) = Some W_26ecd4.
Proof. vm_refl. Qed.
Lemma D_26ecd4 : decode_any W_26ecd4 = Some (OpImm ALU_ADD 17 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ecd8 : bv 32 := 0x76c58513.
Lemma F_26ecd8 : fetch_word Plain.M.loaded_segments (0x26ed20 : word) = Some W_26ecd8.
Proof. vm_refl. Qed.
Lemma D_26ecd8 : decode_any W_26ecd8 = Some (OpImm ALU_ADD 10 11 1900, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ecdc : bv 32 := 0x03848593.
Lemma F_26ecdc : fetch_word Plain.M.loaded_segments (0x26ed24 : word) = Some W_26ecdc.
Proof. vm_refl. Qed.
Lemma D_26ecdc : decode_any W_26ecdc = Some (OpImm ALU_ADD 11 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ece0 : bv 32 := 0x00000073.
Lemma F_26ece0 : fetch_word Plain.M.loaded_segments (0x26ed28 : word) = Some W_26ece0.
Proof. vm_refl. Qed.
Lemma D_26ece0 : decode_any W_26ece0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_26ece0 : is_ecall W_26ece0 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26ece4 : bv 32 := 0x07890613.
Lemma F_26ece4 : fetch_word Plain.M.loaded_segments (0x26ed2c : word) = Some W_26ece4.
Proof. vm_refl. Qed.
Lemma D_26ece4 : decode_any W_26ece4 = Some (OpImm ALU_ADD 12 18 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ece8 : bv 32 := 0x02a92023.
Lemma F_26ece8 : fetch_word Plain.M.loaded_segments (0x26ed30 : word) = Some W_26ece8.
Proof. vm_refl. Qed.
Lemma D_26ece8 : decode_any W_26ece8 = Some (Store SZ4 18 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ecec : bv 32 := 0x08b93c23.
Lemma F_26ecec : fetch_word Plain.M.loaded_segments (0x26ed34 : word) = Some W_26ecec.
Proof. vm_refl. Qed.
Lemma D_26ecec : decode_any W_26ecec = Some (Store SZ8 18 11 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ecf0 : bv 32 := 0x06c93c23.
Lemma F_26ecf0 : fetch_word Plain.M.loaded_segments (0x26ed38 : word) = Some W_26ecf0.
Proof. vm_refl. Qed.
Lemma D_26ecf0 : decode_any W_26ecf0 = Some (Store SZ8 18 12 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ecf4 : bv 32 := 0x000a1517.
Lemma F_26ecf4 : fetch_word Plain.M.loaded_segments (0x26ed3c : word) = Some W_26ecf4.
Proof. vm_refl. Qed.
Lemma D_26ecf4 : decode_any W_26ecf4 = Some (Auipc 10 161, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ecf8 : bv 32 := 0x9b453503.
Lemma F_26ecf8 : fetch_word Plain.M.loaded_segments (0x26ed40 : word) = Some W_26ecf8.
Proof. vm_refl. Qed.
Lemma D_26ecf8 : decode_any W_26ecf8 = Some (Load SZ8 true 10 10 2484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ecfc : bv 32 := 0x01293423.
Lemma F_26ecfc : fetch_word Plain.M.loaded_segments (0x26ed44 : word) = Some W_26ecfc.
Proof. vm_refl. Qed.
Lemma D_26ecfc : decode_any W_26ecfc = Some (Store SZ8 18 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed00 : bv 32 := 0x01293823.
Lemma F_26ed00 : fetch_word Plain.M.loaded_segments (0x26ed48 : word) = Some W_26ed00.
Proof. vm_refl. Qed.
Lemma D_26ed00 : decode_any W_26ed00 = Some (Store SZ8 18 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed04 : bv 32 := 0x00a93c23.
Lemma F_26ed04 : fetch_word Plain.M.loaded_segments (0x26ed4c : word) = Some W_26ed04.
Proof. vm_refl. Qed.
Lemma D_26ed04 : decode_any W_26ed04 = Some (Store SZ8 18 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed08 : bv 32 := 0x0080006f.
Lemma F_26ed08 : fetch_word Plain.M.loaded_segments (0x26ed50 : word) = Some W_26ed08.
Proof. vm_refl. Qed.
Lemma D_26ed08 : decode_any W_26ed08 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed0c : bv 32 := 0x00000023.
Lemma F_26ed0c : fetch_word Plain.M.loaded_segments (0x26ed54 : word) = Some W_26ed0c.
Proof. vm_refl. Qed.
Lemma D_26ed0c : decode_any W_26ed0c = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed10 : bv 32 := 0x03813083.
Lemma F_26ed10 : fetch_word Plain.M.loaded_segments (0x26ed58 : word) = Some W_26ed10.
Proof. vm_refl. Qed.
Lemma D_26ed10 : decode_any W_26ed10 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed14 : bv 32 := 0x03013403.
Lemma F_26ed14 : fetch_word Plain.M.loaded_segments (0x26ed5c : word) = Some W_26ed14.
Proof. vm_refl. Qed.
Lemma D_26ed14 : decode_any W_26ed14 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed18 : bv 32 := 0x02813483.
Lemma F_26ed18 : fetch_word Plain.M.loaded_segments (0x26ed60 : word) = Some W_26ed18.
Proof. vm_refl. Qed.
Lemma D_26ed18 : decode_any W_26ed18 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed1c : bv 32 := 0x02013903.
Lemma F_26ed1c : fetch_word Plain.M.loaded_segments (0x26ed64 : word) = Some W_26ed1c.
Proof. vm_refl. Qed.
Lemma D_26ed1c : decode_any W_26ed1c = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed20 : bv 32 := 0x01813983.
Lemma F_26ed20 : fetch_word Plain.M.loaded_segments (0x26ed68 : word) = Some W_26ed20.
Proof. vm_refl. Qed.
Lemma D_26ed20 : decode_any W_26ed20 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed24 : bv 32 := 0x01013a03.
Lemma F_26ed24 : fetch_word Plain.M.loaded_segments (0x26ed6c : word) = Some W_26ed24.
Proof. vm_refl. Qed.
Lemma D_26ed24 : decode_any W_26ed24 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed28 : bv 32 := 0x00813a83.
Lemma F_26ed28 : fetch_word Plain.M.loaded_segments (0x26ed70 : word) = Some W_26ed28.
Proof. vm_refl. Qed.
Lemma D_26ed28 : decode_any W_26ed28 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed2c : bv 32 := 0x04010113.
Lemma F_26ed2c : fetch_word Plain.M.loaded_segments (0x26ed74 : word) = Some W_26ed2c.
Proof. vm_refl. Qed.
Lemma D_26ed2c : decode_any W_26ed2c = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed30 : bv 32 := 0x00008067.
Lemma F_26ed30 : fetch_word Plain.M.loaded_segments (0x26ed78 : word) = Some W_26ed30.
Proof. vm_refl. Qed.
Lemma D_26ed30 : decode_any W_26ed30 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition W_26ed40 : bv 32 := 0xff010113.
Lemma F_26ed40 : fetch_word Plain.M.loaded_segments (0x26ed7c : word) = Some W_26ed40.
Proof. vm_refl. Qed.
Lemma D_26ed40 : decode_any W_26ed40 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed44 : bv 32 := 0x00113423.
Lemma F_26ed44 : fetch_word Plain.M.loaded_segments (0x26ed80 : word) = Some W_26ed44.
Proof. vm_refl. Qed.
Lemma D_26ed44 : decode_any W_26ed44 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed48 : bv 32 := 0x00050e63.
Lemma F_26ed48 : fetch_word Plain.M.loaded_segments (0x26ed84 : word) = Some W_26ed48.
Proof. vm_refl. Qed.
Lemma D_26ed48 : decode_any W_26ed48 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed4c : bv 32 := 0x00050593.
Lemma F_26ed4c : fetch_word Plain.M.loaded_segments (0x26ed88 : word) = Some W_26ed4c.
Proof. vm_refl. Qed.
Lemma D_26ed4c : decode_any W_26ed4c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed50 : bv 32 := 0x0006c517.
Lemma F_26ed50 : fetch_word Plain.M.loaded_segments (0x26ed8c : word) = Some W_26ed50.
Proof. vm_refl. Qed.
Lemma D_26ed50 : decode_any W_26ed50 = Some (Auipc 10 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed54 : bv 32 := 0x39453503.
Lemma F_26ed54 : fetch_word Plain.M.loaded_segments (0x26ed90 : word) = Some W_26ed54.
Proof. vm_refl. Qed.
Lemma D_26ed54 : decode_any W_26ed54 = Some (Load SZ8 true 10 10 916, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed58 : bv 32 := 0x00800613.
Lemma F_26ed58 : fetch_word Plain.M.loaded_segments (0x26ed94 : word) = Some W_26ed58.
Proof. vm_refl. Qed.
Lemma D_26ed58 : decode_any W_26ed58 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed5c : bv 32 := 0x3250a0ef.
Lemma F_26ed5c : fetch_word Plain.M.loaded_segments (0x26ed98 : word) = Some W_26ed5c.
Proof. vm_refl. Qed.
Lemma D_26ed5c : decode_any W_26ed5c = Some (Jal 1 43812, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed60 : bv 32 := 0x01c0006f.
Lemma F_26ed60 : fetch_word Plain.M.loaded_segments (0x26ed9c : word) = Some W_26ed60.
Proof. vm_refl. Qed.
Lemma D_26ed60 : decode_any W_26ed60 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed64 : bv 32 := 0x0006c517.
Lemma F_26ed64 : fetch_word Plain.M.loaded_segments (0x26eda0 : word) = Some W_26ed64.
Proof. vm_refl. Qed.
Lemma D_26ed64 : decode_any W_26ed64 = Some (Auipc 10 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed68 : bv 32 := 0x38053503.
Lemma F_26ed68 : fetch_word Plain.M.loaded_segments (0x26eda4 : word) = Some W_26ed68.
Proof. vm_refl. Qed.
Lemma D_26ed68 : decode_any W_26ed68 = Some (Load SZ8 true 10 10 896, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed6c : bv 32 := 0x41c655b7.
Lemma F_26ed6c : fetch_word Plain.M.loaded_segments (0x26eda8 : word) = Some W_26ed6c.
Proof. vm_refl. Qed.
Lemma D_26ed6c : decode_any W_26ed6c = Some (Lui 11 269413, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed70 : bv 32 := 0xe6d5859b.
Lemma F_26ed70 : fetch_word Plain.M.loaded_segments (0x26edac : word) = Some W_26ed70.
Proof. vm_refl. Qed.
Lemma D_26ed70 : decode_any W_26ed70 = Some (OpImm32 11 11 3693, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed74 : bv 32 := 0x02b505b3.
Lemma F_26ed74 : fetch_word Plain.M.loaded_segments (0x26edb0 : word) = Some W_26ed74.
Proof. vm_refl. Qed.
Lemma D_26ed74 : decode_any W_26ed74 = Some (Mul M_MUL 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed78 : bv 32 := 0x00b53023.
Lemma F_26ed78 : fetch_word Plain.M.loaded_segments (0x26edb4 : word) = Some W_26ed78.
Proof. vm_refl. Qed.
Lemma D_26ed78 : decode_any W_26ed78 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed7c : bv 32 := 0x0006c517.
Lemma F_26ed7c : fetch_word Plain.M.loaded_segments (0x26edb8 : word) = Some W_26ed7c.
Proof. vm_refl. Qed.
Lemma D_26ed7c : decode_any W_26ed7c = Some (Auipc 10 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed80 : bv 32 := 0x36853503.
Lemma F_26ed80 : fetch_word Plain.M.loaded_segments (0x26edbc : word) = Some W_26ed80.
Proof. vm_refl. Qed.
Lemma D_26ed80 : decode_any W_26ed80 = Some (Load SZ8 true 10 10 872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed84 : bv 32 := 0x000500a3.
Lemma F_26ed84 : fetch_word Plain.M.loaded_segments (0x26edc0 : word) = Some W_26ed84.
Proof. vm_refl. Qed.
Lemma D_26ed84 : decode_any W_26ed84 = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed88 : bv 32 := 0x00053503.
Lemma F_26ed88 : fetch_word Plain.M.loaded_segments (0x26edc4 : word) = Some W_26ed88.
Proof. vm_refl. Qed.
Lemma D_26ed88 : decode_any W_26ed88 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed8c : bv 32 := 0x00020593.
Lemma F_26ed8c : fetch_word Plain.M.loaded_segments (0x26edc8 : word) = Some W_26ed8c.
Proof. vm_refl. Qed.
Lemma D_26ed8c : decode_any W_26ed8c = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed90 : bv 32 := 0xfea5b823.
Lemma F_26ed90 : fetch_word Plain.M.loaded_segments (0x26edcc : word) = Some W_26ed90.
Proof. vm_refl. Qed.
Lemma D_26ed90 : decode_any W_26ed90 = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed94 : bv 32 := 0x00813083.
Lemma F_26ed94 : fetch_word Plain.M.loaded_segments (0x26edd0 : word) = Some W_26ed94.
Proof. vm_refl. Qed.
Lemma D_26ed94 : decode_any W_26ed94 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed98 : bv 32 := 0x01010113.
Lemma F_26ed98 : fetch_word Plain.M.loaded_segments (0x26edd4 : word) = Some W_26ed98.
Proof. vm_refl. Qed.
Lemma D_26ed98 : decode_any W_26ed98 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed9c : bv 32 := 0x00008067.
Lemma F_26ed9c : fetch_word Plain.M.loaded_segments (0x26edd8 : word) = Some W_26ed9c.
Proof. vm_refl. Qed.
Lemma D_26ed9c : decode_any W_26ed9c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eda0 : bv 32 := 0x00000023.
Lemma F_26eda0 : fetch_word Plain.M.loaded_segments (0x26eddc : word) = Some W_26eda0.
Proof. vm_refl. Qed.
Lemma D_26eda0 : decode_any W_26eda0 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eda4 : bv 32 := 0x00008067.
Lemma F_26eda4 : fetch_word Plain.M.loaded_segments (0x26ede0 : word) = Some W_26eda4.
Proof. vm_refl. Qed.
Lemma D_26eda4 : decode_any W_26eda4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eda8 : bv 32 := 0x00020513.
Lemma F_26eda8 : fetch_word Plain.M.loaded_segments (0x26ede4 : word) = Some W_26eda8.
Proof. vm_refl. Qed.
Lemma D_26eda8 : decode_any W_26eda8 = Some (OpImm ALU_ADD 10 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26edac : bv 32 := 0xf5c50513.
Lemma F_26edac : fetch_word Plain.M.loaded_segments (0x26ede8 : word) = Some W_26edac.
Proof. vm_refl. Qed.
Lemma D_26edac : decode_any W_26edac = Some (OpImm ALU_ADD 10 10 3932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26edb0 : bv 32 := 0x00008067.
Lemma F_26edb0 : fetch_word Plain.M.loaded_segments (0x26edec : word) = Some W_26edb0.
Proof. vm_refl. Qed.
Lemma D_26edb0 : decode_any W_26edb0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26edb4 : bv 32 := 0xfd010113.
Lemma F_26edb4 : fetch_word Plain.M.loaded_segments (0x26edf0 : word) = Some W_26edb4.
Proof. vm_refl. Qed.
Lemma D_26edb4 : decode_any W_26edb4 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26edb8 : bv 32 := 0x02113423.
Lemma F_26edb8 : fetch_word Plain.M.loaded_segments (0x26edf4 : word) = Some W_26edb8.
Proof. vm_refl. Qed.
Lemma D_26edb8 : decode_any W_26edb8 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26edbc : bv 32 := 0x00600513.
Lemma F_26edbc : fetch_word Plain.M.loaded_segments (0x26edf8 : word) = Some W_26edbc.
Proof. vm_refl. Qed.
Lemma D_26edbc : decode_any W_26edbc = Some (OpImm ALU_ADD 10 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26edc0 : bv 32 := 0x3a9020ef.
Lemma F_26edc0 : fetch_word Plain.M.loaded_segments (0x26edfc : word) = Some W_26edc0.
Proof. vm_refl. Qed.
Lemma D_26edc0 : decode_any W_26edc0 = Some (Jal 1 11176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26edc4 : bv 32 := 0x00000513.
Lemma F_26edc4 : fetch_word Plain.M.loaded_segments (0x26ee00 : word) = Some W_26edc4.
Proof. vm_refl. Qed.
Lemma D_26edc4 : decode_any W_26edc4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26edc8 : bv 32 := 0x345020ef.
Lemma F_26edc8 : fetch_word Plain.M.loaded_segments (0x26ee04 : word) = Some W_26edc8.
Proof. vm_refl. Qed.
Lemma D_26edc8 : decode_any W_26edc8 = Some (Jal 1 11076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26edcc : bv 32 := 0x000a0517.
Lemma F_26edcc : fetch_word Plain.M.loaded_segments (0x26ee08 : word) = Some W_26edcc.
Proof. vm_refl. Qed.
Lemma D_26edcc : decode_any W_26edcc = Some (Auipc 10 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26edd0 : bv 32 := 0x6b850513.
Lemma F_26edd0 : fetch_word Plain.M.loaded_segments (0x26ee0c : word) = Some W_26edd0.
Proof. vm_refl. Qed.
Lemma D_26edd0 : decode_any W_26edd0 = Some (OpImm ALU_ADD 10 10 1720, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26edd4 : bv 32 := 0x14d0b0ef.
Lemma F_26edd4 : fetch_word Plain.M.loaded_segments (0x26ee10 : word) = Some W_26edd4.
Proof. vm_refl. Qed.
Lemma D_26edd4 : decode_any W_26edd4 = Some (Jal 1 47436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26edd8 : bv 32 := 0x00000613.
Lemma F_26edd8 : fetch_word Plain.M.loaded_segments (0x26ee14 : word) = Some W_26edd8.
Proof. vm_refl. Qed.
Lemma D_26edd8 : decode_any W_26edd8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eddc : bv 32 := 0x00013423.
Lemma F_26eddc : fetch_word Plain.M.loaded_segments (0x26ee18 : word) = Some W_26eddc.
Proof. vm_refl. Qed.
Lemma D_26eddc : decode_any W_26eddc = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ede0 : bv 32 := 0x00013823.
Lemma F_26ede0 : fetch_word Plain.M.loaded_segments (0x26ee1c : word) = Some W_26ede0.
Proof. vm_refl. Qed.
Lemma D_26ede0 : decode_any W_26ede0 = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ede4 : bv 32 := 0x00013c23.
Lemma F_26ede4 : fetch_word Plain.M.loaded_segments (0x26ee20 : word) = Some W_26ede4.
Proof. vm_refl. Qed.
Lemma D_26ede4 : decode_any W_26ede4 = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ede8 : bv 32 := 0x02013023.
Lemma F_26ede8 : fetch_word Plain.M.loaded_segments (0x26ee24 : word) = Some W_26ede8.
Proof. vm_refl. Qed.
Lemma D_26ede8 : decode_any W_26ede8 = Some (Store SZ8 2 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26edec : bv 32 := 0x08600893.
Lemma F_26edec : fetch_word Plain.M.loaded_segments (0x26ee28 : word) = Some W_26edec.
Proof. vm_refl. Qed.
Lemma D_26edec : decode_any W_26edec = Some (OpImm ALU_ADD 17 0 134, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26edf0 : bv 32 := 0x00600513.
Lemma F_26edf0 : fetch_word Plain.M.loaded_segments (0x26ee2c : word) = Some W_26edf0.
Proof. vm_refl. Qed.
Lemma D_26edf0 : decode_any W_26edf0 = Some (OpImm ALU_ADD 10 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26edf4 : bv 32 := 0x00810593.
Lemma F_26edf4 : fetch_word Plain.M.loaded_segments (0x26ee30 : word) = Some W_26edf4.
Proof. vm_refl. Qed.
Lemma D_26edf4 : decode_any W_26edf4 = Some (OpImm ALU_ADD 11 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26edf8 : bv 32 := 0x00800693.
Lemma F_26edf8 : fetch_word Plain.M.loaded_segments (0x26ee34 : word) = Some W_26edf8.
Proof. vm_refl. Qed.
Lemma D_26edf8 : decode_any W_26edf8 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26edfc : bv 32 := 0x00000073.
Lemma F_26edfc : fetch_word Plain.M.loaded_segments (0x26ee38 : word) = Some W_26edfc.
Proof. vm_refl. Qed.
Lemma D_26edfc : decode_any W_26edfc = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_26edfc : is_ecall W_26edfc = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26ee00 : bv 32 := 0x00020513.
Lemma F_26ee00 : fetch_word Plain.M.loaded_segments (0x26ee3c : word) = Some W_26ee00.
Proof. vm_refl. Qed.
Lemma D_26ee00 : decode_any W_26ee00 = Some (OpImm ALU_ADD 10 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee04 : bv 32 := 0xf5852503.
Lemma F_26ee04 : fetch_word Plain.M.loaded_segments (0x26ee40 : word) = Some W_26ee04.
Proof. vm_refl. Qed.
Lemma D_26ee04 : decode_any W_26ee04 = Some (Load SZ4 true 10 10 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee08 : bv 32 := 0x02000613.
Lemma F_26ee08 : fetch_word Plain.M.loaded_segments (0x26ee44 : word) = Some W_26ee08.
Proof. vm_refl. Qed.
Lemma D_26ee08 : decode_any W_26ee08 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee0c : bv 32 := 0x08200893.
Lemma F_26ee0c : fetch_word Plain.M.loaded_segments (0x26ee48 : word) = Some W_26ee0c.
Proof. vm_refl. Qed.
Lemma D_26ee0c : decode_any W_26ee0c = Some (OpImm ALU_ADD 17 0 130, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee10 : bv 32 := 0x00600593.
Lemma F_26ee10 : fetch_word Plain.M.loaded_segments (0x26ee4c : word) = Some W_26ee10.
Proof. vm_refl. Qed.
Lemma D_26ee10 : decode_any W_26ee10 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee14 : bv 32 := 0x00000073.
Lemma F_26ee14 : fetch_word Plain.M.loaded_segments (0x26ee50 : word) = Some W_26ee14.
Proof. vm_refl. Qed.
Lemma D_26ee14 : decode_any W_26ee14 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_26ee14 : is_ecall W_26ee14 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26ee18 : bv 32 := 0x00c13023.
Lemma F_26ee18 : fetch_word Plain.M.loaded_segments (0x26ee54 : word) = Some W_26ee18.
Proof. vm_refl. Qed.
Lemma D_26ee18 : decode_any W_26ee18 = Some (Store SZ8 2 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee1c : bv 32 := 0x08700893.
Lemma F_26ee1c : fetch_word Plain.M.loaded_segments (0x26ee58 : word) = Some W_26ee1c.
Proof. vm_refl. Qed.
Lemma D_26ee1c : decode_any W_26ee1c = Some (OpImm ALU_ADD 17 0 135, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee20 : bv 32 := 0x00010593.
Lemma F_26ee20 : fetch_word Plain.M.loaded_segments (0x26ee5c : word) = Some W_26ee20.
Proof. vm_refl. Qed.
Lemma D_26ee20 : decode_any W_26ee20 = Some (OpImm ALU_ADD 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee24 : bv 32 := 0x00100513.
Lemma F_26ee24 : fetch_word Plain.M.loaded_segments (0x26ee60 : word) = Some W_26ee24.
Proof. vm_refl. Qed.
Lemma D_26ee24 : decode_any W_26ee24 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee28 : bv 32 := 0x00800693.
Lemma F_26ee28 : fetch_word Plain.M.loaded_segments (0x26ee64 : word) = Some W_26ee28.
Proof. vm_refl. Qed.
Lemma D_26ee28 : decode_any W_26ee28 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee2c : bv 32 := 0x00000613.
Lemma F_26ee2c : fetch_word Plain.M.loaded_segments (0x26ee68 : word) = Some W_26ee2c.
Proof. vm_refl. Qed.
Lemma D_26ee2c : decode_any W_26ee2c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee30 : bv 32 := 0x00000073.
Lemma F_26ee30 : fetch_word Plain.M.loaded_segments (0x26ee6c : word) = Some W_26ee30.
Proof. vm_refl. Qed.
Lemma D_26ee30 : decode_any W_26ee30 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_26ee30 : is_ecall W_26ee30 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26ee34 : bv 32 := 0x00000023.
Lemma F_26ee34 : fetch_word Plain.M.loaded_segments (0x26ee70 : word) = Some W_26ee34.
Proof. vm_refl. Qed.
Lemma D_26ee34 : decode_any W_26ee34 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee38 : bv 32 := 0x00900513.
Lemma F_26ee38 : fetch_word Plain.M.loaded_segments (0x26ee74 : word) = Some W_26ee38.
Proof. vm_refl. Qed.
Lemma D_26ee38 : decode_any W_26ee38 = Some (OpImm ALU_ADD 10 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee3c : bv 32 := 0x32d020ef.
Lemma F_26ee3c : fetch_word Plain.M.loaded_segments (0x26ee78 : word) = Some W_26ee3c.
Proof. vm_refl. Qed.
Lemma D_26ee3c : decode_any W_26ee3c = Some (Jal 1 11052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee40 : bv 32 := 0x07f00513.
Lemma F_26ee40 : fetch_word Plain.M.loaded_segments (0x26ee7c : word) = Some W_26ee40.
Proof. vm_refl. Qed.
Lemma D_26ee40 : decode_any W_26ee40 = Some (OpImm ALU_ADD 10 0 127, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee44 : bv 32 := 0x004000ef.
Lemma F_26ee44 : fetch_word Plain.M.loaded_segments (0x26ee80 : word) = Some W_26ee44.
Proof. vm_refl. Qed.
Lemma D_26ee44 : decode_any W_26ee44 = Some (Jal 1 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee48 : bv 32 := 0x00050593.
Lemma F_26ee48 : fetch_word Plain.M.loaded_segments (0x26ee84 : word) = Some W_26ee48.
Proof. vm_refl. Qed.
Lemma D_26ee48 : decode_any W_26ee48 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee4c : bv 32 := 0x05e00893.
Lemma F_26ee4c : fetch_word Plain.M.loaded_segments (0x26ee88 : word) = Some W_26ee4c.
Proof. vm_refl. Qed.
Lemma D_26ee4c : decode_any W_26ee4c = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee50 : bv 32 := 0x00000073.
Lemma F_26ee50 : fetch_word Plain.M.loaded_segments (0x26ee8c : word) = Some W_26ee50.
Proof. vm_refl. Qed.
Lemma D_26ee50 : decode_any W_26ee50 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_26ee50 : is_ecall W_26ee50 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26ee54 : bv 32 := 0x05d00893.
Lemma F_26ee54 : fetch_word Plain.M.loaded_segments (0x26ee90 : word) = Some W_26ee54.
Proof. vm_refl. Qed.
Lemma D_26ee54 : decode_any W_26ee54 = Some (OpImm ALU_ADD 17 0 93, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee58 : bv 32 := 0x00058513.
Lemma F_26ee58 : fetch_word Plain.M.loaded_segments (0x26ee94 : word) = Some W_26ee58.
Proof. vm_refl. Qed.
Lemma D_26ee58 : decode_any W_26ee58 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee5c : bv 32 := 0x00000073.
Lemma F_26ee5c : fetch_word Plain.M.loaded_segments (0x26ee98 : word) = Some W_26ee5c.
Proof. vm_refl. Qed.
Lemma D_26ee5c : decode_any W_26ee5c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_26ee5c : is_ecall W_26ee5c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26ee60 : bv 32 := 0xff9ff06f.
Lemma F_26ee60 : fetch_word Plain.M.loaded_segments (0x26ee9c : word) = Some W_26ee60.
Proof. vm_refl. Qed.
Lemma D_26ee60 : decode_any W_26ee60 = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee64 : bv 32 := 0xfd010113.
Lemma F_26ee64 : fetch_word Plain.M.loaded_segments (0x26eea0 : word) = Some W_26ee64.
Proof. vm_refl. Qed.
Lemma D_26ee64 : decode_any W_26ee64 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee68 : bv 32 := 0x02113423.
Lemma F_26ee68 : fetch_word Plain.M.loaded_segments (0x26eea4 : word) = Some W_26ee68.
Proof. vm_refl. Qed.
Lemma D_26ee68 : decode_any W_26ee68 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee6c : bv 32 := 0x02813023.
Lemma F_26ee6c : fetch_word Plain.M.loaded_segments (0x26eea8 : word) = Some W_26ee6c.
Proof. vm_refl. Qed.
Lemma D_26ee6c : decode_any W_26ee6c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee70 : bv 32 := 0x00913c23.
Lemma F_26ee70 : fetch_word Plain.M.loaded_segments (0x26eeac : word) = Some W_26ee70.
Proof. vm_refl. Qed.
Lemma D_26ee70 : decode_any W_26ee70 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee74 : bv 32 := 0x01213823.
Lemma F_26ee74 : fetch_word Plain.M.loaded_segments (0x26eeb0 : word) = Some W_26ee74.
Proof. vm_refl. Qed.
Lemma D_26ee74 : decode_any W_26ee74 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee78 : bv 32 := 0x01313423.
Lemma F_26ee78 : fetch_word Plain.M.loaded_segments (0x26eeb4 : word) = Some W_26ee78.
Proof. vm_refl. Qed.
Lemma D_26ee78 : decode_any W_26ee78 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee7c : bv 32 := 0x000a0517.
Lemma F_26ee7c : fetch_word Plain.M.loaded_segments (0x26eeb8 : word) = Some W_26ee7c.
Proof. vm_refl. Qed.
Lemma D_26ee7c : decode_any W_26ee7c = Some (Auipc 10 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee80 : bv 32 := 0x61050913.
Lemma F_26ee80 : fetch_word Plain.M.loaded_segments (0x26eebc : word) = Some W_26ee80.
Proof. vm_refl. Qed.
Lemma D_26ee80 : decode_any W_26ee80 = Some (OpImm ALU_ADD 18 10 1552, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee84 : bv 32 := 0x00490413.
Lemma F_26ee84 : fetch_word Plain.M.loaded_segments (0x26eec0 : word) = Some W_26ee84.
Proof. vm_refl. Qed.
Lemma D_26ee84 : decode_any W_26ee84 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee88 : bv 32 := 0x00040513.
Lemma F_26ee88 : fetch_word Plain.M.loaded_segments (0x26eec4 : word) = Some W_26ee88.
Proof. vm_refl. Qed.
Lemma D_26ee88 : decode_any W_26ee88 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee8c : bv 32 := 0x0950b0ef.
Lemma F_26ee8c : fetch_word Plain.M.loaded_segments (0x26eec8 : word) = Some W_26ee8c.
Proof. vm_refl. Qed.
Lemma D_26ee8c : decode_any W_26ee8c = Some (Jal 1 47252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee90 : bv 32 := 0x01093503.
Lemma F_26ee90 : fetch_word Plain.M.loaded_segments (0x26eecc : word) = Some W_26ee90.
Proof. vm_refl. Qed.
Lemma D_26ee90 : decode_any W_26ee90 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee94 : bv 32 := 0x06050863.
Lemma F_26ee94 : fetch_word Plain.M.loaded_segments (0x26eed0 : word) = Some W_26ee94.
Proof. vm_refl. Qed.
Lemma D_26ee94 : decode_any W_26ee94 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee98 : bv 32 := 0x00892583.
Lemma F_26ee98 : fetch_word Plain.M.loaded_segments (0x26eed4 : word) = Some W_26ee98.
Proof. vm_refl. Qed.
Lemma D_26ee98 : decode_any W_26ee98 = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee9c : bv 32 := 0x0180006f.
Lemma F_26ee9c : fetch_word Plain.M.loaded_segments (0x26eed8 : word) = Some W_26ee9c.
Proof. vm_refl. Qed.
Lemma D_26ee9c : decode_any W_26ee9c = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eea0 : bv 32 := 0x00053503.
Lemma F_26eea0 : fetch_word Plain.M.loaded_segments (0x26eedc : word) = Some W_26eea0.
Proof. vm_refl. Qed.
Lemma D_26eea0 : decode_any W_26eea0 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eea4 : bv 32 := 0x02000593.
Lemma F_26eea4 : fetch_word Plain.M.loaded_segments (0x26eee0 : word) = Some W_26eea4.
Proof. vm_refl. Qed.
Lemma D_26eea4 : decode_any W_26eea4 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eea8 : bv 32 := 0x00b92423.
Lemma F_26eea8 : fetch_word Plain.M.loaded_segments (0x26eee4 : word) = Some W_26eea8.
Proof. vm_refl. Qed.
Lemma D_26eea8 : decode_any W_26eea8 = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eeac : bv 32 := 0x00a93823.
Lemma F_26eeac : fetch_word Plain.M.loaded_segments (0x26eee8 : word) = Some W_26eeac.
Proof. vm_refl. Qed.
Lemma D_26eeac : decode_any W_26eeac = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eeb0 : bv 32 := 0x04050a63.
Lemma F_26eeb0 : fetch_word Plain.M.loaded_segments (0x26eeec : word) = Some W_26eeb0.
Proof. vm_refl. Qed.
Lemma D_26eeb0 : decode_any W_26eeb0 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eeb4 : bv 32 := 0xfff5861b.
Lemma F_26eeb4 : fetch_word Plain.M.loaded_segments (0x26eef0 : word) = Some W_26eeb4.
Proof. vm_refl. Qed.
Lemma D_26eeb4 : decode_any W_26eeb4 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eeb8 : bv 32 := 0x00c92423.
Lemma F_26eeb8 : fetch_word Plain.M.loaded_segments (0x26eef4 : word) = Some W_26eeb8.
Proof. vm_refl. Qed.
Lemma D_26eeb8 : decode_any W_26eeb8 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eebc : bv 32 := 0xfeb052e3.
Lemma F_26eebc : fetch_word Plain.M.loaded_segments (0x26eef8 : word) = Some W_26eebc.
Proof. vm_refl. Qed.
Lemma D_26eebc : decode_any W_26eebc = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eec0 : bv 32 := 0x01093503.
Lemma F_26eec0 : fetch_word Plain.M.loaded_segments (0x26eefc : word) = Some W_26eec0.
Proof. vm_refl. Qed.
Lemma D_26eec0 : decode_any W_26eec0 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eec4 : bv 32 := 0x00361613.
Lemma F_26eec4 : fetch_word Plain.M.loaded_segments (0x26ef00 : word) = Some W_26eec4.
Proof. vm_refl. Qed.
Lemma D_26eec4 : decode_any W_26eec4 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eec8 : bv 32 := 0x00c50533.
Lemma F_26eec8 : fetch_word Plain.M.loaded_segments (0x26ef04 : word) = Some W_26eec8.
Proof. vm_refl. Qed.
Lemma D_26eec8 : decode_any W_26eec8 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eecc : bv 32 := 0x00853983.
Lemma F_26eecc : fetch_word Plain.M.loaded_segments (0x26ef08 : word) = Some W_26eecc.
Proof. vm_refl. Qed.
Lemma D_26eecc : decode_any W_26eecc = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eed0 : bv 32 := 0x10853483.
Lemma F_26eed0 : fetch_word Plain.M.loaded_segments (0x26ef0c : word) = Some W_26eed0.
Proof. vm_refl. Qed.
Lemma D_26eed0 : decode_any W_26eed0 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eed4 : bv 32 := 0x00040513.
Lemma F_26eed4 : fetch_word Plain.M.loaded_segments (0x26ef10 : word) = Some W_26eed4.
Proof. vm_refl. Qed.
Lemma D_26eed4 : decode_any W_26eed4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eed8 : bv 32 := 0x2d10b0ef.
Lemma F_26eed8 : fetch_word Plain.M.loaded_segments (0x26ef14 : word) = Some W_26eed8.
Proof. vm_refl. Qed.
Lemma D_26eed8 : decode_any W_26eed8 = Some (Jal 1 47824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eedc : bv 32 := 0x00048513.
Lemma F_26eedc : fetch_word Plain.M.loaded_segments (0x26ef18 : word) = Some W_26eedc.
Proof. vm_refl. Qed.
Lemma D_26eedc : decode_any W_26eedc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eee0 : bv 32 := 0x000980e7.
Lemma F_26eee0 : fetch_word Plain.M.loaded_segments (0x26ef1c : word) = Some W_26eee0.
Proof. vm_refl. Qed.
Lemma D_26eee0 : decode_any W_26eee0 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eee4 : bv 32 := 0x00040513.
Lemma F_26eee4 : fetch_word Plain.M.loaded_segments (0x26ef20 : word) = Some W_26eee4.
Proof. vm_refl. Qed.
Lemma D_26eee4 : decode_any W_26eee4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eee8 : bv 32 := 0x0390b0ef.
Lemma F_26eee8 : fetch_word Plain.M.loaded_segments (0x26ef24 : word) = Some W_26eee8.
Proof. vm_refl. Qed.
Lemma D_26eee8 : decode_any W_26eee8 = Some (Jal 1 47160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eeec : bv 32 := 0x00892503.
Lemma F_26eeec : fetch_word Plain.M.loaded_segments (0x26ef28 : word) = Some W_26eeec.
Proof. vm_refl. Qed.
Lemma D_26eeec : decode_any W_26eeec = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eef0 : bv 32 := 0xfff5061b.
Lemma F_26eef0 : fetch_word Plain.M.loaded_segments (0x26ef2c : word) = Some W_26eef0.
Proof. vm_refl. Qed.
Lemma D_26eef0 : decode_any W_26eef0 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eef4 : bv 32 := 0x00c92423.
Lemma F_26eef4 : fetch_word Plain.M.loaded_segments (0x26ef30 : word) = Some W_26eef4.
Proof. vm_refl. Qed.
Lemma D_26eef4 : decode_any W_26eef4 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eef8 : bv 32 := 0xfca044e3.
Lemma F_26eef8 : fetch_word Plain.M.loaded_segments (0x26ef34 : word) = Some W_26eef8.
Proof. vm_refl. Qed.
Lemma D_26eef8 : decode_any W_26eef8 = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eefc : bv 32 := 0x01093503.
Lemma F_26eefc : fetch_word Plain.M.loaded_segments (0x26ef38 : word) = Some W_26eefc.
Proof. vm_refl. Qed.
Lemma D_26eefc : decode_any W_26eefc = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef00 : bv 32 := 0xfa1ff06f.
Lemma F_26ef00 : fetch_word Plain.M.loaded_segments (0x26ef3c : word) = Some W_26ef00.
Proof. vm_refl. Qed.
Lemma D_26ef00 : decode_any W_26ef00 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef04 : bv 32 := 0x00100513.
Lemma F_26ef04 : fetch_word Plain.M.loaded_segments (0x26ef40 : word) = Some W_26ef04.
Proof. vm_refl. Qed.
Lemma D_26ef04 : decode_any W_26ef04 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef08 : bv 32 := 0x00a90023.
Lemma F_26ef08 : fetch_word Plain.M.loaded_segments (0x26ef44 : word) = Some W_26ef08.
Proof. vm_refl. Qed.
Lemma D_26ef08 : decode_any W_26ef08 = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef0c : bv 32 := 0x00040513.
Lemma F_26ef0c : fetch_word Plain.M.loaded_segments (0x26ef48 : word) = Some W_26ef0c.
Proof. vm_refl. Qed.
Lemma D_26ef0c : decode_any W_26ef0c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef10 : bv 32 := 0x02813083.
Lemma F_26ef10 : fetch_word Plain.M.loaded_segments (0x26ef4c : word) = Some W_26ef10.
Proof. vm_refl. Qed.
Lemma D_26ef10 : decode_any W_26ef10 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef14 : bv 32 := 0x02013403.
Lemma F_26ef14 : fetch_word Plain.M.loaded_segments (0x26ef50 : word) = Some W_26ef14.
Proof. vm_refl. Qed.
Lemma D_26ef14 : decode_any W_26ef14 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef18 : bv 32 := 0x01813483.
Lemma F_26ef18 : fetch_word Plain.M.loaded_segments (0x26ef54 : word) = Some W_26ef18.
Proof. vm_refl. Qed.
Lemma D_26ef18 : decode_any W_26ef18 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef1c : bv 32 := 0x01013903.
Lemma F_26ef1c : fetch_word Plain.M.loaded_segments (0x26ef58 : word) = Some W_26ef1c.
Proof. vm_refl. Qed.
Lemma D_26ef1c : decode_any W_26ef1c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef20 : bv 32 := 0x00813983.
Lemma F_26ef20 : fetch_word Plain.M.loaded_segments (0x26ef5c : word) = Some W_26ef20.
Proof. vm_refl. Qed.
Lemma D_26ef20 : decode_any W_26ef20 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef24 : bv 32 := 0x03010113.
Lemma F_26ef24 : fetch_word Plain.M.loaded_segments (0x26ef60 : word) = Some W_26ef24.
Proof. vm_refl. Qed.
Lemma D_26ef24 : decode_any W_26ef24 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef28 : bv 32 := 0x2810b06f.
Lemma F_26ef28 : fetch_word Plain.M.loaded_segments (0x26ef64 : word) = Some W_26ef28.
Proof. vm_refl. Qed.
Lemma D_26ef28 : decode_any W_26ef28 = Some (Jal 0 47744, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef2c : bv 32 := 0x00008067.
Lemma F_26ef2c : fetch_word Plain.M.loaded_segments (0x26ef68 : word) = Some W_26ef2c.
Proof. vm_refl. Qed.
Lemma D_26ef2c : decode_any W_26ef2c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef30 : bv 32 := 0xfd010113.
Lemma F_26ef30 : fetch_word Plain.M.loaded_segments (0x26ef6c : word) = Some W_26ef30.
Proof. vm_refl. Qed.
Lemma D_26ef30 : decode_any W_26ef30 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef34 : bv 32 := 0x02113423.
Lemma F_26ef34 : fetch_word Plain.M.loaded_segments (0x26ef70 : word) = Some W_26ef34.
Proof. vm_refl. Qed.
Lemma D_26ef34 : decode_any W_26ef34 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef38 : bv 32 := 0x02813023.
Lemma F_26ef38 : fetch_word Plain.M.loaded_segments (0x26ef74 : word) = Some W_26ef38.
Proof. vm_refl. Qed.
Lemma D_26ef38 : decode_any W_26ef38 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef3c : bv 32 := 0x00913c23.
Lemma F_26ef3c : fetch_word Plain.M.loaded_segments (0x26ef78 : word) = Some W_26ef3c.
Proof. vm_refl. Qed.
Lemma D_26ef3c : decode_any W_26ef3c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef40 : bv 32 := 0x01213823.
Lemma F_26ef40 : fetch_word Plain.M.loaded_segments (0x26ef7c : word) = Some W_26ef40.
Proof. vm_refl. Qed.
Lemma D_26ef40 : decode_any W_26ef40 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef44 : bv 32 := 0x01313423.
Lemma F_26ef44 : fetch_word Plain.M.loaded_segments (0x26ef80 : word) = Some W_26ef44.
Proof. vm_refl. Qed.
Lemma D_26ef44 : decode_any W_26ef44 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef48 : bv 32 := 0x00050493.
Lemma F_26ef48 : fetch_word Plain.M.loaded_segments (0x26ef84 : word) = Some W_26ef48.
Proof. vm_refl. Qed.
Lemma D_26ef48 : decode_any W_26ef48 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef4c : bv 32 := 0x000a0517.
Lemma F_26ef4c : fetch_word Plain.M.loaded_segments (0x26ef88 : word) = Some W_26ef4c.
Proof. vm_refl. Qed.
Lemma D_26ef4c : decode_any W_26ef4c = Some (Auipc 10 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef50 : bv 32 := 0x54050993.
Lemma F_26ef50 : fetch_word Plain.M.loaded_segments (0x26ef8c : word) = Some W_26ef50.
Proof. vm_refl. Qed.
Lemma D_26ef50 : decode_any W_26ef50 = Some (OpImm ALU_ADD 19 10 1344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef54 : bv 32 := 0x00498413.
Lemma F_26ef54 : fetch_word Plain.M.loaded_segments (0x26ef90 : word) = Some W_26ef54.
Proof. vm_refl. Qed.
Lemma D_26ef54 : decode_any W_26ef54 = Some (OpImm ALU_ADD 8 19 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef58 : bv 32 := 0x00040513.
Lemma F_26ef58 : fetch_word Plain.M.loaded_segments (0x26ef94 : word) = Some W_26ef58.
Proof. vm_refl. Qed.
Lemma D_26ef58 : decode_any W_26ef58 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef5c : bv 32 := 0x7c40b0ef.
Lemma F_26ef5c : fetch_word Plain.M.loaded_segments (0x26ef98 : word) = Some W_26ef5c.
Proof. vm_refl. Qed.
Lemma D_26ef5c : decode_any W_26ef5c = Some (Jal 1 47044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef60 : bv 32 := 0x0009c503.
Lemma F_26ef60 : fetch_word Plain.M.loaded_segments (0x26ef9c : word) = Some W_26ef60.
Proof. vm_refl. Qed.
Lemma D_26ef60 : decode_any W_26ef60 = Some (Load SZ1 false 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef64 : bv 32 := 0xfff00913.
Lemma F_26ef64 : fetch_word Plain.M.loaded_segments (0x26efa0 : word) = Some W_26ef64.
Proof. vm_refl. Qed.
Lemma D_26ef64 : decode_any W_26ef64 = Some (OpImm ALU_ADD 18 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef68 : bv 32 := 0x06051263.
Lemma F_26ef68 : fetch_word Plain.M.loaded_segments (0x26efa4 : word) = Some W_26ef68.
Proof. vm_refl. Qed.
Lemma D_26ef68 : decode_any W_26ef68 = Some (Branch BC_NE 10 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef6c : bv 32 := 0x0109b503.
Lemma F_26ef6c : fetch_word Plain.M.loaded_segments (0x26efa8 : word) = Some W_26ef6c.
Proof. vm_refl. Qed.
Lemma D_26ef6c : decode_any W_26ef6c = Some (Load SZ8 true 10 19 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef70 : bv 32 := 0x00051663.
Lemma F_26ef70 : fetch_word Plain.M.loaded_segments (0x26efac : word) = Some W_26ef70.
Proof. vm_refl. Qed.
Lemma D_26ef70 : decode_any W_26ef70 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef74 : bv 32 := 0x01898513.
Lemma F_26ef74 : fetch_word Plain.M.loaded_segments (0x26efb0 : word) = Some W_26ef74.
Proof. vm_refl. Qed.
Lemma D_26ef74 : decode_any W_26ef74 = Some (OpImm ALU_ADD 10 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef78 : bv 32 := 0x00a9b823.
Lemma F_26ef78 : fetch_word Plain.M.loaded_segments (0x26efb4 : word) = Some W_26ef78.
Proof. vm_refl. Qed.
Lemma D_26ef78 : decode_any W_26ef78 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef7c : bv 32 := 0x0089a583.
Lemma F_26ef7c : fetch_word Plain.M.loaded_segments (0x26efb8 : word) = Some W_26ef7c.
Proof. vm_refl. Qed.
Lemma D_26ef7c : decode_any W_26ef7c = Some (Load SZ4 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef80 : bv 32 := 0x02000613.
Lemma F_26ef80 : fetch_word Plain.M.loaded_segments (0x26efbc : word) = Some W_26ef80.
Proof. vm_refl. Qed.
Lemma D_26ef80 : decode_any W_26ef80 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef84 : bv 32 := 0x02c59263.
Lemma F_26ef84 : fetch_word Plain.M.loaded_segments (0x26efc0 : word) = Some W_26ef84.
Proof. vm_refl. Qed.
Lemma D_26ef84 : decode_any W_26ef84 = Some (Branch BC_NE 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef88 : bv 32 := 0x20800513.
Lemma F_26ef88 : fetch_word Plain.M.loaded_segments (0x26efc4 : word) = Some W_26ef88.
Proof. vm_refl. Qed.
Lemma D_26ef88 : decode_any W_26ef88 = Some (OpImm ALU_ADD 10 0 520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef8c : bv 32 := 0x00100593.
Lemma F_26ef8c : fetch_word Plain.M.loaded_segments (0x26efc8 : word) = Some W_26ef8c.
Proof. vm_refl. Qed.
Lemma D_26ef8c : decode_any W_26ef8c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef90 : bv 32 := 0x3e0000ef.
Lemma F_26ef90 : fetch_word Plain.M.loaded_segments (0x26efcc : word) = Some W_26ef90.
Proof. vm_refl. Qed.
Lemma D_26ef90 : decode_any W_26ef90 = Some (Jal 1 992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef94 : bv 32 := 0x02050c63.
Lemma F_26ef94 : fetch_word Plain.M.loaded_segments (0x26efd0 : word) = Some W_26ef94.
Proof. vm_refl. Qed.
Lemma D_26ef94 : decode_any W_26ef94 = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef98 : bv 32 := 0x00000593.
Lemma F_26ef98 : fetch_word Plain.M.loaded_segments (0x26efd4 : word) = Some W_26ef98.
Proof. vm_refl. Qed.
Lemma D_26ef98 : decode_any W_26ef98 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef9c : bv 32 := 0x0109b603.
Lemma F_26ef9c : fetch_word Plain.M.loaded_segments (0x26efd8 : word) = Some W_26ef9c.
Proof. vm_refl. Qed.
Lemma D_26ef9c : decode_any W_26ef9c = Some (Load SZ8 true 12 19 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26efa0 : bv 32 := 0x00c53023.
Lemma F_26efa0 : fetch_word Plain.M.loaded_segments (0x26efdc : word) = Some W_26efa0.
Proof. vm_refl. Qed.
Lemma D_26efa0 : decode_any W_26efa0 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26efa4 : bv 32 := 0x00a9b823.
Lemma F_26efa4 : fetch_word Plain.M.loaded_segments (0x26efe0 : word) = Some W_26efa4.
Proof. vm_refl. Qed.
Lemma D_26efa4 : decode_any W_26efa4 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26efa8 : bv 32 := 0x00000913.
Lemma F_26efa8 : fetch_word Plain.M.loaded_segments (0x26efe4 : word) = Some W_26efa8.
Proof. vm_refl. Qed.
Lemma D_26efa8 : decode_any W_26efa8 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26efac : bv 32 := 0x00359613.
Lemma F_26efac : fetch_word Plain.M.loaded_segments (0x26efe8 : word) = Some W_26efac.
Proof. vm_refl. Qed.
Lemma D_26efac : decode_any W_26efac = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26efb0 : bv 32 := 0x00c50533.
Lemma F_26efb0 : fetch_word Plain.M.loaded_segments (0x26efec : word) = Some W_26efb0.
Proof. vm_refl. Qed.
Lemma D_26efb0 : decode_any W_26efb0 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26efb4 : bv 32 := 0x00000617.
Lemma F_26efb4 : fetch_word Plain.M.loaded_segments (0x26eff0 : word) = Some W_26efb4.
Proof. vm_refl. Qed.
Lemma D_26efb4 : decode_any W_26efb4 = Some (Auipc 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26efb8 : bv 32 := 0x00158593.
Lemma F_26efb8 : fetch_word Plain.M.loaded_segments (0x26eff4 : word) = Some W_26efb8.
Proof. vm_refl. Qed.
Lemma D_26efb8 : decode_any W_26efb8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26efbc : bv 32 := 0x04060613.
Lemma F_26efbc : fetch_word Plain.M.loaded_segments (0x26eff8 : word) = Some W_26efbc.
Proof. vm_refl. Qed.
Lemma D_26efbc : decode_any W_26efbc = Some (OpImm ALU_ADD 12 12 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26efc0 : bv 32 := 0x00c53423.
Lemma F_26efc0 : fetch_word Plain.M.loaded_segments (0x26effc : word) = Some W_26efc0.
Proof. vm_refl. Qed.
Lemma D_26efc0 : decode_any W_26efc0 = Some (Store SZ8 10 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26efc4 : bv 32 := 0x10953423.
Lemma F_26efc4 : fetch_word Plain.M.loaded_segments (0x26f000 : word) = Some W_26efc4.
Proof. vm_refl. Qed.
Lemma D_26efc4 : decode_any W_26efc4 = Some (Store SZ8 10 9 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26efc8 : bv 32 := 0x00b9a423.
Lemma F_26efc8 : fetch_word Plain.M.loaded_segments (0x26f004 : word) = Some W_26efc8.
Proof. vm_refl. Qed.
Lemma D_26efc8 : decode_any W_26efc8 = Some (Store SZ4 19 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26efcc : bv 32 := 0x00040513.
Lemma F_26efcc : fetch_word Plain.M.loaded_segments (0x26f008 : word) = Some W_26efcc.
Proof. vm_refl. Qed.
Lemma D_26efcc : decode_any W_26efcc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26efd0 : bv 32 := 0x1d90b0ef.
Lemma F_26efd0 : fetch_word Plain.M.loaded_segments (0x26f00c : word) = Some W_26efd0.
Proof. vm_refl. Qed.
Lemma D_26efd0 : decode_any W_26efd0 = Some (Jal 1 47576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26efd4 : bv 32 := 0x00090513.
Lemma F_26efd4 : fetch_word Plain.M.loaded_segments (0x26f010 : word) = Some W_26efd4.
Proof. vm_refl. Qed.
Lemma D_26efd4 : decode_any W_26efd4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26efd8 : bv 32 := 0x02813083.
Lemma F_26efd8 : fetch_word Plain.M.loaded_segments (0x26f014 : word) = Some W_26efd8.
Proof. vm_refl. Qed.
Lemma D_26efd8 : decode_any W_26efd8 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26efdc : bv 32 := 0x02013403.
Lemma F_26efdc : fetch_word Plain.M.loaded_segments (0x26f018 : word) = Some W_26efdc.
Proof. vm_refl. Qed.
Lemma D_26efdc : decode_any W_26efdc = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26efe0 : bv 32 := 0x01813483.
Lemma F_26efe0 : fetch_word Plain.M.loaded_segments (0x26f01c : word) = Some W_26efe0.
Proof. vm_refl. Qed.
Lemma D_26efe0 : decode_any W_26efe0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26efe4 : bv 32 := 0x01013903.
Lemma F_26efe4 : fetch_word Plain.M.loaded_segments (0x26f020 : word) = Some W_26efe4.
Proof. vm_refl. Qed.
Lemma D_26efe4 : decode_any W_26efe4 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26efe8 : bv 32 := 0x00813983.
Lemma F_26efe8 : fetch_word Plain.M.loaded_segments (0x26f024 : word) = Some W_26efe8.
Proof. vm_refl. Qed.
Lemma D_26efe8 : decode_any W_26efe8 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26efec : bv 32 := 0x03010113.
Lemma F_26efec : fetch_word Plain.M.loaded_segments (0x26f028 : word) = Some W_26efec.
Proof. vm_refl. Qed.
Lemma D_26efec : decode_any W_26efec = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eff0 : bv 32 := 0x00008067.
Lemma F_26eff0 : fetch_word Plain.M.loaded_segments (0x26f02c : word) = Some W_26eff0.
Proof. vm_refl. Qed.
Lemma D_26eff0 : decode_any W_26eff0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eff4 : bv 32 := 0x00050067.
Lemma F_26eff4 : fetch_word Plain.M.loaded_segments (0x26f030 : word) = Some W_26eff4.
Proof. vm_refl. Qed.
Lemma D_26eff4 : decode_any W_26eff4 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eff8 : bv 32 := 0x00008067.
Lemma F_26eff8 : fetch_word Plain.M.loaded_segments (0x26f034 : word) = Some W_26eff8.
Proof. vm_refl. Qed.
Lemma D_26eff8 : decode_any W_26eff8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26effc : bv 32 := 0xfe010113.
Lemma F_26effc : fetch_word Plain.M.loaded_segments (0x26f038 : word) = Some W_26effc.
Proof. vm_refl. Qed.
Lemma D_26effc : decode_any W_26effc = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f000 : bv 32 := 0x00113c23.
Lemma F_26f000 : fetch_word Plain.M.loaded_segments (0x26f03c : word) = Some W_26f000.
Proof. vm_refl. Qed.
Lemma D_26f000 : decode_any W_26f000 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f004 : bv 32 := 0x00813823.
Lemma F_26f004 : fetch_word Plain.M.loaded_segments (0x26f040 : word) = Some W_26f004.
Proof. vm_refl. Qed.
Lemma D_26f004 : decode_any W_26f004 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f008 : bv 32 := 0x00913423.
Lemma F_26f008 : fetch_word Plain.M.loaded_segments (0x26f044 : word) = Some W_26f008.
Proof. vm_refl. Qed.
Lemma D_26f008 : decode_any W_26f008 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f00c : bv 32 := 0x0006c517.
Lemma F_26f00c : fetch_word Plain.M.loaded_segments (0x26f048 : word) = Some W_26f00c.
Proof. vm_refl. Qed.
Lemma D_26f00c : decode_any W_26f00c = Some (Auipc 10 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f010 : bv 32 := 0x0006c597.
Lemma F_26f010 : fetch_word Plain.M.loaded_segments (0x26f04c : word) = Some W_26f010.
Proof. vm_refl. Qed.
Lemma D_26f010 : decode_any W_26f010 = Some (Auipc 11 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f014 : bv 32 := 0x10853503.
Lemma F_26f014 : fetch_word Plain.M.loaded_segments (0x26f050 : word) = Some W_26f014.
Proof. vm_refl. Qed.
Lemma D_26f014 : decode_any W_26f014 = Some (Load SZ8 true 10 10 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f018 : bv 32 := 0x10c5b403.
Lemma F_26f018 : fetch_word Plain.M.loaded_segments (0x26f054 : word) = Some W_26f018.
Proof. vm_refl. Qed.
Lemma D_26f018 : decode_any W_26f018 = Some (Load SZ8 true 8 11 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f01c : bv 32 := 0x00a47c63.
Lemma F_26f01c : fetch_word Plain.M.loaded_segments (0x26f058 : word) = Some W_26f01c.
Proof. vm_refl. Qed.
Lemma D_26f01c : decode_any W_26f01c = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f020 : bv 32 := 0xff853583.
Lemma F_26f020 : fetch_word Plain.M.loaded_segments (0x26f05c : word) = Some W_26f020.
Proof. vm_refl. Qed.
Lemma D_26f020 : decode_any W_26f020 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f024 : bv 32 := 0xff850493.
Lemma F_26f024 : fetch_word Plain.M.loaded_segments (0x26f060 : word) = Some W_26f024.
Proof. vm_refl. Qed.
Lemma D_26f024 : decode_any W_26f024 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f028 : bv 32 := 0x000580e7.
Lemma F_26f028 : fetch_word Plain.M.loaded_segments (0x26f064 : word) = Some W_26f028.
Proof. vm_refl. Qed.
Lemma D_26f028 : decode_any W_26f028 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f02c : bv 32 := 0x00048513.
Lemma F_26f02c : fetch_word Plain.M.loaded_segments (0x26f068 : word) = Some W_26f02c.
Proof. vm_refl. Qed.
Lemma D_26f02c : decode_any W_26f02c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f030 : bv 32 := 0xfe9468e3.
Lemma F_26f030 : fetch_word Plain.M.loaded_segments (0x26f06c : word) = Some W_26f030.
Proof. vm_refl. Qed.
Lemma D_26f030 : decode_any W_26f030 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f034 : bv 32 := 0x01813083.
Lemma F_26f034 : fetch_word Plain.M.loaded_segments (0x26f070 : word) = Some W_26f034.
Proof. vm_refl. Qed.
Lemma D_26f034 : decode_any W_26f034 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f038 : bv 32 := 0x01013403.
Lemma F_26f038 : fetch_word Plain.M.loaded_segments (0x26f074 : word) = Some W_26f038.
Proof. vm_refl. Qed.
Lemma D_26f038 : decode_any W_26f038 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f03c : bv 32 := 0x00813483.
Lemma F_26f03c : fetch_word Plain.M.loaded_segments (0x26f078 : word) = Some W_26f03c.
Proof. vm_refl. Qed.
Lemma D_26f03c : decode_any W_26f03c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f040 : bv 32 := 0x02010113.
Lemma F_26f040 : fetch_word Plain.M.loaded_segments (0x26f07c : word) = Some W_26f040.
Proof. vm_refl. Qed.
Lemma D_26f040 : decode_any W_26f040 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f044 : bv 32 := 0xfb5ff06f.
Lemma F_26f044 : fetch_word Plain.M.loaded_segments (0x26f080 : word) = Some W_26f044.
Proof. vm_refl. Qed.
Lemma D_26f044 : decode_any W_26f044 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f048 : bv 32 := 0xff010113.
Lemma F_26f048 : fetch_word Plain.M.loaded_segments (0x26f084 : word) = Some W_26f048.
Proof. vm_refl. Qed.
Lemma D_26f048 : decode_any W_26f048 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f04c : bv 32 := 0x00113423.
Lemma F_26f04c : fetch_word Plain.M.loaded_segments (0x26f088 : word) = Some W_26f04c.
Proof. vm_refl. Qed.
Lemma D_26f04c : decode_any W_26f04c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f050 : bv 32 := 0x00813023.
Lemma F_26f050 : fetch_word Plain.M.loaded_segments (0x26f08c : word) = Some W_26f050.
Proof. vm_refl. Qed.
Lemma D_26f050 : decode_any W_26f050 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f054 : bv 32 := 0x00000593.
Lemma F_26f054 : fetch_word Plain.M.loaded_segments (0x26f090 : word) = Some W_26f054.
Proof. vm_refl. Qed.
Lemma D_26f054 : decode_any W_26f054 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f058 : bv 32 := 0x00020613.
Lemma F_26f058 : fetch_word Plain.M.loaded_segments (0x26f094 : word) = Some W_26f058.
Proof. vm_refl. Qed.
Lemma D_26f058 : decode_any W_26f058 = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f05c : bv 32 := 0xf5862603.
Lemma F_26f05c : fetch_word Plain.M.loaded_segments (0x26f098 : word) = Some W_26f05c.
Proof. vm_refl. Qed.
Lemma D_26f05c : decode_any W_26f05c = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f060 : bv 32 := 0x000a0697.
Lemma F_26f060 : fetch_word Plain.M.loaded_segments (0x26f09c : word) = Some W_26f060.
Proof. vm_refl. Qed.
Lemma D_26f060 : decode_any W_26f060 = Some (Auipc 13 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f064 : bv 32 := 0x64c68693.
Lemma F_26f064 : fetch_word Plain.M.loaded_segments (0x26f0a0 : word) = Some W_26f064.
Proof. vm_refl. Qed.
Lemma D_26f064 : decode_any W_26f064 = Some (OpImm ALU_ADD 13 13 1612, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f068 : bv 32 := 0x1606a72f.
Lemma F_26f068 : fetch_word Plain.M.loaded_segments (0x26f0a4 : word) = Some W_26f068.
Proof. vm_refl. Qed.
Lemma D_26f068 : decode_any W_26f068 = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f06c : bv 32 := 0x00b71663.
Lemma F_26f06c : fetch_word Plain.M.loaded_segments (0x26f0a8 : word) = Some W_26f06c.
Proof. vm_refl. Qed.
Lemma D_26f06c : decode_any W_26f06c = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f070 : bv 32 := 0x1ec6a7af.
Lemma F_26f070 : fetch_word Plain.M.loaded_segments (0x26f0ac : word) = Some W_26f070.
Proof. vm_refl. Qed.
Lemma D_26f070 : decode_any W_26f070 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f074 : bv 32 := 0xfe079ae3.
Lemma F_26f074 : fetch_word Plain.M.loaded_segments (0x26f0b0 : word) = Some W_26f074.
Proof. vm_refl. Qed.
Lemma D_26f074 : decode_any W_26f074 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f078 : bv 32 := 0x0007059b.
Lemma F_26f078 : fetch_word Plain.M.loaded_segments (0x26f0b4 : word) = Some W_26f078.
Proof. vm_refl. Qed.
Lemma D_26f078 : decode_any W_26f078 = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f07c : bv 32 := 0x02c58263.
Lemma F_26f07c : fetch_word Plain.M.loaded_segments (0x26f0b8 : word) = Some W_26f07c.
Proof. vm_refl. Qed.
Lemma D_26f07c : decode_any W_26f07c = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f080 : bv 32 := 0x02058263.
Lemma F_26f080 : fetch_word Plain.M.loaded_segments (0x26f0bc : word) = Some W_26f080.
Proof. vm_refl. Qed.
Lemma D_26f080 : decode_any W_26f080 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f084 : bv 32 := 0x04900893.
Lemma F_26f084 : fetch_word Plain.M.loaded_segments (0x26f0c0 : word) = Some W_26f084.
Proof. vm_refl. Qed.
Lemma D_26f084 : decode_any W_26f084 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f088 : bv 32 := 0x00000593.
Lemma F_26f088 : fetch_word Plain.M.loaded_segments (0x26f0c4 : word) = Some W_26f088.
Proof. vm_refl. Qed.
Lemma D_26f088 : decode_any W_26f088 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f08c : bv 32 := 0x00000613.
Lemma F_26f08c : fetch_word Plain.M.loaded_segments (0x26f0c8 : word) = Some W_26f08c.
Proof. vm_refl. Qed.
Lemma D_26f08c : decode_any W_26f08c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f090 : bv 32 := 0x00000693.
Lemma F_26f090 : fetch_word Plain.M.loaded_segments (0x26f0cc : word) = Some W_26f090.
Proof. vm_refl. Qed.
Lemma D_26f090 : decode_any W_26f090 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f094 : bv 32 := 0x00000513.
Lemma F_26f094 : fetch_word Plain.M.loaded_segments (0x26f0d0 : word) = Some W_26f094.
Proof. vm_refl. Qed.
Lemma D_26f094 : decode_any W_26f094 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f098 : bv 32 := 0x00000073.
Lemma F_26f098 : fetch_word Plain.M.loaded_segments (0x26f0d4 : word) = Some W_26f098.
Proof. vm_refl. Qed.
Lemma D_26f098 : decode_any W_26f098 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_26f098 : is_ecall W_26f098 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26f09c : bv 32 := 0xff9ff06f.
Lemma F_26f09c : fetch_word Plain.M.loaded_segments (0x26f0d8 : word) = Some W_26f09c.
Proof. vm_refl. Qed.
Lemma D_26f09c : decode_any W_26f09c = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f0a0 : bv 32 := 0x00000023.
Lemma F_26f0a0 : fetch_word Plain.M.loaded_segments (0x26f0dc : word) = Some W_26f0a0.
Proof. vm_refl. Qed.
Lemma D_26f0a0 : decode_any W_26f0a0 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f0a4 : bv 32 := 0x00050413.
Lemma F_26f0a4 : fetch_word Plain.M.loaded_segments (0x26f0e0 : word) = Some W_26f0a4.
Proof. vm_refl. Qed.
Lemma D_26f0a4 : decode_any W_26f0a4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f0a8 : bv 32 := 0xdbdff0ef.
Lemma F_26f0a8 : fetch_word Plain.M.loaded_segments (0x26f0e4 : word) = Some W_26f0a8.
Proof. vm_refl. Qed.
Lemma D_26f0a8 : decode_any W_26f0a8 = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f0ac : bv 32 := 0xf51ff0ef.
Lemma F_26f0ac : fetch_word Plain.M.loaded_segments (0x26f0e8 : word) = Some W_26f0ac.
Proof. vm_refl. Qed.
Lemma D_26f0ac : decode_any W_26f0ac = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f0b0 : bv 32 := 0x7e0030ef.
Lemma F_26f0b0 : fetch_word Plain.M.loaded_segments (0x26f0ec : word) = Some W_26f0b0.
Proof. vm_refl. Qed.
Lemma D_26f0b0 : decode_any W_26f0b0 = Some (Jal 1 14304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f0b4 : bv 32 := 0x00040513.
Lemma F_26f0b4 : fetch_word Plain.M.loaded_segments (0x26f0f0 : word) = Some W_26f0b4.
Proof. vm_refl. Qed.
Lemma D_26f0b4 : decode_any W_26f0b4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f0b8 : bv 32 := 0xd91ff0ef.
Lemma F_26f0b8 : fetch_word Plain.M.loaded_segments (0x26f0f4 : word) = Some W_26f0b8.
Proof. vm_refl. Qed.
Lemma D_26f0b8 : decode_any W_26f0b8 = Some (Jal 1 2096528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f0bc : bv 32 := 0xfa010113.
Lemma F_26f0bc : fetch_word Plain.M.loaded_segments (0x26f0f8 : word) = Some W_26f0bc.
Proof. vm_refl. Qed.
Lemma D_26f0bc : decode_any W_26f0bc = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f0c0 : bv 32 := 0x02113423.
Lemma F_26f0c0 : fetch_word Plain.M.loaded_segments (0x26f0fc : word) = Some W_26f0c0.
Proof. vm_refl. Qed.
Lemma D_26f0c0 : decode_any W_26f0c0 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f0c4 : bv 32 := 0x02813023.
Lemma F_26f0c4 : fetch_word Plain.M.loaded_segments (0x26f100 : word) = Some W_26f0c4.
Proof. vm_refl. Qed.
Lemma D_26f0c4 : decode_any W_26f0c4 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f0c8 : bv 32 := 0x00913c23.
Lemma F_26f0c8 : fetch_word Plain.M.loaded_segments (0x26f104 : word) = Some W_26f0c8.
Proof. vm_refl. Qed.
Lemma D_26f0c8 : decode_any W_26f0c8 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f0cc : bv 32 := 0x00058413.
Lemma F_26f0cc : fetch_word Plain.M.loaded_segments (0x26f108 : word) = Some W_26f0cc.
Proof. vm_refl. Qed.
Lemma D_26f0cc : decode_any W_26f0cc = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f0d0 : bv 32 := 0x00050293.
Lemma F_26f0d0 : fetch_word Plain.M.loaded_segments (0x26f10c : word) = Some W_26f0d0.
Proof. vm_refl. Qed.
Lemma D_26f0d0 : decode_any W_26f0d0 = Some (OpImm ALU_ADD 5 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f0d4 : bv 32 := 0x05013823.
Lemma F_26f0d4 : fetch_word Plain.M.loaded_segments (0x26f110 : word) = Some W_26f0d4.
Proof. vm_refl. Qed.
Lemma D_26f0d4 : decode_any W_26f0d4 = Some (Store SZ8 2 16 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f0d8 : bv 32 := 0x05113c23.
Lemma F_26f0d8 : fetch_word Plain.M.loaded_segments (0x26f114 : word) = Some W_26f0d8.
Proof. vm_refl. Qed.
Lemma D_26f0d8 : decode_any W_26f0d8 = Some (Store SZ8 2 17 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f0dc : bv 32 := 0x0006c517.
Lemma F_26f0dc : fetch_word Plain.M.loaded_segments (0x26f118 : word) = Some W_26f0dc.
Proof. vm_refl. Qed.
Lemma D_26f0dc : decode_any W_26f0dc = Some (Auipc 10 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f0e0 : bv 32 := 0x00853483.
Lemma F_26f0e0 : fetch_word Plain.M.loaded_segments (0x26f11c : word) = Some W_26f0e0.
Proof. vm_refl. Qed.
Lemma D_26f0e0 : decode_any W_26f0e0 = Some (Load SZ8 true 9 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f0e4 : bv 32 := 0x02c13823.
Lemma F_26f0e4 : fetch_word Plain.M.loaded_segments (0x26f120 : word) = Some W_26f0e4.
Proof. vm_refl. Qed.
Lemma D_26f0e4 : decode_any W_26f0e4 = Some (Store SZ8 2 12 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f0e8 : bv 32 := 0x02d13c23.
Lemma F_26f0e8 : fetch_word Plain.M.loaded_segments (0x26f124 : word) = Some W_26f0e8.
Proof. vm_refl. Qed.
Lemma D_26f0e8 : decode_any W_26f0e8 = Some (Store SZ8 2 13 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f0ec : bv 32 := 0x04e13023.
Lemma F_26f0ec : fetch_word Plain.M.loaded_segments (0x26f128 : word) = Some W_26f0ec.
Proof. vm_refl. Qed.
Lemma D_26f0ec : decode_any W_26f0ec = Some (Store SZ8 2 14 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f0f0 : bv 32 := 0x04f13423.
Lemma F_26f0f0 : fetch_word Plain.M.loaded_segments (0x26f12c : word) = Some W_26f0f0.
Proof. vm_refl. Qed.
Lemma D_26f0f0 : decode_any W_26f0f0 = Some (Store SZ8 2 15 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f0f4 : bv 32 := 0x0004b503.
Lemma F_26f0f4 : fetch_word Plain.M.loaded_segments (0x26f130 : word) = Some W_26f0f4.
Proof. vm_refl. Qed.
Lemma D_26f0f4 : decode_any W_26f0f4 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f0f8 : bv 32 := 0x0405f593.
Lemma F_26f0f8 : fetch_word Plain.M.loaded_segments (0x26f134 : word) = Some W_26f0f8.
Proof. vm_refl. Qed.
Lemma D_26f0f8 : decode_any W_26f0f8 = Some (OpImm ALU_AND 11 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f0fc : bv 32 := 0x00a13823.
Lemma F_26f0fc : fetch_word Plain.M.loaded_segments (0x26f138 : word) = Some W_26f0fc.
Proof. vm_refl. Qed.
Lemma D_26f0fc : decode_any W_26f0fc = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f100 : bv 32 := 0x00059c63.
Lemma F_26f100 : fetch_word Plain.M.loaded_segments (0x26f13c : word) = Some W_26f100.
Proof. vm_refl. Qed.
Lemma D_26f100 : decode_any W_26f100 = Some (Branch BC_NE 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f104 : bv 32 := 0x00410537.
Lemma F_26f104 : fetch_word Plain.M.loaded_segments (0x26f140 : word) = Some W_26f104.
Proof. vm_refl. Qed.
Lemma D_26f104 : decode_any W_26f104 = Some (Lui 10 1040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f108 : bv 32 := 0x00a475b3.
Lemma F_26f108 : fetch_word Plain.M.loaded_segments (0x26f144 : word) = Some W_26f108.
Proof. vm_refl. Qed.
Lemma D_26f108 : decode_any W_26f108 = Some (Op ALU_AND 11 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f10c : bv 32 := 0x00a58663.
Lemma F_26f10c : fetch_word Plain.M.loaded_segments (0x26f148 : word) = Some W_26f10c.
Proof. vm_refl. Qed.
Lemma D_26f10c : decode_any W_26f10c = Some (Branch BC_EQ 11 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f110 : bv 32 := 0x00000713.
Lemma F_26f110 : fetch_word Plain.M.loaded_segments (0x26f14c : word) = Some W_26f110.
Proof. vm_refl. Qed.
Lemma D_26f110 : decode_any W_26f110 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f114 : bv 32 := 0x0080006f.
Lemma F_26f114 : fetch_word Plain.M.loaded_segments (0x26f150 : word) = Some W_26f114.
Proof. vm_refl. Qed.
Lemma D_26f114 : decode_any W_26f114 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f118 : bv 32 := 0x03016703.
Lemma F_26f118 : fetch_word Plain.M.loaded_segments (0x26f154 : word) = Some W_26f118.
Proof. vm_refl. Qed.
Lemma D_26f118 : decode_any W_26f118 = Some (Load SZ4 false 14 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f11c : bv 32 := 0x000086b7.
Lemma F_26f11c : fetch_word Plain.M.loaded_segments (0x26f158 : word) = Some W_26f11c.
Proof. vm_refl. Qed.
Lemma D_26f11c : decode_any W_26f11c = Some (Lui 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f120 : bv 32 := 0x00d466b3.
Lemma F_26f120 : fetch_word Plain.M.loaded_segments (0x26f15c : word) = Some W_26f120.
Proof. vm_refl. Qed.
Lemma D_26f120 : decode_any W_26f120 = Some (Op ALU_OR 13 8 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f124 : bv 32 := 0x03800513.
Lemma F_26f124 : fetch_word Plain.M.loaded_segments (0x26f160 : word) = Some W_26f124.
Proof. vm_refl. Qed.
Lemma D_26f124 : decode_any W_26f124 = Some (OpImm ALU_ADD 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f128 : bv 32 := 0xf9c00593.
Lemma F_26f128 : fetch_word Plain.M.loaded_segments (0x26f164 : word) = Some W_26f128.
Proof. vm_refl. Qed.
Lemma D_26f128 : decode_any W_26f128 = Some (OpImm ALU_ADD 11 0 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f12c : bv 32 := 0x00028613.
Lemma F_26f12c : fetch_word Plain.M.loaded_segments (0x26f168 : word) = Some W_26f12c.
Proof. vm_refl. Qed.
Lemma D_26f12c : decode_any W_26f12c = Some (OpImm ALU_ADD 12 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f130 : bv 32 := 0x00000793.
Lemma F_26f130 : fetch_word Plain.M.loaded_segments (0x26f16c : word) = Some W_26f130.
Proof. vm_refl. Qed.
Lemma D_26f130 : decode_any W_26f130 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f134 : bv 32 := 0x00000813.
Lemma F_26f134 : fetch_word Plain.M.loaded_segments (0x26f170 : word) = Some W_26f134.
Proof. vm_refl. Qed.
Lemma D_26f134 : decode_any W_26f134 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f138 : bv 32 := 0x1090b0ef.
Lemma F_26f138 : fetch_word Plain.M.loaded_segments (0x26f174 : word) = Some W_26f138.
Proof. vm_refl. Qed.
Lemma D_26f138 : decode_any W_26f138 = Some (Jal 1 47368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f13c : bv 32 := 0x02c41413.
Lemma F_26f13c : fetch_word Plain.M.loaded_segments (0x26f178 : word) = Some W_26f13c.
Proof. vm_refl. Qed.
Lemma D_26f13c : decode_any W_26f13c = Some (ShiftImm ALU_SLL 8 8 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f140 : bv 32 := 0x00050693.
Lemma F_26f140 : fetch_word Plain.M.loaded_segments (0x26f17c : word) = Some W_26f140.
Proof. vm_refl. Qed.
Lemma D_26f140 : decode_any W_26f140 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f144 : bv 32 := 0x02045663.
Lemma F_26f144 : fetch_word Plain.M.loaded_segments (0x26f180 : word) = Some W_26f144.
Proof. vm_refl. Qed.
Lemma D_26f144 : decode_any W_26f144 = Some (Branch BC_GE 8 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f148 : bv 32 := 0x80000537.
Lemma F_26f148 : fetch_word Plain.M.loaded_segments (0x26f184 : word) = Some W_26f148.
Proof. vm_refl. Qed.
Lemma D_26f148 : decode_any W_26f148 = Some (Lui 10 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f14c : bv 32 := 0xfff5051b.
Lemma F_26f14c : fetch_word Plain.M.loaded_segments (0x26f188 : word) = Some W_26f14c.
Proof. vm_refl. Qed.
Lemma D_26f14c : decode_any W_26f14c = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f150 : bv 32 := 0x00150593.
Lemma F_26f150 : fetch_word Plain.M.loaded_segments (0x26f18c : word) = Some W_26f150.
Proof. vm_refl. Qed.
Lemma D_26f150 : decode_any W_26f150 = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f154 : bv 32 := 0x00b6f5b3.
Lemma F_26f154 : fetch_word Plain.M.loaded_segments (0x26f190 : word) = Some W_26f154.
Proof. vm_refl. Qed.
Lemma D_26f154 : decode_any W_26f154 = Some (Op ALU_AND 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f158 : bv 32 := 0x00059c63.
Lemma F_26f158 : fetch_word Plain.M.loaded_segments (0x26f194 : word) = Some W_26f158.
Proof. vm_refl. Qed.
Lemma D_26f158 : decode_any W_26f158 = Some (Branch BC_NE 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f15c : bv 32 := 0x00a6f533.
Lemma F_26f15c : fetch_word Plain.M.loaded_segments (0x26f198 : word) = Some W_26f15c.
Proof. vm_refl. Qed.
Lemma D_26f15c : decode_any W_26f15c = Some (Op ALU_AND 10 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f160 : bv 32 := 0x01900893.
Lemma F_26f160 : fetch_word Plain.M.loaded_segments (0x26f19c : word) = Some W_26f160.
Proof. vm_refl. Qed.
Lemma D_26f160 : decode_any W_26f160 = Some (OpImm ALU_ADD 17 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f164 : bv 32 := 0x00200593.
Lemma F_26f164 : fetch_word Plain.M.loaded_segments (0x26f1a0 : word) = Some W_26f164.
Proof. vm_refl. Qed.
Lemma D_26f164 : decode_any W_26f164 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f168 : bv 32 := 0x00100613.
Lemma F_26f168 : fetch_word Plain.M.loaded_segments (0x26f1a4 : word) = Some W_26f168.
Proof. vm_refl. Qed.
Lemma D_26f168 : decode_any W_26f168 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f16c : bv 32 := 0x00000073.
Lemma F_26f16c : fetch_word Plain.M.loaded_segments (0x26f1a8 : word) = Some W_26f16c.
Proof. vm_refl. Qed.
Lemma D_26f16c : decode_any W_26f16c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_26f16c : is_ecall W_26f16c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26f170 : bv 32 := 0x0006851b.
Lemma F_26f170 : fetch_word Plain.M.loaded_segments (0x26f1ac : word) = Some W_26f170.
Proof. vm_refl. Qed.
Lemma D_26f170 : decode_any W_26f170 = Some (OpImm32 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f174 : bv 32 := 0x02c000ef.
Lemma F_26f174 : fetch_word Plain.M.loaded_segments (0x26f1b0 : word) = Some W_26f174.
Proof. vm_refl. Qed.
Lemma D_26f174 : decode_any W_26f174 = Some (Jal 1 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f178 : bv 32 := 0x0004b583.
Lemma F_26f178 : fetch_word Plain.M.loaded_segments (0x26f1b4 : word) = Some W_26f178.
Proof. vm_refl. Qed.
Lemma D_26f178 : decode_any W_26f178 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f17c : bv 32 := 0x01013603.
Lemma F_26f17c : fetch_word Plain.M.loaded_segments (0x26f1b8 : word) = Some W_26f17c.
Proof. vm_refl. Qed.
Lemma D_26f17c : decode_any W_26f17c = Some (Load SZ8 true 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f180 : bv 32 := 0x00c59e63.
Lemma F_26f180 : fetch_word Plain.M.loaded_segments (0x26f1bc : word) = Some W_26f180.
Proof. vm_refl. Qed.
Lemma D_26f180 : decode_any W_26f180 = Some (Branch BC_NE 11 12 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f184 : bv 32 := 0x0005051b.
Lemma F_26f184 : fetch_word Plain.M.loaded_segments (0x26f1c0 : word) = Some W_26f184.
Proof. vm_refl. Qed.
Lemma D_26f184 : decode_any W_26f184 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f188 : bv 32 := 0x02813083.
Lemma F_26f188 : fetch_word Plain.M.loaded_segments (0x26f1c4 : word) = Some W_26f188.
Proof. vm_refl. Qed.
Lemma D_26f188 : decode_any W_26f188 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f18c : bv 32 := 0x02013403.
Lemma F_26f18c : fetch_word Plain.M.loaded_segments (0x26f1c8 : word) = Some W_26f18c.
Proof. vm_refl. Qed.
Lemma D_26f18c : decode_any W_26f18c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f190 : bv 32 := 0x01813483.
Lemma F_26f190 : fetch_word Plain.M.loaded_segments (0x26f1cc : word) = Some W_26f190.
Proof. vm_refl. Qed.
Lemma D_26f190 : decode_any W_26f190 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f194 : bv 32 := 0x06010113.
Lemma F_26f194 : fetch_word Plain.M.loaded_segments (0x26f1d0 : word) = Some W_26f194.
Proof. vm_refl. Qed.
Lemma D_26f194 : decode_any W_26f194 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f198 : bv 32 := 0x00008067.
Lemma F_26f198 : fetch_word Plain.M.loaded_segments (0x26f1d4 : word) = Some W_26f198.
Proof. vm_refl. Qed.
Lemma D_26f198 : decode_any W_26f198 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f19c : bv 32 := 0xc05ff0ef.
Lemma F_26f19c : fetch_word Plain.M.loaded_segments (0x26f1d8 : word) = Some W_26f19c.
Proof. vm_refl. Qed.
Lemma D_26f19c : decode_any W_26f19c = Some (Jal 1 2096132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f1a0 : bv 32 := 0xfffff5b7.
Lemma F_26f1a0 : fetch_word Plain.M.loaded_segments (0x26f1dc : word) = Some W_26f1a0.
Proof. vm_refl. Qed.
Lemma D_26f1a0 : decode_any W_26f1a0 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f1a4 : bv 32 := 0x0015859b.
Lemma F_26f1a4 : fetch_word Plain.M.loaded_segments (0x26f1e0 : word) = Some W_26f1a4.
Proof. vm_refl. Qed.
Lemma D_26f1a4 : decode_any W_26f1a4 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f1a8 : bv 32 := 0x02b56663.
Lemma F_26f1a8 : fetch_word Plain.M.loaded_segments (0x26f1e4 : word) = Some W_26f1a8.
Proof. vm_refl. Qed.
Lemma D_26f1a8 : decode_any W_26f1a8 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f1ac : bv 32 := 0xff010113.
Lemma F_26f1ac : fetch_word Plain.M.loaded_segments (0x26f1e8 : word) = Some W_26f1ac.
Proof. vm_refl. Qed.
Lemma D_26f1ac : decode_any W_26f1ac = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f1b0 : bv 32 := 0x00113423.
Lemma F_26f1b0 : fetch_word Plain.M.loaded_segments (0x26f1ec : word) = Some W_26f1b0.
Proof. vm_refl. Qed.
Lemma D_26f1b0 : decode_any W_26f1b0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f1b4 : bv 32 := 0x00813023.
Lemma F_26f1b4 : fetch_word Plain.M.loaded_segments (0x26f1f0 : word) = Some W_26f1b4.
Proof. vm_refl. Qed.
Lemma D_26f1b4 : decode_any W_26f1b4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f1b8 : bv 32 := 0x40a0043b.
Lemma F_26f1b8 : fetch_word Plain.M.loaded_segments (0x26f1f4 : word) = Some W_26f1b8.
Proof. vm_refl. Qed.
Lemma D_26f1b8 : decode_any W_26f1b8 = Some (Op32 ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f1bc : bv 32 := 0xbedff0ef.
Lemma F_26f1bc : fetch_word Plain.M.loaded_segments (0x26f1f8 : word) = Some W_26f1bc.
Proof. vm_refl. Qed.
Lemma D_26f1bc : decode_any W_26f1bc = Some (Jal 1 2096108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f1c0 : bv 32 := 0x00852023.
Lemma F_26f1c0 : fetch_word Plain.M.loaded_segments (0x26f1fc : word) = Some W_26f1c0.
Proof. vm_refl. Qed.
Lemma D_26f1c0 : decode_any W_26f1c0 = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f1c4 : bv 32 := 0xfff00513.
Lemma F_26f1c4 : fetch_word Plain.M.loaded_segments (0x26f200 : word) = Some W_26f1c4.
Proof. vm_refl. Qed.
Lemma D_26f1c4 : decode_any W_26f1c4 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f1c8 : bv 32 := 0x00813083.
Lemma F_26f1c8 : fetch_word Plain.M.loaded_segments (0x26f204 : word) = Some W_26f1c8.
Proof. vm_refl. Qed.
Lemma D_26f1c8 : decode_any W_26f1c8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f1cc : bv 32 := 0x00013403.
Lemma F_26f1cc : fetch_word Plain.M.loaded_segments (0x26f208 : word) = Some W_26f1cc.
Proof. vm_refl. Qed.
Lemma D_26f1cc : decode_any W_26f1cc = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f1d0 : bv 32 := 0x01010113.
Lemma F_26f1d0 : fetch_word Plain.M.loaded_segments (0x26f20c : word) = Some W_26f1d0.
Proof. vm_refl. Qed.
Lemma D_26f1d0 : decode_any W_26f1d0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26f1d4 : bv 32 := 0x00008067.
Lemma F_26f1d4 : fetch_word Plain.M.loaded_segments (0x26f210 : word) = Some W_26f1d4.
Proof. vm_refl. Qed.
Lemma D_26f1d4 : decode_any W_26f1d4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
