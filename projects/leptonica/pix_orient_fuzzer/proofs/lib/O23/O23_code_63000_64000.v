(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)




(* [comment removed for export] *)
Definition W_63000 : bv 32 := 0x00060413.
Lemma F_63000 : fetch_word Plain.M.loaded_segments (0x63058 : word) = Some W_63000.
Proof. vm_refl. Qed.
Lemma D_63000 : decode_any W_63000 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63004 : bv 32 := 0x00050613.
Lemma F_63004 : fetch_word Plain.M.loaded_segments (0x6305c : word) = Some W_63004.
Proof. vm_refl. Qed.
Lemma D_63004 : decode_any W_63004 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63008 : bv 32 := 0xfffbb517.
Lemma F_63008 : fetch_word Plain.M.loaded_segments (0x63060 : word) = Some W_63008.
Proof. vm_refl. Qed.
Lemma D_63008 : decode_any W_63008 = Some (Auipc 10 1048507, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6300c : bv 32 := 0x2c550513.
Lemma F_6300c : fetch_word Plain.M.loaded_segments (0x63064 : word) = Some W_6300c.
Proof. vm_refl. Qed.
Lemma D_6300c : decode_any W_6300c = Some (OpImm ALU_ADD 10 10 709, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63010 : bv 32 := 0x018000ef.
Lemma F_63010 : fetch_word Plain.M.loaded_segments (0x63068 : word) = Some W_63010.
Proof. vm_refl. Qed.
Lemma D_63010 : decode_any W_63010 = Some (Jal 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63014 : bv 32 := 0x00040513.
Lemma F_63014 : fetch_word Plain.M.loaded_segments (0x6306c : word) = Some W_63014.
Proof. vm_refl. Qed.
Lemma D_63014 : decode_any W_63014 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63018 : bv 32 := 0x00813083.
Lemma F_63018 : fetch_word Plain.M.loaded_segments (0x63070 : word) = Some W_63018.
Proof. vm_refl. Qed.
Lemma D_63018 : decode_any W_63018 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6301c : bv 32 := 0x00013403.
Lemma F_6301c : fetch_word Plain.M.loaded_segments (0x63074 : word) = Some W_6301c.
Proof. vm_refl. Qed.
Lemma D_6301c : decode_any W_6301c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63020 : bv 32 := 0x01010113.
Lemma F_63020 : fetch_word Plain.M.loaded_segments (0x63078 : word) = Some W_63020.
Proof. vm_refl. Qed.
Lemma D_63020 : decode_any W_63020 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63024 : bv 32 := 0x00008067.
Lemma F_63024 : fetch_word Plain.M.loaded_segments (0x6307c : word) = Some W_63024.
Proof. vm_refl. Qed.
Lemma D_63024 : decode_any W_63024 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630c4 : bv 32 := 0xff010113.
Lemma F_630c4 : fetch_word Plain.M.loaded_segments (0x6311c : word) = Some W_630c4.
Proof. vm_refl. Qed.
Lemma D_630c4 : decode_any W_630c4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630c8 : bv 32 := 0x00113423.
Lemma F_630c8 : fetch_word Plain.M.loaded_segments (0x63120 : word) = Some W_630c8.
Proof. vm_refl. Qed.
Lemma D_630c8 : decode_any W_630c8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630cc : bv 32 := 0x00813023.
Lemma F_630cc : fetch_word Plain.M.loaded_segments (0x63124 : word) = Some W_630cc.
Proof. vm_refl. Qed.
Lemma D_630cc : decode_any W_630cc = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630d0 : bv 32 := 0x00060413.
Lemma F_630d0 : fetch_word Plain.M.loaded_segments (0x63128 : word) = Some W_630d0.
Proof. vm_refl. Qed.
Lemma D_630d0 : decode_any W_630d0 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630d4 : bv 32 := 0x00050613.
Lemma F_630d4 : fetch_word Plain.M.loaded_segments (0x6312c : word) = Some W_630d4.
Proof. vm_refl. Qed.
Lemma D_630d4 : decode_any W_630d4 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630d8 : bv 32 := 0xfffbb517.
Lemma F_630d8 : fetch_word Plain.M.loaded_segments (0x63130 : word) = Some W_630d8.
Proof. vm_refl. Qed.
Lemma D_630d8 : decode_any W_630d8 = Some (Auipc 10 1048507, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630dc : bv 32 := 0x1f550513.
Lemma F_630dc : fetch_word Plain.M.loaded_segments (0x63134 : word) = Some W_630dc.
Proof. vm_refl. Qed.
Lemma D_630dc : decode_any W_630dc = Some (OpImm ALU_ADD 10 10 501, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630e0 : bv 32 := 0xf49ff0ef.
Lemma F_630e0 : fetch_word Plain.M.loaded_segments (0x63138 : word) = Some W_630e0.
Proof. vm_refl. Qed.
Lemma D_630e0 : decode_any W_630e0 = Some (Jal 1 2096968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630e4 : bv 32 := 0x00040513.
Lemma F_630e4 : fetch_word Plain.M.loaded_segments (0x6313c : word) = Some W_630e4.
Proof. vm_refl. Qed.
Lemma D_630e4 : decode_any W_630e4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630e8 : bv 32 := 0x00813083.
Lemma F_630e8 : fetch_word Plain.M.loaded_segments (0x63140 : word) = Some W_630e8.
Proof. vm_refl. Qed.
Lemma D_630e8 : decode_any W_630e8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630ec : bv 32 := 0x00013403.
Lemma F_630ec : fetch_word Plain.M.loaded_segments (0x63144 : word) = Some W_630ec.
Proof. vm_refl. Qed.
Lemma D_630ec : decode_any W_630ec = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630f0 : bv 32 := 0x01010113.
Lemma F_630f0 : fetch_word Plain.M.loaded_segments (0x63148 : word) = Some W_630f0.
Proof. vm_refl. Qed.
Lemma D_630f0 : decode_any W_630f0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630f4 : bv 32 := 0x00008067.
Lemma F_630f4 : fetch_word Plain.M.loaded_segments (0x6314c : word) = Some W_630f4.
Proof. vm_refl. Qed.
Lemma D_630f4 : decode_any W_630f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635fc : bv 32 := 0x02050e63.
Lemma F_635fc : fetch_word Plain.M.loaded_segments (0x63654 : word) = Some W_635fc.
Proof. vm_refl. Qed.
Lemma D_635fc : decode_any W_635fc = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63600 : bv 32 := 0xfe010113.
Lemma F_63600 : fetch_word Plain.M.loaded_segments (0x63658 : word) = Some W_63600.
Proof. vm_refl. Qed.
Lemma D_63600 : decode_any W_63600 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63604 : bv 32 := 0x00113c23.
Lemma F_63604 : fetch_word Plain.M.loaded_segments (0x6365c : word) = Some W_63604.
Proof. vm_refl. Qed.
Lemma D_63604 : decode_any W_63604 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63608 : bv 32 := 0x00813823.
Lemma F_63608 : fetch_word Plain.M.loaded_segments (0x63660 : word) = Some W_63608.
Proof. vm_refl. Qed.
Lemma D_63608 : decode_any W_63608 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6360c : bv 32 := 0x00913423.
Lemma F_6360c : fetch_word Plain.M.loaded_segments (0x63664 : word) = Some W_6360c.
Proof. vm_refl. Qed.
Lemma D_6360c : decode_any W_6360c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63610 : bv 32 := 0x00058493.
Lemma F_63610 : fetch_word Plain.M.loaded_segments (0x63668 : word) = Some W_63610.
Proof. vm_refl. Qed.
Lemma D_63610 : decode_any W_63610 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63614 : bv 32 := 0x00050413.
Lemma F_63614 : fetch_word Plain.M.loaded_segments (0x6366c : word) = Some W_63614.
Proof. vm_refl. Qed.
Lemma D_63614 : decode_any W_63614 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63618 : bv 32 := 0x00053503.
Lemma F_63618 : fetch_word Plain.M.loaded_segments (0x63670 : word) = Some W_63618.
Proof. vm_refl. Qed.
Lemma D_63618 : decode_any W_63618 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6361c : bv 32 := 0x00050463.
Lemma F_6361c : fetch_word Plain.M.loaded_segments (0x63674 : word) = Some W_6361c.
Proof. vm_refl. Qed.
Lemma D_6361c : decode_any W_6361c = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63624 : bv 32 := 0x04048063.
Lemma F_63624 : fetch_word Plain.M.loaded_segments (0x6367c : word) = Some W_63624.
Proof. vm_refl. Qed.
Lemma D_63624 : decode_any W_63624 = Some (Branch BC_EQ 9 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63664 : bv 32 := 0x00000593.
Lemma F_63664 : fetch_word Plain.M.loaded_segments (0x636bc : word) = Some W_63664.
Proof. vm_refl. Qed.
Lemma D_63664 : decode_any W_63664 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63668 : bv 32 := 0x00000513.
Lemma F_63668 : fetch_word Plain.M.loaded_segments (0x636c0 : word) = Some W_63668.
Proof. vm_refl. Qed.
Lemma D_63668 : decode_any W_63668 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6366c : bv 32 := 0x00b43023.
Lemma F_6366c : fetch_word Plain.M.loaded_segments (0x636c4 : word) = Some W_6366c.
Proof. vm_refl. Qed.
Lemma D_6366c : decode_any W_6366c = Some (Store SZ8 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63670 : bv 32 := 0x01813083.
Lemma F_63670 : fetch_word Plain.M.loaded_segments (0x636c8 : word) = Some W_63670.
Proof. vm_refl. Qed.
Lemma D_63670 : decode_any W_63670 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63674 : bv 32 := 0x01013403.
Lemma F_63674 : fetch_word Plain.M.loaded_segments (0x636cc : word) = Some W_63674.
Proof. vm_refl. Qed.
Lemma D_63674 : decode_any W_63674 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63678 : bv 32 := 0x00813483.
Lemma F_63678 : fetch_word Plain.M.loaded_segments (0x636d0 : word) = Some W_63678.
Proof. vm_refl. Qed.
Lemma D_63678 : decode_any W_63678 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6367c : bv 32 := 0x02010113.
Lemma F_6367c : fetch_word Plain.M.loaded_segments (0x636d4 : word) = Some W_6367c.
Proof. vm_refl. Qed.
Lemma D_6367c : decode_any W_6367c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63680 : bv 32 := 0x00008067.
Lemma F_63680 : fetch_word Plain.M.loaded_segments (0x636d8 : word) = Some W_63680.
Proof. vm_refl. Qed.
Lemma D_63680 : decode_any W_63680 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
