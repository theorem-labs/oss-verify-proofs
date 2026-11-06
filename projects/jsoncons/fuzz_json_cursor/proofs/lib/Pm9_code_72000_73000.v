(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_725ec : bv 32 := 0xfe010113.
Lemma F_725ec : fetch_word AsanUbsan.M.loaded_segments (0x72634 : word) = Some W_725ec.
Proof. vm_refl. Qed.
Lemma D_725ec : decode_any W_725ec = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_725f0 : bv 32 := 0x00113c23.
Lemma F_725f0 : fetch_word AsanUbsan.M.loaded_segments (0x72638 : word) = Some W_725f0.
Proof. vm_refl. Qed.
Lemma D_725f0 : decode_any W_725f0 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_725f4 : bv 32 := 0x00813823.
Lemma F_725f4 : fetch_word AsanUbsan.M.loaded_segments (0x7263c : word) = Some W_725f4.
Proof. vm_refl. Qed.
Lemma D_725f4 : decode_any W_725f4 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_725f8 : bv 32 := 0x00913423.
Lemma F_725f8 : fetch_word AsanUbsan.M.loaded_segments (0x72640 : word) = Some W_725f8.
Proof. vm_refl. Qed.
Lemma D_725f8 : decode_any W_725f8 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_725fc : bv 32 := 0x01213023.
Lemma F_725fc : fetch_word AsanUbsan.M.loaded_segments (0x72644 : word) = Some W_725fc.
Proof. vm_refl. Qed.
Lemma D_725fc : decode_any W_725fc = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_72600 : bv 32 := 0x00050413.
Lemma F_72600 : fetch_word AsanUbsan.M.loaded_segments (0x72648 : word) = Some W_72600.
Proof. vm_refl. Qed.
Lemma D_72600 : decode_any W_72600 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_72604 : bv 32 := 0x038160ef.
Lemma F_72604 : fetch_word AsanUbsan.M.loaded_segments (0x7264c : word) = Some W_72604.
Proof. vm_refl. Qed.
Lemma D_72604 : decode_any W_72604 = Some (Jal 1 90168, 4%Z).
Proof. vm_refl. Qed.

Definition W_72608 : bv 32 := 0x000e4597.
Lemma F_72608 : fetch_word AsanUbsan.M.loaded_segments (0x72650 : word) = Some W_72608.
Proof. vm_refl. Qed.
Lemma D_72608 : decode_any W_72608 = Some (Auipc 11 228, 4%Z).
Proof. vm_refl. Qed.

Definition W_7260c : bv 32 := 0xdc85b583.
Lemma F_7260c : fetch_word AsanUbsan.M.loaded_segments (0x72654 : word) = Some W_7260c.
Proof. vm_refl. Qed.
Lemma D_7260c : decode_any W_7260c = Some (Load SZ8 true 11 11 3528, 4%Z).
Proof. vm_refl. Qed.

Definition W_72610 : bv 32 := 0x00050913.
Lemma F_72610 : fetch_word AsanUbsan.M.loaded_segments (0x72658 : word) = Some W_72610.
Proof. vm_refl. Qed.
Lemma D_72610 : decode_any W_72610 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_72614 : bv 32 := 0x00040513.
Lemma F_72614 : fetch_word AsanUbsan.M.loaded_segments (0x7265c : word) = Some W_72614.
Proof. vm_refl. Qed.
Lemma D_72614 : decode_any W_72614 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_72618 : bv 32 := 0x000580e7.
Lemma F_72618 : fetch_word AsanUbsan.M.loaded_segments (0x72660 : word) = Some W_72618.
Proof. vm_refl. Qed.
Lemma D_72618 : decode_any W_72618 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7261c : bv 32 := 0x00050493.
Lemma F_7261c : fetch_word AsanUbsan.M.loaded_segments (0x72664 : word) = Some W_7261c.
Proof. vm_refl. Qed.
Lemma D_7261c : decode_any W_7261c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_72620 : bv 32 := 0x02090663.
Lemma F_72620 : fetch_word AsanUbsan.M.loaded_segments (0x72668 : word) = Some W_72620.
Proof. vm_refl. Qed.
Lemma D_72620 : decode_any W_72620 = Some (Branch BC_EQ 18 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_72624 : bv 32 := 0x019180ef.
Lemma F_72624 : fetch_word AsanUbsan.M.loaded_segments (0x7266c : word) = Some W_72624.
Proof. vm_refl. Qed.
Lemma D_72624 : decode_any W_72624 = Some (Jal 1 100376, 4%Z).
Proof. vm_refl. Qed.

Definition W_72628 : bv 32 := 0x00050863.
Lemma F_72628 : fetch_word AsanUbsan.M.loaded_segments (0x72670 : word) = Some W_72628.
Proof. vm_refl. Qed.
Lemma D_72628 : decode_any W_72628 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7262c : bv 32 := 0x03053603.
Lemma F_7262c : fetch_word AsanUbsan.M.loaded_segments (0x72674 : word) = Some W_7262c.
Proof. vm_refl. Qed.
Lemma D_7262c : decode_any W_7262c = Some (Load SZ8 true 12 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_72630 : bv 32 := 0x03853683.
Lemma F_72630 : fetch_word AsanUbsan.M.loaded_segments (0x72678 : word) = Some W_72630.
Proof. vm_refl. Qed.
Lemma D_72630 : decode_any W_72630 = Some (Load SZ8 true 13 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_72634 : bv 32 := 0x00c0006f.
Lemma F_72634 : fetch_word AsanUbsan.M.loaded_segments (0x7267c : word) = Some W_72634.
Proof. vm_refl. Qed.
Lemma D_72634 : decode_any W_72634 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_72640 : bv 32 := 0x00040513.
Lemma F_72640 : fetch_word AsanUbsan.M.loaded_segments (0x72688 : word) = Some W_72640.
Proof. vm_refl. Qed.
Lemma D_72640 : decode_any W_72640 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_72644 : bv 32 := 0x00048593.
Lemma F_72644 : fetch_word AsanUbsan.M.loaded_segments (0x7268c : word) = Some W_72644.
Proof. vm_refl. Qed.
Lemma D_72644 : decode_any W_72644 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_72648 : bv 32 := 0x725250ef.
Lemma F_72648 : fetch_word AsanUbsan.M.loaded_segments (0x72690 : word) = Some W_72648.
Proof. vm_refl. Qed.
Lemma D_72648 : decode_any W_72648 = Some (Jal 1 155428, 4%Z).
Proof. vm_refl. Qed.

Definition W_7264c : bv 32 := 0x00048513.
Lemma F_7264c : fetch_word AsanUbsan.M.loaded_segments (0x72694 : word) = Some W_7264c.
Proof. vm_refl. Qed.
Lemma D_7264c : decode_any W_7264c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_72650 : bv 32 := 0x01813083.
Lemma F_72650 : fetch_word AsanUbsan.M.loaded_segments (0x72698 : word) = Some W_72650.
Proof. vm_refl. Qed.
Lemma D_72650 : decode_any W_72650 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_72654 : bv 32 := 0x01013403.
Lemma F_72654 : fetch_word AsanUbsan.M.loaded_segments (0x7269c : word) = Some W_72654.
Proof. vm_refl. Qed.
Lemma D_72654 : decode_any W_72654 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_72658 : bv 32 := 0x00813483.
Lemma F_72658 : fetch_word AsanUbsan.M.loaded_segments (0x726a0 : word) = Some W_72658.
Proof. vm_refl. Qed.
Lemma D_72658 : decode_any W_72658 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7265c : bv 32 := 0x00013903.
Lemma F_7265c : fetch_word AsanUbsan.M.loaded_segments (0x726a4 : word) = Some W_7265c.
Proof. vm_refl. Qed.
Lemma D_7265c : decode_any W_7265c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_72660 : bv 32 := 0x02010113.
Lemma F_72660 : fetch_word AsanUbsan.M.loaded_segments (0x726a8 : word) = Some W_72660.
Proof. vm_refl. Qed.
Lemma D_72660 : decode_any W_72660 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_72664 : bv 32 := 0x00008067.
Lemma F_72664 : fetch_word AsanUbsan.M.loaded_segments (0x726ac : word) = Some W_72664.
Proof. vm_refl. Qed.
Lemma D_72664 : decode_any W_72664 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

