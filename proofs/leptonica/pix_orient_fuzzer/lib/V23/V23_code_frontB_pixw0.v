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

Definition W_6dc64 : bv 32 := 0x06a05a63.
Lemma F_6dc64 : fetch_word Ubsan.M.loaded_segments (0x6dc64 : word) = Some W_6dc64.
Proof. vm_refl. Qed.
Lemma D_6dc64 : decode_any W_6dc64 = Some (Branch BC_GE 0 10 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcd8 : bv 32 := 0x000b9517.
Lemma F_6dcd8 : fetch_word Ubsan.M.loaded_segments (0x6dcd8 : word) = Some W_6dcd8.
Proof. vm_refl. Qed.
Lemma D_6dcd8 : decode_any W_6dcd8 = Some (Auipc 10 185, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcdc : bv 32 := 0xd9853503.
Lemma F_6dcdc : fetch_word Ubsan.M.loaded_segments (0x6dcdc : word) = Some W_6dcdc.
Proof. vm_refl. Qed.
Lemma D_6dcdc : decode_any W_6dcdc = Some (Load SZ8 true 10 10 3480, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dce0 : bv 32 := 0x00052503.
Lemma F_6dce0 : fetch_word Ubsan.M.loaded_segments (0x6dce0 : word) = Some W_6dce0.
Proof. vm_refl. Qed.
Lemma D_6dce0 : decode_any W_6dce0 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dce4 : bv 32 := 0x00500593.
Lemma F_6dce4 : fetch_word Ubsan.M.loaded_segments (0x6dce4 : word) = Some W_6dce4.
Proof. vm_refl. Qed.
Lemma D_6dce4 : decode_any W_6dce4 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dce8 : bv 32 := 0x18a5c863.
Lemma F_6dce8 : fetch_word Ubsan.M.loaded_segments (0x6dce8 : word) = Some W_6dce8.
Proof. vm_refl. Qed.
Lemma D_6dce8 : decode_any W_6dce8 = Some (Branch BC_LT 11 10 400, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcec : bv 32 := 0xfffa2517.
Lemma F_6dcec : fetch_word Ubsan.M.loaded_segments (0x6dcec : word) = Some W_6dcec.
Proof. vm_refl. Qed.
Lemma D_6dcec : decode_any W_6dcec = Some (Auipc 10 1048482, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcf0 : bv 32 := 0xfffa8597.
Lemma F_6dcf0 : fetch_word Ubsan.M.loaded_segments (0x6dcf0 : word) = Some W_6dcf0.
Proof. vm_refl. Qed.
Lemma D_6dcf0 : decode_any W_6dcf0 = Some (Auipc 11 1048488, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcf4 : bv 32 := 0x6c150513.
Lemma F_6dcf4 : fetch_word Ubsan.M.loaded_segments (0x6dcf4 : word) = Some W_6dcf4.
Proof. vm_refl. Qed.
Lemma D_6dcf4 : decode_any W_6dcf4 = Some (OpImm ALU_ADD 10 10 1729, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcf8 : bv 32 := 0xd5858593.
Lemma F_6dcf8 : fetch_word Ubsan.M.loaded_segments (0x6dcf8 : word) = Some W_6dcf8.
Proof. vm_refl. Qed.
Lemma D_6dcf8 : decode_any W_6dcf8 = Some (OpImm ALU_ADD 11 11 3416, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcfc : bv 32 := 0x0c40006f.
Lemma F_6dcfc : fetch_word Ubsan.M.loaded_segments (0x6dcfc : word) = Some W_6dcfc.
Proof. vm_refl. Qed.
Lemma D_6dcfc : decode_any W_6dcfc = Some (Jal 0 196, 4%Z).
Proof. vm_refl. Qed.
