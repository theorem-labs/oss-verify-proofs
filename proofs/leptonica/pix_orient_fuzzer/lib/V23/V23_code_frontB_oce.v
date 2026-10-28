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

Definition W_af66c : bv 32 := 0x000a0a63.
Lemma F_af66c : fetch_word Ubsan.M.loaded_segments (0xaf66c : word) = Some W_af66c.
Proof. vm_refl. Qed.
Lemma D_af66c : decode_any W_af66c = Some (Branch BC_EQ 20 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_af670 : bv 32 := 0x003a7513.
Lemma F_af670 : fetch_word Ubsan.M.loaded_segments (0xaf670 : word) = Some W_af670.
Proof. vm_refl. Qed.
Lemma D_af670 : decode_any W_af670 = Some (OpImm ALU_AND 10 20 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_af674 : bv 32 := 0x22051463.
Lemma F_af674 : fetch_word Ubsan.M.loaded_segments (0xaf674 : word) = Some W_af674.
Proof. vm_refl. Qed.
Lemma D_af674 : decode_any W_af674 = Some (Branch BC_NE 10 0 552, 4%Z).
Proof. vm_refl. Qed.

Definition W_af678 : bv 32 := 0x01812787.
Lemma F_af678 : fetch_word Ubsan.M.loaded_segments (0xaf678 : word) = Some W_af678.
Proof. vm_refl. Qed.
Lemma D_af678 : decode_any W_af678 = Some (FLoad FMT_S 15 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_af67c : bv 32 := 0x00fa2027.
Lemma F_af67c : fetch_word Ubsan.M.loaded_segments (0xaf67c : word) = Some W_af67c.
Proof. vm_refl. Qed.
Lemma D_af67c : decode_any W_af67c = Some (FStore FMT_S 20 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_af680 : bv 32 := 0x06098863.
Lemma F_af680 : fetch_word Ubsan.M.loaded_segments (0xaf680 : word) = Some W_af680.
Proof. vm_refl. Qed.
Lemma D_af680 : decode_any W_af680 = Some (Branch BC_EQ 19 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_af684 : bv 32 := 0x0039f513.
Lemma F_af684 : fetch_word Ubsan.M.loaded_segments (0xaf684 : word) = Some W_af684.
Proof. vm_refl. Qed.
Lemma D_af684 : decode_any W_af684 = Some (OpImm ALU_AND 10 19 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_af688 : bv 32 := 0x20051a63.
Lemma F_af688 : fetch_word Ubsan.M.loaded_segments (0xaf688 : word) = Some W_af688.
Proof. vm_refl. Qed.
Lemma D_af688 : decode_any W_af688 = Some (Branch BC_NE 10 0 532, 4%Z).
Proof. vm_refl. Qed.

Definition W_af68c : bv 32 := 0x01412587.
Lemma F_af68c : fetch_word Ubsan.M.loaded_segments (0xaf68c : word) = Some W_af68c.
Proof. vm_refl. Qed.
Lemma D_af68c : decode_any W_af68c = Some (FLoad FMT_S 11 2 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_af690 : bv 32 := 0x00b9a027.
Lemma F_af690 : fetch_word Ubsan.M.loaded_segments (0xaf690 : word) = Some W_af690.
Proof. vm_refl. Qed.
Lemma D_af690 : decode_any W_af690 = Some (FStore FMT_S 19 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_af694 : bv 32 := 0x0600006f.
Lemma F_af694 : fetch_word Ubsan.M.loaded_segments (0xaf694 : word) = Some W_af694.
Proof. vm_refl. Qed.
Lemma D_af694 : decode_any W_af694 = Some (Jal 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_af6f0 : bv 32 := 0x01412587.
Lemma F_af6f0 : fetch_word Ubsan.M.loaded_segments (0xaf6f0 : word) = Some W_af6f0.
Proof. vm_refl. Qed.
Lemma D_af6f0 : decode_any W_af6f0 = Some (FLoad FMT_S 11 2 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_af6f4 : bv 32 := 0x01812507.
Lemma F_af6f4 : fetch_word Ubsan.M.loaded_segments (0xaf6f4 : word) = Some W_af6f4.
Proof. vm_refl. Qed.
Lemma D_af6f4 : decode_any W_af6f4 = Some (FLoad FMT_S 10 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_af6f8 : bv 32 := 0x01c10513.
Lemma F_af6f8 : fetch_word Ubsan.M.loaded_segments (0xaf6f8 : word) = Some W_af6f8.
Proof. vm_refl. Qed.
Lemma D_af6f8 : decode_any W_af6f8 = Some (OpImm ALU_ADD 10 2 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_af6fc : bv 32 := 0x20948653.
Lemma F_af6fc : fetch_word Ubsan.M.loaded_segments (0xaf6fc : word) = Some W_af6fc.
Proof. vm_refl. Qed.
Lemma D_af6fc : decode_any W_af6fc = Some (Fsgnj F_SGNJ FMT_S 12 9 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_af700 : bv 32 := 0x208406d3.
Lemma F_af700 : fetch_word Ubsan.M.loaded_segments (0xaf700 : word) = Some W_af700.
Proof. vm_refl. Qed.
Lemma D_af700 : decode_any W_af700 = Some (Fsgnj F_SGNJ FMT_S 13 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_af704 : bv 32 := 0x00090593.
Lemma F_af704 : fetch_word Ubsan.M.loaded_segments (0xaf704 : word) = Some W_af704.
Proof. vm_refl. Qed.
Lemma D_af704 : decode_any W_af704 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_af708 : bv 32 := 0x72c000ef.
Lemma F_af708 : fetch_word Ubsan.M.loaded_segments (0xaf708 : word) = Some W_af708.
Proof. vm_refl. Qed.
Lemma D_af708 : decode_any W_af708 = Some (Jal 1 1836, 4%Z).
Proof. vm_refl. Qed.
