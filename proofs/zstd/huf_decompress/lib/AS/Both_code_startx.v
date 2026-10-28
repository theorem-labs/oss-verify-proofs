(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.zstd.huf_decompress.images Require Import AsanUbsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_9e890 : bv 32 := 0x0004b503.
Lemma F_9e890 : fetch_word AsanUbsan.M.loaded_segments (0xa1260 : word) = Some W_9e890.
Proof. vm_refl. Qed.
Lemma D_9e890 : decode_any W_9e890 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e894 : bv 32 := 0x00848493.
Lemma F_9e894 : fetch_word AsanUbsan.M.loaded_segments (0xa1264 : word) = Some W_9e894.
Proof. vm_refl. Qed.
Lemma D_9e894 : decode_any W_9e894 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e898 : bv 32 := 0xfe051ce3.
Lemma F_9e898 : fetch_word AsanUbsan.M.loaded_segments (0xa1268 : word) = Some W_9e898.
Proof. vm_refl. Qed.
Lemma D_9e898 : decode_any W_9e898 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition W_9e94c : bv 32 := 0x00b53023.
Lemma F_9e94c : fetch_word AsanUbsan.M.loaded_segments (0xa131c : word) = Some W_9e94c.
Proof. vm_refl. Qed.
Lemma D_9e94c : decode_any W_9e94c = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e950 : bv 32 := 0x00158593.
Lemma F_9e950 : fetch_word AsanUbsan.M.loaded_segments (0xa1320 : word) = Some W_9e950.
Proof. vm_refl. Qed.
Lemma D_9e950 : decode_any W_9e950 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e954 : bv 32 := 0xfff5c683.
Lemma F_9e954 : fetch_word AsanUbsan.M.loaded_segments (0xa1324 : word) = Some W_9e954.
Proof. vm_refl. Qed.
Lemma D_9e954 : decode_any W_9e954 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e958 : bv 32 := 0xfec68ae3.
Lemma F_9e958 : fetch_word AsanUbsan.M.loaded_segments (0xa1328 : word) = Some W_9e958.
Proof. vm_refl. Qed.
Lemma D_9e958 : decode_any W_9e958 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e95c : bv 32 := 0xfe069ae3.
Lemma F_9e95c : fetch_word AsanUbsan.M.loaded_segments (0xa132c : word) = Some W_9e95c.
Proof. vm_refl. Qed.
Lemma D_9e95c : decode_any W_9e95c = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
