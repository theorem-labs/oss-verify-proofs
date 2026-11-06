(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.zstd.fse_read_ncount.images Require Import AsanUbsan.
Open Scope bv_scope.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Definition W_88bb8 : bv 32 := 0x0004b503.
Lemma F_88bb8 : fetch_word AsanUbsan.M.loaded_segments (0x88a48 : word) = Some W_88bb8.
Proof. vm_refl. Qed.
Lemma D_88bb8 : decode_any W_88bb8 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_88bbc : bv 32 := 0x00848493.
Lemma F_88bbc : fetch_word AsanUbsan.M.loaded_segments (0x88a4c : word) = Some W_88bbc.
Proof. vm_refl. Qed.
Lemma D_88bbc : decode_any W_88bbc = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_88bc0 : bv 32 := 0xfe051ce3.
Lemma F_88bc0 : fetch_word AsanUbsan.M.loaded_segments (0x88a50 : word) = Some W_88bc0.
Proof. vm_refl. Qed.
Lemma D_88bc0 : decode_any W_88bc0 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.
Definition W_88c74 : bv 32 := 0x00b53023.
Lemma F_88c74 : fetch_word AsanUbsan.M.loaded_segments (0x88b04 : word) = Some W_88c74.
Proof. vm_refl. Qed.
Lemma D_88c74 : decode_any W_88c74 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_88c78 : bv 32 := 0x00158593.
Lemma F_88c78 : fetch_word AsanUbsan.M.loaded_segments (0x88b08 : word) = Some W_88c78.
Proof. vm_refl. Qed.
Lemma D_88c78 : decode_any W_88c78 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_88c7c : bv 32 := 0xfff5c683.
Lemma F_88c7c : fetch_word AsanUbsan.M.loaded_segments (0x88b0c : word) = Some W_88c7c.
Proof. vm_refl. Qed.
Lemma D_88c7c : decode_any W_88c7c = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.
Definition W_88c80 : bv 32 := 0xfec68ae3.
Lemma F_88c80 : fetch_word AsanUbsan.M.loaded_segments (0x88b10 : word) = Some W_88c80.
Proof. vm_refl. Qed.
Lemma D_88c80 : decode_any W_88c80 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.
Definition W_88c84 : bv 32 := 0xfe069ae3.
Lemma F_88c84 : fetch_word AsanUbsan.M.loaded_segments (0x88b14 : word) = Some W_88c84.
Proof. vm_refl. Qed.
Lemma D_88c84 : decode_any W_88c84 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
