(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_bf150 : bv 32 := 0x0004b503.
Lemma F_bf150 : fetch_word AsanUbsan.M.loaded_segments (0xbf158 : word) = Some W_bf150.
Proof. vm_refl. Qed.
Lemma D_bf150 : decode_any W_bf150 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_bf154 : bv 32 := 0x00848493.
Lemma F_bf154 : fetch_word AsanUbsan.M.loaded_segments (0xbf15c : word) = Some W_bf154.
Proof. vm_refl. Qed.
Lemma D_bf154 : decode_any W_bf154 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_bf158 : bv 32 := 0xfe051ce3.
Lemma F_bf158 : fetch_word AsanUbsan.M.loaded_segments (0xbf160 : word) = Some W_bf158.
Proof. vm_refl. Qed.
Lemma D_bf158 : decode_any W_bf158 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_bf20c : bv 32 := 0x00b53023.
Lemma F_bf20c : fetch_word AsanUbsan.M.loaded_segments (0xbf214 : word) = Some W_bf20c.
Proof. vm_refl. Qed.
Lemma D_bf20c : decode_any W_bf20c = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_bf210 : bv 32 := 0x00158593.
Lemma F_bf210 : fetch_word AsanUbsan.M.loaded_segments (0xbf218 : word) = Some W_bf210.
Proof. vm_refl. Qed.
Lemma D_bf210 : decode_any W_bf210 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_bf214 : bv 32 := 0xfff5c683.
Lemma F_bf214 : fetch_word AsanUbsan.M.loaded_segments (0xbf21c : word) = Some W_bf214.
Proof. vm_refl. Qed.
Lemma D_bf214 : decode_any W_bf214 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_bf218 : bv 32 := 0xfec68ae3.
Lemma F_bf218 : fetch_word AsanUbsan.M.loaded_segments (0xbf220 : word) = Some W_bf218.
Proof. vm_refl. Qed.
Lemma D_bf218 : decode_any W_bf218 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_bf21c : bv 32 := 0xfe069ae3.
Lemma F_bf21c : fetch_word AsanUbsan.M.loaded_segments (0xbf224 : word) = Some W_bf21c.
Proof. vm_refl. Qed.
Lemma D_bf21c : decode_any W_bf21c = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
