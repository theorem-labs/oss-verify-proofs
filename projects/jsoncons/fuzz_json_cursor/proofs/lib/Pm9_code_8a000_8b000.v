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

Definition W_8a008 : bv 32 := 0xff010113.
Lemma F_8a008 : fetch_word AsanUbsan.M.loaded_segments (0x8a050 : word) = Some W_8a008.
Proof. vm_refl. Qed.
Lemma D_8a008 : decode_any W_8a008 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_8a00c : bv 32 := 0x00113423.
Lemma F_8a00c : fetch_word AsanUbsan.M.loaded_segments (0x8a054 : word) = Some W_8a00c.
Proof. vm_refl. Qed.
Lemma D_8a00c : decode_any W_8a00c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8a010 : bv 32 := 0x62d000ef.
Lemma F_8a010 : fetch_word AsanUbsan.M.loaded_segments (0x8a058 : word) = Some W_8a010.
Proof. vm_refl. Qed.
Lemma D_8a010 : decode_any W_8a010 = Some (Jal 1 3628, 4%Z).
Proof. vm_refl. Qed.

Definition W_8a014 : bv 32 := 0x00050c63.
Lemma F_8a014 : fetch_word AsanUbsan.M.loaded_segments (0x8a05c : word) = Some W_8a014.
Proof. vm_refl. Qed.
Lemma D_8a014 : decode_any W_8a014 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8a018 : bv 32 := 0x7ff50513.
Lemma F_8a018 : fetch_word AsanUbsan.M.loaded_segments (0x8a060 : word) = Some W_8a018.
Proof. vm_refl. Qed.
Lemma D_8a018 : decode_any W_8a018 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_8a01c : bv 32 := 0x2f150513.
Lemma F_8a01c : fetch_word AsanUbsan.M.loaded_segments (0x8a064 : word) = Some W_8a01c.
Proof. vm_refl. Qed.
Lemma D_8a01c : decode_any W_8a01c = Some (OpImm ALU_ADD 10 10 753, 4%Z).
Proof. vm_refl. Qed.

Definition W_8a020 : bv 32 := 0x00813083.
Lemma F_8a020 : fetch_word AsanUbsan.M.loaded_segments (0x8a068 : word) = Some W_8a020.
Proof. vm_refl. Qed.
Lemma D_8a020 : decode_any W_8a020 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8a024 : bv 32 := 0x01010113.
Lemma F_8a024 : fetch_word AsanUbsan.M.loaded_segments (0x8a06c : word) = Some W_8a024.
Proof. vm_refl. Qed.
Lemma D_8a024 : decode_any W_8a024 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8a028 : bv 32 := 0x00008067.
Lemma F_8a028 : fetch_word AsanUbsan.M.loaded_segments (0x8a070 : word) = Some W_8a028.
Proof. vm_refl. Qed.
Lemma D_8a028 : decode_any W_8a028 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ae3c : bv 32 := 0xff010113.
Lemma F_8ae3c : fetch_word AsanUbsan.M.loaded_segments (0x8ae84 : word) = Some W_8ae3c.
Proof. vm_refl. Qed.
Lemma D_8ae3c : decode_any W_8ae3c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ae40 : bv 32 := 0x00113423.
Lemma F_8ae40 : fetch_word AsanUbsan.M.loaded_segments (0x8ae88 : word) = Some W_8ae40.
Proof. vm_refl. Qed.
Lemma D_8ae40 : decode_any W_8ae40 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ae44 : bv 32 := 0xe78f80ef.
Lemma F_8ae44 : fetch_word AsanUbsan.M.loaded_segments (0x8ae8c : word) = Some W_8ae44.
Proof. vm_refl. Qed.
Lemma D_8ae44 : decode_any W_8ae44 = Some (Jal 1 2066040, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ae48 : bv 32 := 0x00050463.
Lemma F_8ae48 : fetch_word AsanUbsan.M.loaded_segments (0x8ae90 : word) = Some W_8ae48.
Proof. vm_refl. Qed.
Lemma D_8ae48 : decode_any W_8ae48 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ae4c : bv 32 := 0x09853503.
Lemma F_8ae4c : fetch_word AsanUbsan.M.loaded_segments (0x8ae94 : word) = Some W_8ae4c.
Proof. vm_refl. Qed.
Lemma D_8ae4c : decode_any W_8ae4c = Some (Load SZ8 true 10 10 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ae50 : bv 32 := 0x00813083.
Lemma F_8ae50 : fetch_word AsanUbsan.M.loaded_segments (0x8ae98 : word) = Some W_8ae50.
Proof. vm_refl. Qed.
Lemma D_8ae50 : decode_any W_8ae50 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ae54 : bv 32 := 0x01010113.
Lemma F_8ae54 : fetch_word AsanUbsan.M.loaded_segments (0x8ae9c : word) = Some W_8ae54.
Proof. vm_refl. Qed.
Lemma D_8ae54 : decode_any W_8ae54 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ae58 : bv 32 := 0x00008067.
Lemma F_8ae58 : fetch_word AsanUbsan.M.loaded_segments (0x8aea0 : word) = Some W_8ae58.
Proof. vm_refl. Qed.
Lemma D_8ae58 : decode_any W_8ae58 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

