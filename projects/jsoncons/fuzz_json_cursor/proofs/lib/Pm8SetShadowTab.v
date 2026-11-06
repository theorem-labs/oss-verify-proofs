(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition Wx_82994 : bv 32 := 0x00058613.
Lemma Fx_82994 : fetch_word Asan.M.loaded_segments (0x829e4 : word) = Some Wx_82994.
Proof. vm_refl. Qed.
Lemma Dx_82994 : decode_any Wx_82994 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82998 : bv 32 := 0x000d0597.
Lemma Fx_82998 : fetch_word Asan.M.loaded_segments (0x829e8 : word) = Some Wx_82998.
Proof. vm_refl. Qed.
Lemma Dx_82998 : decode_any Wx_82998 = Some (Auipc 11 208, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8299c : bv 32 := 0x7705b583.
Lemma Fx_8299c : fetch_word Asan.M.loaded_segments (0x829ec : word) = Some Wx_8299c.
Proof. vm_refl. Qed.
Lemma Dx_8299c : decode_any Wx_8299c = Some (Load SZ8 true 11 11 1904, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_829a0 : bv 32 := 0x0005b303.
Lemma Fx_829a0 : fetch_word Asan.M.loaded_segments (0x829f0 : word) = Some Wx_829a0.
Proof. vm_refl. Qed.
Lemma Dx_829a0 : decode_any Wx_829a0 = Some (Load SZ8 true 6 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_829a4 : bv 32 := 0x00000593.
Lemma Fx_829a4 : fetch_word Asan.M.loaded_segments (0x829f4 : word) = Some Wx_829a4.
Proof. vm_refl. Qed.
Lemma Dx_829a4 : decode_any Wx_829a4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_829a8 : bv 32 := 0x00030067.
Lemma Fx_829a8 : fetch_word Asan.M.loaded_segments (0x829f8 : word) = Some Wx_829a8.
Proof. vm_refl. Qed.
Lemma Dx_829a8 : decode_any Wx_829a8 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82a9c : bv 32 := 0x000d0617.
Lemma Fx_82a9c : fetch_word Asan.M.loaded_segments (0x82aec : word) = Some Wx_82a9c.
Proof. vm_refl. Qed.
Lemma Dx_82a9c : decode_any Wx_82a9c = Some (Auipc 12 208, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82aa0 : bv 32 := 0x66c63603.
Lemma Fx_82aa0 : fetch_word Asan.M.loaded_segments (0x82af0 : word) = Some Wx_82aa0.
Proof. vm_refl. Qed.
Lemma Dx_82aa0 : decode_any Wx_82aa0 = Some (Load SZ8 true 12 12 1644, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82aa4 : bv 32 := 0x00063303.
Lemma Fx_82aa4 : fetch_word Asan.M.loaded_segments (0x82af4 : word) = Some Wx_82aa4.
Proof. vm_refl. Qed.
Lemma Dx_82aa4 : decode_any Wx_82aa4 = Some (Load SZ8 true 6 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82aa8 : bv 32 := 0x00058613.
Lemma Fx_82aa8 : fetch_word Asan.M.loaded_segments (0x82af8 : word) = Some Wx_82aa8.
Proof. vm_refl. Qed.
Lemma Dx_82aa8 : decode_any Wx_82aa8 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82aac : bv 32 := 0x0f500593.
Lemma Fx_82aac : fetch_word Asan.M.loaded_segments (0x82afc : word) = Some Wx_82aac.
Proof. vm_refl. Qed.
Lemma Dx_82aac : decode_any Wx_82aac = Some (OpImm ALU_ADD 11 0 245, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82ab0 : bv 32 := 0x00030067.
Lemma Fx_82ab0 : fetch_word Asan.M.loaded_segments (0x82b00 : word) = Some Wx_82ab0.
Proof. vm_refl. Qed.
Lemma Dx_82ab0 : decode_any Wx_82ab0 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82ab4 : bv 32 := 0x000d0617.
Lemma Fx_82ab4 : fetch_word Asan.M.loaded_segments (0x82b04 : word) = Some Wx_82ab4.
Proof. vm_refl. Qed.
Lemma Dx_82ab4 : decode_any Wx_82ab4 = Some (Auipc 12 208, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82ab8 : bv 32 := 0x65463603.
Lemma Fx_82ab8 : fetch_word Asan.M.loaded_segments (0x82b08 : word) = Some Wx_82ab8.
Proof. vm_refl. Qed.
Lemma Dx_82ab8 : decode_any Wx_82ab8 = Some (Load SZ8 true 12 12 1620, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82abc : bv 32 := 0x00063303.
Lemma Fx_82abc : fetch_word Asan.M.loaded_segments (0x82b0c : word) = Some Wx_82abc.
Proof. vm_refl. Qed.
Lemma Dx_82abc : decode_any Wx_82abc = Some (Load SZ8 true 6 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82ac0 : bv 32 := 0x00058613.
Lemma Fx_82ac0 : fetch_word Asan.M.loaded_segments (0x82b10 : word) = Some Wx_82ac0.
Proof. vm_refl. Qed.
Lemma Dx_82ac0 : decode_any Wx_82ac0 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82ac4 : bv 32 := 0x0f800593.
Lemma Fx_82ac4 : fetch_word Asan.M.loaded_segments (0x82b14 : word) = Some Wx_82ac4.
Proof. vm_refl. Qed.
Lemma Dx_82ac4 : decode_any Wx_82ac4 = Some (OpImm ALU_ADD 11 0 248, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82ac8 : bv 32 := 0x00030067.
Lemma Fx_82ac8 : fetch_word Asan.M.loaded_segments (0x82b18 : word) = Some Wx_82ac8.
Proof. vm_refl. Qed.
Lemma Dx_82ac8 : decode_any Wx_82ac8 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

