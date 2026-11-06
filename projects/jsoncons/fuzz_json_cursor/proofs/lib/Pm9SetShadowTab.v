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

Definition Wx_82d5c : bv 32 := 0x00058613.
Lemma Fx_82d5c : fetch_word AsanUbsan.M.loaded_segments (0x82da4 : word) = Some Wx_82d5c.
Proof. vm_refl. Qed.
Lemma Dx_82d5c : decode_any Wx_82d5c = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d60 : bv 32 := 0x000d1597.
Lemma Fx_82d60 : fetch_word AsanUbsan.M.loaded_segments (0x82da8 : word) = Some Wx_82d60.
Proof. vm_refl. Qed.
Lemma Dx_82d60 : decode_any Wx_82d60 = Some (Auipc 11 209, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d64 : bv 32 := 0x7785b583.
Lemma Fx_82d64 : fetch_word AsanUbsan.M.loaded_segments (0x82dac : word) = Some Wx_82d64.
Proof. vm_refl. Qed.
Lemma Dx_82d64 : decode_any Wx_82d64 = Some (Load SZ8 true 11 11 1912, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d68 : bv 32 := 0x0005b303.
Lemma Fx_82d68 : fetch_word AsanUbsan.M.loaded_segments (0x82db0 : word) = Some Wx_82d68.
Proof. vm_refl. Qed.
Lemma Dx_82d68 : decode_any Wx_82d68 = Some (Load SZ8 true 6 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d6c : bv 32 := 0x00000593.
Lemma Fx_82d6c : fetch_word AsanUbsan.M.loaded_segments (0x82db4 : word) = Some Wx_82d6c.
Proof. vm_refl. Qed.
Lemma Dx_82d6c : decode_any Wx_82d6c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d70 : bv 32 := 0x00030067.
Lemma Fx_82d70 : fetch_word AsanUbsan.M.loaded_segments (0x82db8 : word) = Some Wx_82d70.
Proof. vm_refl. Qed.
Lemma Dx_82d70 : decode_any Wx_82d70 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e64 : bv 32 := 0x000d1617.
Lemma Fx_82e64 : fetch_word AsanUbsan.M.loaded_segments (0x82eac : word) = Some Wx_82e64.
Proof. vm_refl. Qed.
Lemma Dx_82e64 : decode_any Wx_82e64 = Some (Auipc 12 209, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e68 : bv 32 := 0x67463603.
Lemma Fx_82e68 : fetch_word AsanUbsan.M.loaded_segments (0x82eb0 : word) = Some Wx_82e68.
Proof. vm_refl. Qed.
Lemma Dx_82e68 : decode_any Wx_82e68 = Some (Load SZ8 true 12 12 1652, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e6c : bv 32 := 0x00063303.
Lemma Fx_82e6c : fetch_word AsanUbsan.M.loaded_segments (0x82eb4 : word) = Some Wx_82e6c.
Proof. vm_refl. Qed.
Lemma Dx_82e6c : decode_any Wx_82e6c = Some (Load SZ8 true 6 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e70 : bv 32 := 0x00058613.
Lemma Fx_82e70 : fetch_word AsanUbsan.M.loaded_segments (0x82eb8 : word) = Some Wx_82e70.
Proof. vm_refl. Qed.
Lemma Dx_82e70 : decode_any Wx_82e70 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e74 : bv 32 := 0x0f500593.
Lemma Fx_82e74 : fetch_word AsanUbsan.M.loaded_segments (0x82ebc : word) = Some Wx_82e74.
Proof. vm_refl. Qed.
Lemma Dx_82e74 : decode_any Wx_82e74 = Some (OpImm ALU_ADD 11 0 245, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e78 : bv 32 := 0x00030067.
Lemma Fx_82e78 : fetch_word AsanUbsan.M.loaded_segments (0x82ec0 : word) = Some Wx_82e78.
Proof. vm_refl. Qed.
Lemma Dx_82e78 : decode_any Wx_82e78 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e7c : bv 32 := 0x000d1617.
Lemma Fx_82e7c : fetch_word AsanUbsan.M.loaded_segments (0x82ec4 : word) = Some Wx_82e7c.
Proof. vm_refl. Qed.
Lemma Dx_82e7c : decode_any Wx_82e7c = Some (Auipc 12 209, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e80 : bv 32 := 0x65c63603.
Lemma Fx_82e80 : fetch_word AsanUbsan.M.loaded_segments (0x82ec8 : word) = Some Wx_82e80.
Proof. vm_refl. Qed.
Lemma Dx_82e80 : decode_any Wx_82e80 = Some (Load SZ8 true 12 12 1628, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e84 : bv 32 := 0x00063303.
Lemma Fx_82e84 : fetch_word AsanUbsan.M.loaded_segments (0x82ecc : word) = Some Wx_82e84.
Proof. vm_refl. Qed.
Lemma Dx_82e84 : decode_any Wx_82e84 = Some (Load SZ8 true 6 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e88 : bv 32 := 0x00058613.
Lemma Fx_82e88 : fetch_word AsanUbsan.M.loaded_segments (0x82ed0 : word) = Some Wx_82e88.
Proof. vm_refl. Qed.
Lemma Dx_82e88 : decode_any Wx_82e88 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e8c : bv 32 := 0x0f800593.
Lemma Fx_82e8c : fetch_word AsanUbsan.M.loaded_segments (0x82ed4 : word) = Some Wx_82e8c.
Proof. vm_refl. Qed.
Lemma Dx_82e8c : decode_any Wx_82e8c = Some (OpImm ALU_ADD 11 0 248, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e90 : bv 32 := 0x00030067.
Lemma Fx_82e90 : fetch_word AsanUbsan.M.loaded_segments (0x82ed8 : word) = Some Wx_82e90.
Proof. vm_refl. Qed.
Lemma Dx_82e90 : decode_any Wx_82e90 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

