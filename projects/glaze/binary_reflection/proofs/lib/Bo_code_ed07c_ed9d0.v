(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
From OSSVerify.Proofs.glaze.binary_reflection.lib.Common Require InstrEnc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- @eq (option (bv 32)) (fetch_word ?s ?a) ?r =>
      apply (@bool_decide_eq_true_1 _ (@decide_rel (option (bv 32)) (option (bv 32)) (@eq (option (bv 32))) (@option_eq_dec (bv 32) (bv_eq_dec 32)) (fetch_word s a) r));
      vm_cast_no_check (@eq_refl bool true)
  | |- @eq (option (prod instr Z)) (decode_any ?w) ?r =>
      (* [comment removed for export] *)
      apply (@InstrEnc.enc_opt_inj (decode_any w) r);
      vm_cast_no_check (@eq_refl (list Z) (InstrEnc.enc_opt r))
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_ed2e0 : bv 32 := @BV 32 0x0004b503%Z I.
Lemma F_ed2e0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xed2e0%Z I : word) = Some W_ed2e0.
Proof. vm_refl. Qed.
Lemma D_ed2e0 : decode_any W_ed2e0 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ed2e4 : bv 32 := @BV 32 0x00848493%Z I.
Lemma F_ed2e4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xed2e4%Z I : word) = Some W_ed2e4.
Proof. vm_refl. Qed.
Lemma D_ed2e4 : decode_any W_ed2e4 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 9%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ed2e8 : bv 32 := @BV 32 0xfe051ce3%Z I.
Lemma F_ed2e8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xed2e8%Z I : word) = Some W_ed2e8.
Proof. vm_refl. Qed.
Lemma D_ed2e8 : decode_any W_ed2e8 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 8184%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ed39c : bv 32 := @BV 32 0x00b53023%Z I.
Lemma F_ed39c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xed39c%Z I : word) = Some W_ed39c.
Proof. vm_refl. Qed.
Lemma D_ed39c : decode_any W_ed39c = Some (Store SZ8 (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ed3a0 : bv 32 := @BV 32 0x00158593%Z I.
Lemma F_ed3a0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xed3a0%Z I : word) = Some W_ed3a0.
Proof. vm_refl. Qed.
Lemma D_ed3a0 : decode_any W_ed3a0 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ed3a4 : bv 32 := @BV 32 0xfff5c683%Z I.
Lemma F_ed3a4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xed3a4%Z I : word) = Some W_ed3a4.
Proof. vm_refl. Qed.
Lemma D_ed3a4 : decode_any W_ed3a4 = Some (Load SZ1 false (@BV 5 13%Z I) (@BV 5 11%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ed3a8 : bv 32 := @BV 32 0xfec68ae3%Z I.
Lemma F_ed3a8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xed3a8%Z I : word) = Some W_ed3a8.
Proof. vm_refl. Qed.
Lemma D_ed3a8 : decode_any W_ed3a8 = Some (Branch BC_EQ (@BV 5 13%Z I) (@BV 5 12%Z I) (@BV 13 8180%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ed3ac : bv 32 := @BV 32 0xfe069ae3%Z I.
Lemma F_ed3ac : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xed3ac%Z I : word) = Some W_ed3ac.
Proof. vm_refl. Qed.
Lemma D_ed3ac : decode_any W_ed3ac = Some (Branch BC_NE (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 13 8180%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ed9c4 : bv 32 := @BV 32 0x00020513%Z I.
Lemma F_ed9c4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xed9b8%Z I : word) = Some W_ed9c4.
Proof. vm_refl. Qed.
Lemma D_ed9c4 : decode_any W_ed9c4 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 4%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ed9c8 : bv 32 := @BV 32 0xf5c50513%Z I.
Lemma F_ed9c8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xed9bc%Z I : word) = Some W_ed9c8.
Proof. vm_refl. Qed.
Lemma D_ed9c8 : decode_any W_ed9c8 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 3932%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ed9cc : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_ed9cc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xed9c0%Z I : word) = Some W_ed9cc.
Proof. vm_refl. Qed.
Lemma D_ed9cc : decode_any W_ed9cc = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.
