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
Definition W_77ff8 : bv 32 := @BV 32 0xff010113%Z I.
Lemma F_77ff8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x77ff8%Z I : word) = Some W_77ff8.
Proof. vm_refl. Qed.
Lemma D_77ff8 : decode_any W_77ff8 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4080%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ffc : bv 32 := @BV 32 0x00113423%Z I.
Lemma F_77ffc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x77ffc%Z I : word) = Some W_77ffc.
Proof. vm_refl. Qed.
Lemma D_77ffc : decode_any W_77ffc = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78000 : bv 32 := @BV 32 0x62d000ef%Z I.
Lemma F_78000 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x78000%Z I : word) = Some W_78000.
Proof. vm_refl. Qed.
Lemma D_78000 : decode_any W_78000 = Some (Jal (@BV 5 1%Z I) (@BV 21 3628%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78004 : bv 32 := @BV 32 0x00050c63%Z I.
Lemma F_78004 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x78004%Z I : word) = Some W_78004.
Proof. vm_refl. Qed.
Lemma D_78004 : decode_any W_78004 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78008 : bv 32 := @BV 32 0x7ff50513%Z I.
Lemma F_78008 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x78008%Z I : word) = Some W_78008.
Proof. vm_refl. Qed.
Lemma D_78008 : decode_any W_78008 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 2047%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7800c : bv 32 := @BV 32 0x2f150513%Z I.
Lemma F_7800c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7800c%Z I : word) = Some W_7800c.
Proof. vm_refl. Qed.
Lemma D_7800c : decode_any W_7800c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 753%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78010 : bv 32 := @BV 32 0x00813083%Z I.
Lemma F_78010 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x78010%Z I : word) = Some W_78010.
Proof. vm_refl. Qed.
Lemma D_78010 : decode_any W_78010 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78014 : bv 32 := @BV 32 0x01010113%Z I.
Lemma F_78014 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x78014%Z I : word) = Some W_78014.
Proof. vm_refl. Qed.
Lemma D_78014 : decode_any W_78014 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78018 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_78018 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x78018%Z I : word) = Some W_78018.
Proof. vm_refl. Qed.
Lemma D_78018 : decode_any W_78018 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.














































































