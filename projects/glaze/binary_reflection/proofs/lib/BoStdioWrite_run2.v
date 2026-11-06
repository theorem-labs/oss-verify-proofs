(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.InstrEnc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Bo_code_f34c8_f34f8.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.

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
End Bo_code_f34c8_f34f8.
Module Bo_code_f3610_f37a8.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.

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
Definition W_f3618 : bv 32 := @BV 32 0xf9010113%Z I.
Lemma F_f3618 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf360c%Z I : word) = Some W_f3618.
Proof. vm_refl. Qed.
Lemma D_f3618 : decode_any W_f3618 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 3984%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f361c : bv 32 := @BV 32 0x06113423%Z I.
Lemma F_f361c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3610%Z I : word) = Some W_f361c.
Proof. vm_refl. Qed.
Lemma D_f361c : decode_any W_f361c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 104%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3620 : bv 32 := @BV 32 0x06813023%Z I.
Lemma F_f3620 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3614%Z I : word) = Some W_f3620.
Proof. vm_refl. Qed.
Lemma D_f3620 : decode_any W_f3620 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 96%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3624 : bv 32 := @BV 32 0x04913c23%Z I.
Lemma F_f3624 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3618%Z I : word) = Some W_f3624.
Proof. vm_refl. Qed.
Lemma D_f3624 : decode_any W_f3624 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 88%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3628 : bv 32 := @BV 32 0x05213823%Z I.
Lemma F_f3628 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf361c%Z I : word) = Some W_f3628.
Proof. vm_refl. Qed.
Lemma D_f3628 : decode_any W_f3628 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 80%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f362c : bv 32 := @BV 32 0x05313423%Z I.
Lemma F_f362c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3620%Z I : word) = Some W_f362c.
Proof. vm_refl. Qed.
Lemma D_f362c : decode_any W_f362c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 19%Z I) (@BV 12 72%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3630 : bv 32 := @BV 32 0x05413023%Z I.
Lemma F_f3630 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3624%Z I : word) = Some W_f3630.
Proof. vm_refl. Qed.
Lemma D_f3630 : decode_any W_f3630 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 20%Z I) (@BV 12 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3634 : bv 32 := @BV 32 0x03513c23%Z I.
Lemma F_f3634 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3628%Z I : word) = Some W_f3634.
Proof. vm_refl. Qed.
Lemma D_f3634 : decode_any W_f3634 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 21%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3638 : bv 32 := @BV 32 0x03613823%Z I.
Lemma F_f3638 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf362c%Z I : word) = Some W_f3638.
Proof. vm_refl. Qed.
Lemma D_f3638 : decode_any W_f3638 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 22%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f363c : bv 32 := @BV 32 0x00060413%Z I.
Lemma F_f363c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3630%Z I : word) = Some W_f363c.
Proof. vm_refl. Qed.
Lemma D_f363c : decode_any W_f363c = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3640 : bv 32 := @BV 32 0x00050493%Z I.
Lemma F_f3640 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3634%Z I : word) = Some W_f3640.
Proof. vm_refl. Qed.
Lemma D_f3640 : decode_any W_f3640 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3644 : bv 32 := @BV 32 0x00013517%Z I.
Lemma F_f3644 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3638%Z I : word) = Some W_f3644.
Proof. vm_refl. Qed.
Lemma D_f3644 : decode_any W_f3644 = Some (Auipc (@BV 5 10%Z I) (@BV 20 19%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3648 : bv 32 := @BV 32 0x62853a83%Z I.
Lemma F_f3648 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf363c%Z I : word) = Some W_f3648.
Proof. vm_refl. Qed.
Lemma D_f3648 : decode_any W_f3648 = Some (Load SZ8 true (@BV 5 21%Z I) (@BV 5 10%Z I) (@BV 12 1576%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f364c : bv 32 := @BV 32 0x000ab503%Z I.
Lemma F_f364c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3640%Z I : word) = Some W_f364c.
Proof. vm_refl. Qed.
Lemma D_f364c : decode_any W_f364c = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 21%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3650 : bv 32 := @BV 32 0x02a13423%Z I.
Lemma F_f3650 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3644%Z I : word) = Some W_f3650.
Proof. vm_refl. Qed.
Lemma D_f3650 : decode_any W_f3650 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 10%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3654 : bv 32 := @BV 32 0x0284b503%Z I.
Lemma F_f3654 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3648%Z I : word) = Some W_f3654.
Proof. vm_refl. Qed.
Lemma D_f3654 : decode_any W_f3654 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3658 : bv 32 := @BV 32 0x0384b603%Z I.
Lemma F_f3658 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf364c%Z I : word) = Some W_f3658.
Proof. vm_refl. Qed.
Lemma D_f3658 : decode_any W_f3658 = Some (Load SZ8 true (@BV 5 12%Z I) (@BV 5 9%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f365c : bv 32 := @BV 32 0x40c50b33%Z I.
Lemma F_f365c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3650%Z I : word) = Some W_f365c.
Proof. vm_refl. Qed.
Lemma D_f365c : decode_any W_f365c = Some (Op ALU_SUB (@BV 5 22%Z I) (@BV 5 10%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3660 : bv 32 := @BV 32 0x00c546b3%Z I.
Lemma F_f3660 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3654%Z I : word) = Some W_f3660.
Proof. vm_refl. Qed.
Lemma D_f3660 : decode_any W_f3660 = Some (Op ALU_XOR (@BV 5 13%Z I) (@BV 5 10%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3664 : bv 32 := @BV 32 0x00c13423%Z I.
Lemma F_f3664 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3658%Z I : word) = Some W_f3664.
Proof. vm_refl. Qed.
Lemma D_f3664 : decode_any W_f3664 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 12%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3668 : bv 32 := @BV 32 0x01613823%Z I.
Lemma F_f3668 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf365c%Z I : word) = Some W_f3668.
Proof. vm_refl. Qed.
Lemma D_f3668 : decode_any W_f3668 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 22%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f366c : bv 32 := @BV 32 0x00b13c23%Z I.
Lemma F_f366c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3660%Z I : word) = Some W_f366c.
Proof. vm_refl. Qed.
Lemma D_f366c : decode_any W_f366c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 11%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3670 : bv 32 := @BV 32 0x02813023%Z I.
Lemma F_f3670 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3664%Z I : word) = Some W_f3670.
Proof. vm_refl. Qed.
Lemma D_f3670 : decode_any W_f3670 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3674 : bv 32 := @BV 32 0x008b0b33%Z I.
Lemma F_f3674 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3668%Z I : word) = Some W_f3674.
Proof. vm_refl. Qed.
Lemma D_f3674 : decode_any W_f3674 = Some (Op ALU_ADD (@BV 5 22%Z I) (@BV 5 22%Z I) (@BV 5 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3678 : bv 32 := @BV 32 0x00d03933%Z I.
Lemma F_f3678 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf366c%Z I : word) = Some W_f3678.
Proof. vm_refl. Qed.
Lemma D_f3678 : decode_any W_f3678 = Some (Op ALU_SLTU (@BV 5 18%Z I) (@BV 5 0%Z I) (@BV 5 13%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f367c : bv 32 := @BV 32 0x00c50663%Z I.
Lemma F_f367c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3670%Z I : word) = Some W_f367c.
Proof. vm_refl. Qed.
Lemma D_f367c : decode_any W_f367c = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 12%Z I) (@BV 13 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3680 : bv 32 := @BV 32 0x00810993%Z I.
Lemma F_f3680 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3674%Z I : word) = Some W_f3680.
Proof. vm_refl. Qed.
Lemma D_f3680 : decode_any W_f3680 = Some (OpImm ALU_ADD (@BV 5 19%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3684 : bv 32 := @BV 32 0x0080006f%Z I.
Lemma F_f3684 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3678%Z I : word) = Some W_f3684.
Proof. vm_refl. Qed.
Lemma D_f3684 : decode_any W_f3684 = Some (Jal (@BV 5 0%Z I) (@BV 21 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3688 : bv 32 := @BV 32 0x01810993%Z I.
Lemma F_f3688 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf367c%Z I : word) = Some W_f3688.
Proof. vm_refl. Qed.
Lemma D_f3688 : decode_any W_f3688 = Some (OpImm ALU_ADD (@BV 5 19%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f368c : bv 32 := @BV 32 0x0784a503%Z I.
Lemma F_f368c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3680%Z I : word) = Some W_f368c.
Proof. vm_refl. Qed.
Lemma D_f368c : decode_any W_f368c = Some (Load SZ4 true (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 12 120%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3690 : bv 32 := @BV 32 0x00190913%Z I.
Lemma F_f3690 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3684%Z I : word) = Some W_f3690.
Proof. vm_refl. Qed.
Lemma D_f3690 : decode_any W_f3690 = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 18%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3694 : bv 32 := @BV 32 0x04200893%Z I.
Lemma F_f3694 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3688%Z I : word) = Some W_f3694.
Proof. vm_refl. Qed.
Lemma D_f3694 : decode_any W_f3694 = Some (OpImm ALU_ADD (@BV 5 17%Z I) (@BV 5 0%Z I) (@BV 12 66%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3698 : bv 32 := @BV 32 0x00098593%Z I.
Lemma F_f3698 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf368c%Z I : word) = Some W_f3698.
Proof. vm_refl. Qed.
Lemma D_f3698 : decode_any W_f3698 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f369c : bv 32 := @BV 32 0x00090613%Z I.
Lemma F_f369c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3690%Z I : word) = Some W_f369c.
Proof. vm_refl. Qed.
Lemma D_f369c : decode_any W_f369c = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f36a0 : bv 32 := @BV 32 0x00000073%Z I.
Lemma F_f36a0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3694%Z I : word) = Some W_f36a0.
Proof. vm_refl. Qed.

Lemma E_f36a0 : is_ecall W_f36a0 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_f36a4 : bv 32 := @BV 32 0x985fa0ef%Z I.
Lemma F_f36a4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3698%Z I : word) = Some W_f36a4.
Proof. vm_refl. Qed.
Lemma D_f36a4 : decode_any W_f36a4 = Some (Jal (@BV 5 1%Z I) (@BV 21 2075012%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f36a8 : bv 32 := @BV 32 0x09651863%Z I.
Lemma F_f36a8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf369c%Z I : word) = Some W_f36a8.
Proof. vm_refl. Qed.
Lemma D_f36a8 : decode_any W_f36a8 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 22%Z I) (@BV 13 144%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f36ac : bv 32 := @BV 32 0x0584b503%Z I.
Lemma F_f36ac : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf36a0%Z I : word) = Some W_f36ac.
Proof. vm_refl. Qed.
Lemma D_f36ac : decode_any W_f36ac = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 12 88%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f36b0 : bv 32 := @BV 32 0x0604b583%Z I.
Lemma F_f36b0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf36a4%Z I : word) = Some W_f36b0.
Proof. vm_refl. Qed.
Lemma D_f36b0 : decode_any W_f36b0 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 12 96%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f36b4 : bv 32 := @BV 32 0x00b505b3%Z I.
Lemma F_f36b4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf36a8%Z I : word) = Some W_f36b4.
Proof. vm_refl. Qed.
Lemma D_f36b4 : decode_any W_f36b4 = Some (Op ALU_ADD (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f36b8 : bv 32 := @BV 32 0x02b4b023%Z I.
Lemma F_f36b8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf36ac%Z I : word) = Some W_f36b8.
Proof. vm_refl. Qed.
Lemma D_f36b8 : decode_any W_f36b8 = Some (Store SZ8 (@BV 5 9%Z I) (@BV 5 11%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f36bc : bv 32 := @BV 32 0x02a4b423%Z I.
Lemma F_f36bc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf36b0%Z I : word) = Some W_f36bc.
Proof. vm_refl. Qed.
Lemma D_f36bc : decode_any W_f36bc = Some (Store SZ8 (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f36c0 : bv 32 := @BV 32 0x02a4bc23%Z I.
Lemma F_f36c0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf36b4%Z I : word) = Some W_f36c0.
Proof. vm_refl. Qed.
Lemma D_f36c0 : decode_any W_f36c0 = Some (Store SZ8 (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f36c4 : bv 32 := @BV 32 0x00040513%Z I.
Lemma F_f36c4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf36b8%Z I : word) = Some W_f36c4.
Proof. vm_refl. Qed.
Lemma D_f36c4 : decode_any W_f36c4 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f36c8 : bv 32 := @BV 32 0x000ab583%Z I.
Lemma F_f36c8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf36bc%Z I : word) = Some W_f36c8.
Proof. vm_refl. Qed.
Lemma D_f36c8 : decode_any W_f36c8 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 21%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f36cc : bv 32 := @BV 32 0x02813603%Z I.
Lemma F_f36cc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf36c0%Z I : word) = Some W_f36cc.
Proof. vm_refl. Qed.
Lemma D_f36cc : decode_any W_f36cc = Some (Load SZ8 true (@BV 5 12%Z I) (@BV 5 2%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f36d0 : bv 32 := @BV 32 0x0cc59a63%Z I.
Lemma F_f36d0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf36c4%Z I : word) = Some W_f36d0.
Proof. vm_refl. Qed.
Lemma D_f36d0 : decode_any W_f36d0 = Some (Branch BC_NE (@BV 5 11%Z I) (@BV 5 12%Z I) (@BV 13 212%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f36d4 : bv 32 := @BV 32 0x06813083%Z I.
Lemma F_f36d4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf36c8%Z I : word) = Some W_f36d4.
Proof. vm_refl. Qed.
Lemma D_f36d4 : decode_any W_f36d4 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 104%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f36d8 : bv 32 := @BV 32 0x06013403%Z I.
Lemma F_f36d8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf36cc%Z I : word) = Some W_f36d8.
Proof. vm_refl. Qed.
Lemma D_f36d8 : decode_any W_f36d8 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 96%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f36dc : bv 32 := @BV 32 0x05813483%Z I.
Lemma F_f36dc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf36d0%Z I : word) = Some W_f36dc.
Proof. vm_refl. Qed.
Lemma D_f36dc : decode_any W_f36dc = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 88%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f36e0 : bv 32 := @BV 32 0x05013903%Z I.
Lemma F_f36e0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf36d4%Z I : word) = Some W_f36e0.
Proof. vm_refl. Qed.
Lemma D_f36e0 : decode_any W_f36e0 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 80%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f36e4 : bv 32 := @BV 32 0x04813983%Z I.
Lemma F_f36e4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf36d8%Z I : word) = Some W_f36e4.
Proof. vm_refl. Qed.
Lemma D_f36e4 : decode_any W_f36e4 = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 2%Z I) (@BV 12 72%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f36e8 : bv 32 := @BV 32 0x04013a03%Z I.
Lemma F_f36e8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf36dc%Z I : word) = Some W_f36e8.
Proof. vm_refl. Qed.
Lemma D_f36e8 : decode_any W_f36e8 = Some (Load SZ8 true (@BV 5 20%Z I) (@BV 5 2%Z I) (@BV 12 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f36ec : bv 32 := @BV 32 0x03813a83%Z I.
Lemma F_f36ec : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf36e0%Z I : word) = Some W_f36ec.
Proof. vm_refl. Qed.
Lemma D_f36ec : decode_any W_f36ec = Some (Load SZ8 true (@BV 5 21%Z I) (@BV 5 2%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f36f0 : bv 32 := @BV 32 0x03013b03%Z I.
Lemma F_f36f0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf36e4%Z I : word) = Some W_f36f0.
Proof. vm_refl. Qed.
Lemma D_f36f0 : decode_any W_f36f0 = Some (Load SZ8 true (@BV 5 22%Z I) (@BV 5 2%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f36f4 : bv 32 := @BV 32 0x07010113%Z I.
Lemma F_f36f4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf36e8%Z I : word) = Some W_f36f4.
Proof. vm_refl. Qed.
Lemma D_f36f4 : decode_any W_f36f4 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 112%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f36f8 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_f36f8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf36ec%Z I : word) = Some W_f36f8.
Proof. vm_refl. Qed.
Lemma D_f36f8 : decode_any W_f36f8 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f36fc : bv 32 := @BV 32 0x00800713%Z I.
Lemma F_f36fc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf36f0%Z I : word) = Some W_f36fc.
Proof. vm_refl. Qed.
Lemma D_f36fc : decode_any W_f36fc = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3700 : bv 32 := @BV 32 0x000a0593%Z I.
Lemma F_f3700 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf36f4%Z I : word) = Some W_f3700.
Proof. vm_refl. Qed.
Lemma D_f3700 : decode_any W_f3700 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 20%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3704 : bv 32 := @BV 32 0x00e98733%Z I.
Lemma F_f3704 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf36f8%Z I : word) = Some W_f3704.
Proof. vm_refl. Qed.
Lemma D_f3704 : decode_any W_f3704 = Some (Op ALU_ADD (@BV 5 14%Z I) (@BV 5 19%Z I) (@BV 5 14%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3708 : bv 32 := @BV 32 0x00073783%Z I.
Lemma F_f3708 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf36fc%Z I : word) = Some W_f3708.
Proof. vm_refl. Qed.
Lemma D_f3708 : decode_any W_f3708 = Some (Load SZ8 true (@BV 5 15%Z I) (@BV 5 14%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f370c : bv 32 := @BV 32 0x40ab0b33%Z I.
Lemma F_f370c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3700%Z I : word) = Some W_f370c.
Proof. vm_refl. Qed.
Lemma D_f370c : decode_any W_f370c = Some (Op ALU_SUB (@BV 5 22%Z I) (@BV 5 22%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3710 : bv 32 := @BV 32 0x0784a503%Z I.
Lemma F_f3710 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3704%Z I : word) = Some W_f3710.
Proof. vm_refl. Qed.
Lemma D_f3710 : decode_any W_f3710 = Some (Load SZ4 true (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 12 120%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3714 : bv 32 := @BV 32 0x40c9093b%Z I.
Lemma F_f3714 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3708%Z I : word) = Some W_f3714.
Proof. vm_refl. Qed.
Lemma D_f3714 : decode_any W_f3714 = Some (Op32 ALU_SUB (@BV 5 18%Z I) (@BV 5 18%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3718 : bv 32 := @BV 32 0x40d787b3%Z I.
Lemma F_f3718 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf370c%Z I : word) = Some W_f3718.
Proof. vm_refl. Qed.
Lemma D_f3718 : decode_any W_f3718 = Some (Op ALU_SUB (@BV 5 15%Z I) (@BV 5 15%Z I) (@BV 5 13%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f371c : bv 32 := @BV 32 0x00f73023%Z I.
Lemma F_f371c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3710%Z I : word) = Some W_f371c.
Proof. vm_refl. Qed.
Lemma D_f371c : decode_any W_f371c = Some (Store SZ8 (@BV 5 14%Z I) (@BV 5 15%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3720 : bv 32 := @BV 32 0x04200893%Z I.
Lemma F_f3720 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3714%Z I : word) = Some W_f3720.
Proof. vm_refl. Qed.
Lemma D_f3720 : decode_any W_f3720 = Some (OpImm ALU_ADD (@BV 5 17%Z I) (@BV 5 0%Z I) (@BV 12 66%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3724 : bv 32 := @BV 32 0x00090613%Z I.
Lemma F_f3724 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3718%Z I : word) = Some W_f3724.
Proof. vm_refl. Qed.
Lemma D_f3724 : decode_any W_f3724 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3728 : bv 32 := @BV 32 0x00000073%Z I.
Lemma F_f3728 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf371c%Z I : word) = Some W_f3728.
Proof. vm_refl. Qed.

Lemma E_f3728 : is_ecall W_f3728 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_f372c : bv 32 := @BV 32 0x8fdfa0ef%Z I.
Lemma F_f372c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3720%Z I : word) = Some W_f372c.
Proof. vm_refl. Qed.
Lemma D_f372c : decode_any W_f372c = Some (Jal (@BV 5 1%Z I) (@BV 21 2074876%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3730 : bv 32 := @BV 32 0x000a0993%Z I.
Lemma F_f3730 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3724%Z I : word) = Some W_f3730.
Proof. vm_refl. Qed.
Lemma D_f3730 : decode_any W_f3730 = Some (OpImm ALU_ADD (@BV 5 19%Z I) (@BV 5 20%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3734 : bv 32 := @BV 32 0xf7650ce3%Z I.
Lemma F_f3734 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3728%Z I : word) = Some W_f3734.
Proof. vm_refl. Qed.
Lemma D_f3734 : decode_any W_f3734 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 22%Z I) (@BV 13 8056%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3738 : bv 32 := @BV 32 0x02054c63%Z I.
Lemma F_f3738 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf372c%Z I : word) = Some W_f3738.
Proof. vm_refl. Qed.
Lemma D_f3738 : decode_any W_f3738 = Some (Branch BC_LT (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f373c : bv 32 := @BV 32 0x0089b583%Z I.
Lemma F_f373c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3730%Z I : word) = Some W_f373c.
Proof. vm_refl. Qed.
Lemma D_f373c : decode_any W_f373c = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 19%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3740 : bv 32 := @BV 32 0x00a5b633%Z I.
Lemma F_f3740 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3734%Z I : word) = Some W_f3740.
Proof. vm_refl. Qed.
Lemma D_f3740 : decode_any W_f3740 = Some (Op ALU_SLTU (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3744 : bv 32 := @BV 32 0x00461a13%Z I.
Lemma F_f3744 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3738%Z I : word) = Some W_f3744.
Proof. vm_refl. Qed.
Lemma D_f3744 : decode_any W_f3744 = Some (ShiftImm ALU_SLL (@BV 5 20%Z I) (@BV 5 12%Z I) (@BV 6 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3748 : bv 32 := @BV 32 0x01498a33%Z I.
Lemma F_f3748 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf373c%Z I : word) = Some W_f3748.
Proof. vm_refl. Qed.
Lemma D_f3748 : decode_any W_f3748 = Some (Op ALU_ADD (@BV 5 20%Z I) (@BV 5 19%Z I) (@BV 5 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f374c : bv 32 := @BV 32 0x000a3703%Z I.
Lemma F_f374c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3740%Z I : word) = Some W_f374c.
Proof. vm_refl. Qed.
Lemma D_f374c : decode_any W_f374c = Some (Load SZ8 true (@BV 5 14%Z I) (@BV 5 20%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3750 : bv 32 := @BV 32 0x40c006b3%Z I.
Lemma F_f3750 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3744%Z I : word) = Some W_f3750.
Proof. vm_refl. Qed.
Lemma D_f3750 : decode_any W_f3750 = Some (Op ALU_SUB (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3754 : bv 32 := @BV 32 0x00b6f6b3%Z I.
Lemma F_f3754 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3748%Z I : word) = Some W_f3754.
Proof. vm_refl. Qed.
Lemma D_f3754 : decode_any W_f3754 = Some (Op ALU_AND (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3758 : bv 32 := @BV 32 0x40d506b3%Z I.
Lemma F_f3758 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf374c%Z I : word) = Some W_f3758.
Proof. vm_refl. Qed.
Lemma D_f3758 : decode_any W_f3758 = Some (Op ALU_SUB (@BV 5 13%Z I) (@BV 5 10%Z I) (@BV 5 13%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f375c : bv 32 := @BV 32 0x00d70733%Z I.
Lemma F_f375c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3750%Z I : word) = Some W_f375c.
Proof. vm_refl. Qed.
Lemma D_f375c : decode_any W_f375c = Some (Op ALU_ADD (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 5 13%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3760 : bv 32 := @BV 32 0x00ea3023%Z I.
Lemma F_f3760 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3754%Z I : word) = Some W_f3760.
Proof. vm_refl. Qed.
Lemma D_f3760 : decode_any W_f3760 = Some (Store SZ8 (@BV 5 20%Z I) (@BV 5 14%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3764 : bv 32 := @BV 32 0xf8a5fce3%Z I.
Lemma F_f3764 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3758%Z I : word) = Some W_f3764.
Proof. vm_refl. Qed.
Lemma D_f3764 : decode_any W_f3764 = Some (Branch BC_GEU (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 13 8088%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f3768 : bv 32 := @BV 32 0x01800713%Z I.
Lemma F_f3768 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf375c%Z I : word) = Some W_f3768.
Proof. vm_refl. Qed.
Lemma D_f3768 : decode_any W_f3768 = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f376c : bv 32 := @BV 32 0xf95ff06f%Z I.
Lemma F_f376c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xf3760%Z I : word) = Some W_f376c.
Proof. vm_refl. Qed.
Lemma D_f376c : decode_any W_f376c = Some (Jal (@BV 5 0%Z I) (@BV 21 2097044%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_f3610_f37a8.
Module Bo_code_f3bf8_f3d9c.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.

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
End Bo_code_f3bf8_f3d9c.
Module Bo_code_f3fbc_f423c.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.

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
End Bo_code_f3fbc_f423c.
Module Bo_code_f43a4_f4964.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.

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
End Bo_code_f43a4_f4964.
Module Bo_code_edf44_ee420.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.

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
Definition W_ee028 : bv 32 := @BV 32 0xfffff5b7%Z I.
Lemma F_ee028 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xee01c%Z I : word) = Some W_ee028.
Proof. vm_refl. Qed.
Lemma D_ee028 : decode_any W_ee028 = Some (Lui (@BV 5 11%Z I) (@BV 20 1048575%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ee02c : bv 32 := @BV 32 0x0015859b%Z I.
Lemma F_ee02c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xee020%Z I : word) = Some W_ee02c.
Proof. vm_refl. Qed.
Lemma D_ee02c : decode_any W_ee02c = Some (OpImm32 (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ee030 : bv 32 := @BV 32 0x02b56663%Z I.
Lemma F_ee030 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xee024%Z I : word) = Some W_ee030.
Proof. vm_refl. Qed.
Lemma D_ee030 : decode_any W_ee030 = Some (Branch BC_LTU (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 13 44%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ee05c : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_ee05c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xee050%Z I : word) = Some W_ee05c.
Proof. vm_refl. Qed.
Lemma D_ee05c : decode_any W_ee05c = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_edf44_ee420.
Module Bo_code_ee7cc_ef130.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.

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
End Bo_code_ee7cc_ef130.
Require Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoStdioDefs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel.
Export OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.






(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPGen0.
Context {fx : FPState}.

Lemma bo_wseg_1c : wseg_ok RSEGS (0x10a000 : word) 8192%nat = true.
Proof. vm_compute. reflexivity. Qed.

Lemma store_ok_data : forall m (a : word) n,
  (0x10a000 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0x10c000)%Z ->
  store_ok RSEGS m a n = true.
Proof.
  intros m a n Hlo Hhi.
  eapply (store_ok_window RSEGS m (0x10a000 : word) a 8192%nat n 0x10a000 0x10c000);
    [reflexivity | reflexivity | lia | exact bo_wseg_1c | exact Hlo | exact Hhi].
Qed.
End FPGen0.

Ltac sok_data := store_ok_peel; apply store_ok_data; zsimp; lia.

(* [comment removed for export] *)
Ltac sok_frame SOK :=
  store_ok_peel;
  eapply (store_ok_sub _ _ _ _ 112%nat); [ | exact SOK | | ]; zsimp; lia.

Section FPGen1.
Context {fx : FPState}.

Record sw_file (mem : word -> option byte) (f : Z) (wb wp : Z) (fd : Z) (bufp bufsz : word) : Prop := {
  swf_wpos  : rdn RSEGS mem (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
  swf_wbase : rdn RSEGS mem (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
  swf_fd    : rdn RSEGS mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd));
  swf_buf   : rdn RSEGS mem (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
  swf_bsz   : rdn RSEGS mem (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz)
}.

(* [comment removed for export] *)
Definition ssp_cells (mem : word -> option byte) (can : word) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0x106c60) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6613c0))
  /\ rdn RSEGS mem (Z_to_bv 64 0x6613c0) 8%nat = Some (word_to_le_bytes 8 can).

Record sw_post (mem : word -> option byte) (su f : Z) (bufp bufsz : word)
       (mem' : word -> option byte) : Prop := {
  swp_agree : forall x : word,
      ~ (su - 112 <= bv_unsigned x < su)%Z ->
      ~ (f + 32 <= bv_unsigned x < f + 48)%Z ->
      ~ (f + 56 <= bv_unsigned x < f + 64)%Z ->
      mem' x = mem x;
  swp_grows : mem_grows mem mem';
  swp_wend  : rdn RSEGS mem' (Z_to_bv 64 (f + 32)) 8%nat = Some (word_to_le_bytes 8 (v_add bufp bufsz));
  swp_wpos  : rdn RSEGS mem' (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 bufp);
  swp_wbase : rdn RSEGS mem' (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 bufp)
}.


End FPGen1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPGenW.
Context {fx : FPState}.

Definition mclean (H : word -> bool) (m : word -> option byte) : Prop := forall a, H a = true -> m a = None.

Definition HYP_writev1_wall_stmt (R : shape_rel RSEGS) : Prop :=
  forall (H : word -> bool) (A : list (Z * Z)) (F : word -> option byte)
         regs (pc : word) (m : word -> option byte) model w (fd : Z) (iov b1 n1 : word) bs1 (K : TSet),
  H_off_segments RSEGS H -> wx_segs_nowrap RSEGS -> A_wf A -> MInv A model -> lazy_cover H (m_vm_lazy model) A ->
  mclean H m ->
  fetch_word RSEGS pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2 ^ 31)%Z ->
  getr regs 17 = Z_to_bv 64 66 -> getr regs 10 = Z_to_bv 64 fd -> getr regs 11 = iov -> getr regs 12 = Z_to_bv 64 1 ->
  rdn RSEGS m iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn RSEGS m (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn RSEGS m b1 (word_to_nat n1) = Some bs1 ->
  range_avoids H iov 16%nat -> range_avoids H b1 (word_to_nat n1) ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z -> (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1)%Z -> (bv_unsigned n1 <= 2 ^ 30)%Z ->
  K [] ->
  (forall k mdl', (1 <= k)%nat -> (k <= length bs1)%nat -> MInv A mdl' -> same_but_materialized model mdl' ->
     R (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) (munrestrict H F m) (seg_rom RSEGS)) mdl')
              (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)) ->
  R (mkCfg (mkst regs pc (munrestrict H F m) (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) bs1) K).

Definition HYP_writev2_wall_stmt (R : shape_rel RSEGS) : Prop :=
  forall (H : word -> bool) (A : list (Z * Z)) (F : word -> option byte)
         regs (pc : word) (m : word -> option byte) model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (K : TSet),
  H_off_segments RSEGS H -> wx_segs_nowrap RSEGS -> A_wf A -> MInv A model -> lazy_cover H (m_vm_lazy model) A ->
  mclean H m ->
  fetch_word RSEGS pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2 ^ 31)%Z ->
  getr regs 17 = Z_to_bv 64 66 -> getr regs 10 = Z_to_bv 64 fd -> getr regs 11 = iov -> getr regs 12 = Z_to_bv 64 2 ->
  rdn RSEGS m iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn RSEGS m (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn RSEGS m (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
  rdn RSEGS m (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
  rdn RSEGS m b1 (word_to_nat n1) = Some bs1 ->
  rdn RSEGS m b2 (word_to_nat n2) = Some bs2 ->
  range_avoids H iov 32%nat -> range_avoids H b1 (word_to_nat n1) -> range_avoids H b2 (word_to_nat n2) ->
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z -> (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  K [] ->
  (forall k mdl', (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat -> MInv A mdl' -> same_but_materialized model mdl' ->
     R (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) (munrestrict H F m) (seg_rom RSEGS)) mdl')
              (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)) ->
  R (mkCfg (mkst regs pc (munrestrict H F m) (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) (bs1 ++ bs2)) K).

Definition HYP_writev1_zero_stmt (R : shape_rel RSEGS) : Prop :=
  forall (H : word -> bool) (A : list (Z * Z)) (F : word -> option byte)
         regs (pc : word) (m : word -> option byte) model w (fd : Z) (iov b1 : word) (K : TSet),
  H_off_segments RSEGS H -> wx_segs_nowrap RSEGS -> A_wf A -> MInv A model -> lazy_cover H (m_vm_lazy model) A ->
  mclean H m ->
  fetch_word RSEGS pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2 ^ 31)%Z ->
  getr regs 17 = Z_to_bv 64 66 -> getr regs 10 = Z_to_bv 64 fd -> getr regs 11 = iov -> getr regs 12 = Z_to_bv 64 1 ->
  rdn RSEGS m iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn RSEGS m (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  range_avoids H iov 16%nat ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z -> (bv_unsigned b1 <= TASK_SIZE)%Z ->
  (forall mdl', MInv A mdl' -> same_but_materialized model mdl' ->
     R (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (munrestrict H F m) (seg_rom RSEGS)) mdl') K) ->
  R (mkCfg (mkst regs pc (munrestrict H F m) (seg_rom RSEGS)) model) K.
End FPGenW.
End BoStdioDefs.
Module BoStdioWrite_run1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.LibAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes BoStdioDefs Bo_code_f34c8_f34f8 Bo_code_f3610_f37a8 Bo_code_f3bf8_f3d9c Bo_code_f3fbc_f423c Bo_code_f43a4_f4964 Bo_code_edf44_ee420 Bo_code_ee7cc_ef130.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPGen1.
Context {fx : FPState}.


Lemma v_sub_Z : forall a b, (0 <= b <= a)%Z -> (a < 2^64)%Z ->
  v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof. intros a b H H2. unfold v_sub. u_norm. reflexivity. Qed.

Lemma v_add_Z : forall a (l : word), (0 <= a < 2^64)%Z ->
  v_add (Z_to_bv 64 a) l = Z_to_bv 64 (a + bv_unsigned l).
Proof. intros a l H. unfold v_add. u_norm. reflexivity. Qed.

Lemma v_add_wZ : forall (b : word) c, (0 <= c < 2^64)%Z ->
  v_add b (Z_to_bv 64 c) = Z_to_bv 64 (bv_unsigned b + c).
Proof. intros b c H. unfold v_add. u_norm. reflexivity. Qed.

Lemma v_add_ZZ' : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z ->
  v_add (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof. intros. unfold v_add. u_norm. reflexivity. Qed.

Lemma sltu0_xor_ne : forall a b, (0 <= a < 2^64)%Z -> (0 <= b < 2^64)%Z -> a <> b ->
  v_sltu (Z_to_bv 64 0) (v_xor (Z_to_bv 64 a) (Z_to_bv 64 b)) = Z_to_bv 64 1.
Proof.
  intros a b Ha Hb Hne. unfold v_sltu, c_ltu, bv_ltu, v_xor.
  rewrite (u_Z2bv a), (u_Z2bv b), (u_Z2bv 0) by lia.
  pose proof (Z_lxor_range a b Ha Hb) as Hr.
  rewrite u_Z2bv by lia.
  destruct (Z.ltb_spec 0 (Z.lxor a b)) as [Hlt|Hge]; [reflexivity|].
  exfalso. apply Hne. apply Z.lxor_eq. lia.
Qed.

Lemma sltu0_xor_eq : forall a : word, v_sltu (Z_to_bv 64 0) (v_xor a a) = Z_to_bv 64 0.
Proof.
  intros a. unfold v_sltu, c_ltu, bv_ltu, v_xor. rewrite Z.lxor_nilpotent.
  rewrite (u_Z2bv 0) by lia. reflexivity.
Qed.

Lemma sltu_ge : forall a b, (0 <= b <= a)%Z -> (a < 2^64)%Z ->
  v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 0.
Proof.
  intros a b H H2. unfold v_sltu, c_ltu, bv_ltu. u_norm.
  destruct (Z.ltb_spec a b); [lia|reflexivity].
Qed.

Lemma sltu_lt : forall a b, (0 <= a < b)%Z -> (b < 2^64)%Z ->
  v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 1.
Proof.
  intros a b H H2. unfold v_sltu, c_ltu, bv_ltu. u_norm.
  destruct (Z.ltb_spec a b); [reflexivity|lia].
Qed.

Lemma c_lts_pos_0 : forall a, (0 <= a < 2^63)%Z ->
  c_lts (Z_to_bv 64 a) (Z_to_bv 64 0) = false.
Proof.
  intros a H. unfold c_lts, bv_lts. rewrite !bv_signed_small by (u_norm; lia). u_norm.
  destruct (Z.ltb_spec a 0); [lia|reflexivity].
Qed.

Lemma v_and_0_l : forall (x : word), v_and (Z_to_bv 64 0) x = Z_to_bv 64 0.
Proof. intros x. unfold v_and. rewrite (u_Z2bv 0) by lia. rewrite Z.land_0_l. reflexivity. Qed.

Lemma v_and_m1_l : forall a, (0 <= a < 2^64)%Z ->
  v_and (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 a) = Z_to_bv 64 a.
Proof.
  intros a H. unfold v_and. u_norm.
  change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
  f_equal. apply Z.mod_small. lia.
Qed.

Lemma v_subw_small_lit : forall a b, (0 <= b <= a)%Z -> (a < 2^31)%Z ->
  v_subw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof.
  intros a b H H2. unfold v_subw. u_norm.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia).
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mem_sw1 (mem : word -> option byte) (su : Z) (ra s0 s1 s2 s3 s4 s5 s6 : word)
           (can : word) (wb n : Z) (s l : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (su - 8))  (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (su - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 (su - 24)) (word_to_le_bytes 8 s1))
    (Z_to_bv 64 (su - 32)) (word_to_le_bytes 8 s2))
    (Z_to_bv 64 (su - 40)) (word_to_le_bytes 8 s3))
    (Z_to_bv 64 (su - 48)) (word_to_le_bytes 8 s4))
    (Z_to_bv 64 (su - 56)) (word_to_le_bytes 8 s5))
    (Z_to_bv 64 (su - 64)) (word_to_le_bytes 8 s6))
    (Z_to_bv 64 (su - 72)) (word_to_le_bytes 8 can))
    (Z_to_bv 64 (su - 104)) (word_to_le_bytes 8 (Z_to_bv 64 wb)))
    (Z_to_bv 64 (su - 96)) (word_to_le_bytes 8 (Z_to_bv 64 n)))
    (Z_to_bv 64 (su - 88)) (word_to_le_bytes 8 s))
    (Z_to_bv 64 (su - 80)) (word_to_le_bytes 8 l).

Lemma sw_enter : forall regs mem rom (su f wb wp fd : Z) (s l bufp bufsz can ret : word),
  getr regs 2 = Z_to_bv 64 su -> getr regs 10 = Z_to_bv 64 f ->
  getr regs 11 = s -> getr regs 12 = l -> getr regs 1 = ret ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
  (0x10a5c8 <= f)%Z -> (f + 232 <= 0x10a7a0)%Z ->
  sw_file mem f wb wp fd bufp bufsz ->
  ssp_cells mem can ->
  (0 < fd < 2147483648)%Z ->
  (0 <= wb < wp)%Z -> (wp < 2^64)%Z -> (wp - wb + bv_unsigned l < 2147483648)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0xf360c : word) mem rom)
      (mkst regs' (0xf3694 : word)
         (mem_sw1 mem su ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                  (getr regs 20) (getr regs 21) (getr regs 22) can wb (wp - wb) s l) rom)
    /\ getr regs' 17 = Z_to_bv 64 66
    /\ getr regs' 10 = Z_to_bv 64 fd
    /\ getr regs' 11 = Z_to_bv 64 (su - 104)
    /\ getr regs' 12 = Z_to_bv 64 2
    /\ getr regs' 2 = Z_to_bv 64 (su - 112)
    /\ getr regs' 8 = l /\ getr regs' 9 = Z_to_bv 64 f
    /\ getr regs' 18 = Z_to_bv 64 2 /\ getr regs' 19 = Z_to_bv 64 (su - 104)
    /\ getr regs' 21 = Z_to_bv 64 0x6613c0
    /\ getr regs' 22 = Z_to_bv 64 (wp - wb + bv_unsigned l)
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
    /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
    /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.
Proof.
  intros regs mem rom su f wb wp fd s l bufp bufsz can ret
         Hsp Ha0 Ha1 Ha2 Hra SUlo SUhi SOK Flo Fhi [Fwp Fwb Ffd Fbuf Fbsz] [Ggot Gcan]
         FD WBP WPhi SMALL.
  zaddr Fwp; zaddr Fwb; zaddr Ffd; zaddr Fbuf; zaddr Fbsz.
  unfold mem_sw1. eexists. split.
  - stepn F_f3618 D_f3618. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_f361c D_f361c (Z_to_bv 64 (su - 8)) ret ltac:(sok_frame SOK).
    stepST F_f3620 D_f3620 (Z_to_bv 64 (su - 16)) (getr regs 8) ltac:(sok_frame SOK).
    stepST F_f3624 D_f3624 (Z_to_bv 64 (su - 24)) (getr regs 9) ltac:(sok_frame SOK).
    stepST F_f3628 D_f3628 (Z_to_bv 64 (su - 32)) (getr regs 18) ltac:(sok_frame SOK).
    stepST F_f362c D_f362c (Z_to_bv 64 (su - 40)) (getr regs 19) ltac:(sok_frame SOK).
    stepST F_f3630 D_f3630 (Z_to_bv 64 (su - 48)) (getr regs 20) ltac:(sok_frame SOK).
    stepST F_f3634 D_f3634 (Z_to_bv 64 (su - 56)) (getr regs 21) ltac:(sok_frame SOK).
    stepST F_f3638 D_f3638 (Z_to_bv 64 (su - 64)) (getr regs 22) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepn F_f363c D_f363c. rewrite Ha2.
    stepn F_f3640 D_f3640. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_f3644 D_f3644.
    stepLD8 F_f3648 D_f3648 (Z_to_bv 64 0x6613c0).
    stepLD8 F_f364c D_f364c can.
    stepST F_f3650 D_f3650 (Z_to_bv 64 (su - 72)) can ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepLD8 F_f3654 D_f3654 (Z_to_bv 64 wp).
    stepLD8 F_f3658 D_f3658 (Z_to_bv 64 wb).
    (* [comment removed for export] *)
    stepn F_f365c D_f365c. rewrite (v_sub_Z wp wb) by lia.
    stepn F_f3660 D_f3660.
    (* [comment removed for export] *)
    stepST F_f3664 D_f3664 (Z_to_bv 64 (su - 104)) (Z_to_bv 64 wb) ltac:(sok_frame SOK).
    stepST F_f3668 D_f3668 (Z_to_bv 64 (su - 96)) (Z_to_bv 64 (wp - wb)) ltac:(sok_frame SOK).
    stepST F_f366c D_f366c (Z_to_bv 64 (su - 88)) s ltac:(sok_frame SOK).
    stepST F_f3670 D_f3670 (Z_to_bv 64 (su - 80)) l ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepn F_f3674 D_f3674. rewrite (v_add_Z (wp - wb) l) by lia.
    stepn F_f3678 D_f3678. rewrite (sltu0_xor_ne wp wb) by lia.
    (* [comment removed for export] *)
    stepb_ft F_f367c D_f367c ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    stepn F_f3680 D_f3680.
    replace (v_addi (Z_to_bv 64 (su - 112)) 8) with (Z_to_bv 64 (su - 104))
      by (unfold v_addi; u_norm; f_equal; lia).
    stepn F_f3684 D_f3684.
    (* [comment removed for export] *)
    stepLD F_f368c D_f368c (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small fd) by lia.
    stepn F_f3690 D_f3690.
    stepn F_f3694 D_f3694.
    stepn F_f3698 D_f3698.
    stepn F_f369c D_f369c.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sw_enter_eq : forall regs mem rom (su f wp fd : Z) (s l bufp bufsz can ret : word),
  getr regs 2 = Z_to_bv 64 su -> getr regs 10 = Z_to_bv 64 f ->
  getr regs 11 = s -> getr regs 12 = l -> getr regs 1 = ret ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
  (0x10a5c8 <= f)%Z -> (f + 232 <= 0x10a7a0)%Z ->
  sw_file mem f wp wp fd bufp bufsz ->
  ssp_cells mem can ->
  (0 < fd < 2147483648)%Z ->
  (0 <= wp < 2^64)%Z -> (bv_unsigned l < 2147483648)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0xf360c : word) mem rom)
      (mkst regs' (0xf3694 : word)
         (mem_sw1 mem su ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                  (getr regs 20) (getr regs 21) (getr regs 22) can wp 0 s l) rom)
    /\ getr regs' 17 = Z_to_bv 64 66
    /\ getr regs' 10 = Z_to_bv 64 fd
    /\ getr regs' 11 = Z_to_bv 64 (su - 88)
    /\ getr regs' 12 = Z_to_bv 64 1
    /\ getr regs' 2 = Z_to_bv 64 (su - 112)
    /\ getr regs' 8 = l /\ getr regs' 9 = Z_to_bv 64 f
    /\ getr regs' 18 = Z_to_bv 64 1 /\ getr regs' 19 = Z_to_bv 64 (su - 88)
    /\ getr regs' 21 = Z_to_bv 64 0x6613c0
    /\ getr regs' 22 = l
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
    /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
    /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.
Proof.
  intros regs mem rom su f wp fd s l bufp bufsz can ret
         Hsp Ha0 Ha1 Ha2 Hra SUlo SUhi SOK Flo Fhi [Fwp Fwb Ffd Fbuf Fbsz] [Ggot Gcan]
         FD WPhi SMALL.
  pose proof (u64_range l) as Hl.
  zaddr Fwp; zaddr Fwb; zaddr Ffd; zaddr Fbuf; zaddr Fbsz.
  unfold mem_sw1. eexists. split.
  - stepn F_f3618 D_f3618. rewrite Hsp. sp_renorm.
    stepST F_f361c D_f361c (Z_to_bv 64 (su - 8)) ret ltac:(sok_frame SOK).
    stepST F_f3620 D_f3620 (Z_to_bv 64 (su - 16)) (getr regs 8) ltac:(sok_frame SOK).
    stepST F_f3624 D_f3624 (Z_to_bv 64 (su - 24)) (getr regs 9) ltac:(sok_frame SOK).
    stepST F_f3628 D_f3628 (Z_to_bv 64 (su - 32)) (getr regs 18) ltac:(sok_frame SOK).
    stepST F_f362c D_f362c (Z_to_bv 64 (su - 40)) (getr regs 19) ltac:(sok_frame SOK).
    stepST F_f3630 D_f3630 (Z_to_bv 64 (su - 48)) (getr regs 20) ltac:(sok_frame SOK).
    stepST F_f3634 D_f3634 (Z_to_bv 64 (su - 56)) (getr regs 21) ltac:(sok_frame SOK).
    stepST F_f3638 D_f3638 (Z_to_bv 64 (su - 64)) (getr regs 22) ltac:(sok_frame SOK).
    stepn F_f363c D_f363c. rewrite Ha2.
    stepn F_f3640 D_f3640. rewrite Ha0.
    stepn F_f3644 D_f3644.
    stepLD8 F_f3648 D_f3648 (Z_to_bv 64 0x6613c0).
    stepLD8 F_f364c D_f364c can.
    stepST F_f3650 D_f3650 (Z_to_bv 64 (su - 72)) can ltac:(sok_frame SOK).
    stepLD8 F_f3654 D_f3654 (Z_to_bv 64 wp).
    stepLD8 F_f3658 D_f3658 (Z_to_bv 64 wp).
    stepn F_f365c D_f365c. rewrite (v_sub_Z wp wp) by lia. rewrite Z.sub_diag.
    stepn F_f3660 D_f3660.
    stepST F_f3664 D_f3664 (Z_to_bv 64 (su - 104)) (Z_to_bv 64 wp) ltac:(sok_frame SOK).
    stepST F_f3668 D_f3668 (Z_to_bv 64 (su - 96)) (Z_to_bv 64 0) ltac:(sok_frame SOK).
    stepST F_f366c D_f366c (Z_to_bv 64 (su - 88)) s ltac:(sok_frame SOK).
    stepST F_f3670 D_f3670 (Z_to_bv 64 (su - 80)) l ltac:(sok_frame SOK).
    stepn F_f3674 D_f3674.
    stepn F_f3678 D_f3678. rewrite sltu0_xor_eq.
    (* [comment removed for export] *)
    stepb_tk F_f367c D_f367c ltac:(apply c_eq_refl).
    stepn F_f3688 D_f3688.
    replace (v_addi (Z_to_bv 64 (su - 112)) 24) with (Z_to_bv 64 (su - 88))
      by (unfold v_addi; u_norm; f_equal; lia).
    stepLD F_f368c D_f368c (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small fd) by lia.
    stepn F_f3690 D_f3690.
    stepn F_f3694 D_f3694.
    stepn F_f3698 D_f3698.
    stepn F_f369c D_f369c.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
End FPGen1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End BoStdioWrite_run1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.LibAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes BoStdioDefs BoStdioWrite_run1 Bo_code_f34c8_f34f8 Bo_code_f3610_f37a8 Bo_code_f3bf8_f3d9c Bo_code_f3fbc_f423c Bo_code_f43a4_f4964 Bo_code_edf44_ee420 Bo_code_ee7cc_ef130.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPGen1.
Context {fx : FPState}.

Definition sw_regs_but (regs regs' : bvmap 5 word) : Prop :=
  getr regs' 2 = getr regs 2 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
  /\ getr regs' 21 = getr regs 21
  /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
  /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
  /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.

Lemma sw_c1_eq : forall regs mem rom (k : Z),
  getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 k ->
  (0 <= k < 2147483648)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0xf3698 : word) mem rom) (mkst regs' (0xf36a0 : word) mem rom)
    /\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
    /\ sw_regs_but regs regs'.
Proof.
  intros regs mem rom k Ha0 Hs6 K.
  eexists. split.
  - stepn F_f36a4 D_f36a4.
    stepn F_ee028 D_ee028.
    stepn F_ee02c D_ee02c.
    stepb_tk F_ee030 D_ee030 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_ee05c D_ee05c (0xf369c : word) ltac:(bveq).
    stepb_ft F_f36a8 D_f36a8 ltac:(rewrite Ha0, Hs6; apply c_eq_refl).
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

Lemma sw_c1_ne : forall regs mem rom (k rem : Z),
  getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 rem ->
  (0 <= k < 2147483648)%Z -> (0 <= rem < 2^64)%Z -> k <> rem ->
  exists regs',
    msteps RSEGS (mkst regs (0xf3698 : word) mem rom) (mkst regs' (0xf372c : word) mem rom)
    /\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
    /\ sw_regs_but regs regs'.
Proof.
  intros regs mem rom k rem Ha0 Hs6 K REM NE.
  eexists. split.
  - stepn F_f36a4 D_f36a4.
    stepn F_ee028 D_ee028.
    stepn F_ee02c D_ee02c.
    stepb_tk F_ee030 D_ee030 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_ee05c D_ee05c (0xf369c : word) ltac:(bveq).
    stepb_tk F_f36a8 D_f36a8 ltac:(rewrite Ha0, Hs6, c_eq_Z by lia; apply Z.eqb_neq; lia).
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

Lemma sw_c2_eq : forall regs mem rom (k : Z),
  getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 k ->
  (0 <= k < 2147483648)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0xf3720 : word) mem rom) (mkst regs' (0xf36a0 : word) mem rom)
    /\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 20 /\ getr regs' 20 = getr regs 20
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
    /\ sw_regs_but regs regs'.
Proof.
  intros regs mem rom k Ha0 Hs6 K.
  eexists. split.
  - stepn F_f372c D_f372c.
    stepn F_ee028 D_ee028.
    stepn F_ee02c D_ee02c.
    stepb_tk F_ee030 D_ee030 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_ee05c D_ee05c (0xf3724 : word) ltac:(bveq).
    stepn F_f3730 D_f3730.
    stepb_tk F_f3734 D_f3734 ltac:(rewrite Ha0, Hs6; apply c_eq_refl).
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

Lemma sw_c2_ne : forall regs mem rom (k rem : Z),
  getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 rem ->
  (0 <= k < 2147483648)%Z -> (0 <= rem < 2^64)%Z -> k <> rem ->
  exists regs',
    msteps RSEGS (mkst regs (0xf3720 : word) mem rom) (mkst regs' (0xf372c : word) mem rom)
    /\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 20 /\ getr regs' 20 = getr regs 20
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
    /\ sw_regs_but regs regs'.
Proof.
  intros regs mem rom k rem Ha0 Hs6 K REM NE.
  eexists. split.
  - stepn F_f372c D_f372c.
    stepn F_ee028 D_ee028.
    stepn F_ee02c D_ee02c.
    stepb_tk F_ee030 D_ee030 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_ee05c D_ee05c (0xf3724 : word) ltac:(bveq).
    stepn F_f3730 D_f3730.
    stepb_ft F_f3734 D_f3734 ltac:(rewrite Ha0, Hs6, c_eq_Z by lia; apply Z.eqb_neq; lia).
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sw_retry_a : forall regs mem rom (su f fd io ic cnt n0 rem : Z) (b0 : word),
  getr regs 10 = Z_to_bv 64 cnt -> getr regs 19 = Z_to_bv 64 io -> getr regs 18 = Z_to_bv 64 ic ->
  getr regs 22 = Z_to_bv 64 rem -> getr regs 9 = Z_to_bv 64 f -> getr regs 2 = Z_to_bv 64 (su - 112) ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  (0x10a5c8 <= f)%Z -> (f + 232 <= 0x10a7a0)%Z ->
  (su - 104 <= io)%Z -> (io + 16 <= su - 72)%Z ->
  (1 <= ic <= 2)%Z ->
  (1 <= cnt <= n0)%Z -> (n0 < 2^62)%Z -> (cnt <= rem)%Z -> (rem < 2^62)%Z ->
  (bv_unsigned b0 + n0 <= 2^64)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 io) 8%nat = Some (word_to_le_bytes 8 b0) ->
  rdn RSEGS mem (Z_to_bv 64 (io + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 n0)) ->
  rdn RSEGS mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
  (0 < fd < 2147483648)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0xf372c : word) mem rom)
      (mkst regs' (0xf371c : word)
        (wbytes (wbytes mem (Z_to_bv 64 io) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned b0 + cnt))))
                (Z_to_bv 64 (io + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (n0 - cnt)))) rom)
    /\ getr regs' 17 = Z_to_bv 64 66 /\ getr regs' 10 = Z_to_bv 64 fd
    /\ getr regs' 11 = Z_to_bv 64 io /\ getr regs' 12 = Z_to_bv 64 ic
    /\ getr regs' 18 = Z_to_bv 64 ic /\ getr regs' 19 = Z_to_bv 64 io /\ getr regs' 20 = Z_to_bv 64 io
    /\ getr regs' 22 = Z_to_bv 64 (rem - cnt)
    /\ sw_regs_but regs regs'.
Proof.
  intros regs mem rom su f fd io ic cnt n0 rem b0
         Ha0 Hs3 Hs2 Hs6 Hs1 Hsp SUlo SUhi Flo Fhi IOlo IOhi IC CNT N0 CR REM B0 SOK Mb0 Mn0 Mfd FD.
  pose proof (u64_range b0) as Hb0.
  eexists. split.
  - (* [comment removed for export] *)
    stepb_ft F_f3738 D_f3738 ltac:(rewrite Ha0; apply c_lts_pos_0; lia).
    (* [comment removed for export] *)
    stepLD8 F_f373c D_f373c (Z_to_bv 64 n0).
    (* [comment removed for export] *)
    stepn F_f3740 D_f3740. rewrite Ha0, (sltu_ge n0 cnt) by lia.
    (* [comment removed for export] *)
    stepn F_f3744 D_f3744.
    stepn F_f3748 D_f3748. rewrite Hs3.
    (* [comment removed for export] *)
    stepLD8 F_f374c D_f374c b0.
    (* [comment removed for export] *)
    stepn F_f3750 D_f3750.
    stepn F_f3754 D_f3754. rewrite v_and_0_l.
    stepn F_f3758 D_f3758. rewrite Ha0, (v_sub_Z cnt 0) by lia. rewrite Z.sub_0_r.
    (* [comment removed for export] *)
    stepn F_f375c D_f375c. rewrite (v_add_wZ b0 cnt) by lia.
    (* [comment removed for export] *)
    stepST F_f3760 D_f3760 (Z_to_bv 64 io) (Z_to_bv 64 (bv_unsigned b0 + cnt)) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepb_tk F_f3764 D_f3764 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_ge; lia).
    (* [comment removed for export] *)
    stepn F_f36fc D_f36fc.
    stepn F_f3700 D_f3700.
    stepn F_f3704 D_f3704. rewrite Hs3, (v_add_ZZ' io 8) by lia.
    (* [comment removed for export] *)
    stepLD8 F_f3708 D_f3708 (Z_to_bv 64 n0).
    (* [comment removed for export] *)
    stepn F_f370c D_f370c. rewrite Hs6, Ha0, (v_sub_Z rem cnt) by lia.
    (* [comment removed for export] *)
    stepLD F_f3710 D_f3710 (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small fd) by lia.
    (* [comment removed for export] *)
    stepn F_f3714 D_f3714. rewrite Hs2, (v_subw_small_lit ic 0) by lia. rewrite Z.sub_0_r.
    (* [comment removed for export] *)
    stepn F_f3718 D_f3718. rewrite (v_sub_Z n0 cnt) by lia.
    stepST F_f371c D_f371c (Z_to_bv 64 (io + 8)) (Z_to_bv 64 (n0 - cnt)) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepn F_f3720 D_f3720.
    stepn F_f3724 D_f3724.
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity; try assumption.
Qed.


(* [comment removed for export] *)
Lemma sw_retry_b : forall regs mem rom (su f fd io cnt n0 n1 rem : Z) (b1 : word),
  getr regs 10 = Z_to_bv 64 cnt -> getr regs 19 = Z_to_bv 64 io -> getr regs 18 = Z_to_bv 64 2 ->
  getr regs 22 = Z_to_bv 64 rem -> getr regs 9 = Z_to_bv 64 f -> getr regs 2 = Z_to_bv 64 (su - 112) ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  (0x10a5c8 <= f)%Z -> (f + 232 <= 0x10a7a0)%Z ->
  (su - 104 <= io)%Z -> (io + 32 <= su - 72)%Z ->
  (0 <= n0 < cnt)%Z -> (cnt <= rem)%Z -> (rem < 2^62)%Z -> (cnt - n0 <= n1)%Z -> (n1 < 2^62)%Z ->
  (bv_unsigned b1 + n1 <= 2^64)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 (io + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 n0)) ->
  rdn RSEGS mem (Z_to_bv 64 (io + 16)) 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn RSEGS mem (Z_to_bv 64 (io + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 n1)) ->
  rdn RSEGS mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
  (0 < fd < 2147483648)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0xf372c : word) mem rom)
      (mkst regs' (0xf371c : word)
        (wbytes (wbytes mem (Z_to_bv 64 (io + 16)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned b1 + (cnt - n0)))))
                (Z_to_bv 64 (io + 24)) (word_to_le_bytes 8 (Z_to_bv 64 (n1 - (cnt - n0))))) rom)
    /\ getr regs' 17 = Z_to_bv 64 66 /\ getr regs' 10 = Z_to_bv 64 fd
    /\ getr regs' 11 = Z_to_bv 64 (io + 16) /\ getr regs' 12 = Z_to_bv 64 1
    /\ getr regs' 18 = Z_to_bv 64 1 /\ getr regs' 19 = Z_to_bv 64 io /\ getr regs' 20 = Z_to_bv 64 (io + 16)
    /\ getr regs' 22 = Z_to_bv 64 (rem - cnt)
    /\ sw_regs_but regs regs'.
Proof.
  intros regs mem rom su f fd io cnt n0 n1 rem b1
         Ha0 Hs3 Hs2 Hs6 Hs1 Hsp SUlo SUhi Flo Fhi IOlo IOhi N0 CR REM N1 N1hi B1 SOK Mn0 Mb1 Mn1 Mfd FD.
  pose proof (u64_range b1) as Hb1.
  eexists. split.
  - (* [comment removed for export] *)
    stepb_ft F_f3738 D_f3738 ltac:(rewrite Ha0; apply c_lts_pos_0; lia).
    (* [comment removed for export] *)
    stepLD8 F_f373c D_f373c (Z_to_bv 64 n0).
    (* [comment removed for export] *)
    stepn F_f3740 D_f3740. rewrite Ha0, (sltu_lt n0 cnt) by lia.
    (* [comment removed for export] *)
    stepn F_f3744 D_f3744.
    stepn F_f3748 D_f3748. rewrite Hs3, (v_add_ZZ' io 16) by lia.
    (* [comment removed for export] *)
    stepLD8 F_f374c D_f374c b1.
    (* [comment removed for export] *)
    stepn F_f3750 D_f3750.
    stepn F_f3754 D_f3754. rewrite (v_and_m1_l n0) by lia.
    stepn F_f3758 D_f3758. rewrite Ha0, (v_sub_Z cnt n0) by lia.
    (* [comment removed for export] *)
    stepn F_f375c D_f375c. rewrite (v_add_wZ b1 (cnt - n0)) by lia.
    (* [comment removed for export] *)
    stepST F_f3760 D_f3760 (Z_to_bv 64 (io + 16)) (Z_to_bv 64 (bv_unsigned b1 + (cnt - n0))) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepb_ft F_f3764 D_f3764 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_lt; lia).
    (* [comment removed for export] *)
    stepn F_f3768 D_f3768.
    stepn F_f376c D_f376c.
    stepn F_f3700 D_f3700.
    stepn F_f3704 D_f3704. rewrite Hs3, (v_add_ZZ' io 24) by lia.
    (* [comment removed for export] *)
    stepLD8 F_f3708 D_f3708 (Z_to_bv 64 n1).
    (* [comment removed for export] *)
    stepn F_f370c D_f370c. rewrite Hs6, Ha0, (v_sub_Z rem cnt) by lia.
    (* [comment removed for export] *)
    stepLD F_f3710 D_f3710 (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small fd) by lia.
    (* [comment removed for export] *)
    stepn F_f3714 D_f3714. rewrite Hs2. vals_lit.
    (* [comment removed for export] *)
    stepn F_f3718 D_f3718. rewrite (v_sub_Z n1 (cnt - n0)) by lia.
    stepST F_f371c D_f371c (Z_to_bv 64 (io + 24)) (Z_to_bv 64 (n1 - (cnt - n0))) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepn F_f3720 D_f3720.
    stepn F_f3724 D_f3724.
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity; try assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mem_sw2 (mem1 : word -> option byte) (f : Z) (bufp bufsz : word) :=
  wbytes (wbytes (wbytes mem1
    (Z_to_bv 64 (f + 32)) (word_to_le_bytes 8 (v_add bufp bufsz)))
    (Z_to_bv 64 (f + 40)) (word_to_le_bytes 8 bufp))
    (Z_to_bv 64 (f + 56)) (word_to_le_bytes 8 bufp).

Lemma sw_done : forall regs mem rom (su f : Z) (l bufp bufsz can ret s0v s1v s2v s3v s4v s5v s6v : word),
  getr regs 2 = Z_to_bv 64 (su - 112) ->
  getr regs 8 = l -> getr regs 9 = Z_to_bv 64 f ->
  getr regs 21 = Z_to_bv 64 0x6613c0 ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  (0x10a5c8 <= f)%Z -> (f + 232 <= 0x10a7a0)%Z ->
  ret_ok ret ->
  rdn RSEGS mem (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 s0v) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 s1v) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 s2v) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 s3v) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 s4v) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 s5v) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 s6v) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can) ->
  rdn RSEGS mem (Z_to_bv 64 0x6613c0) 8%nat = Some (word_to_le_bytes 8 can) ->
  rdn RSEGS mem (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp) ->
  rdn RSEGS mem (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz) ->
  exists regs',
    msteps RSEGS (mkst regs (0xf36a0 : word) mem rom)
                 (mkst regs' ret (mem_sw2 mem f bufp bufsz) rom)
    /\ getr regs' 10 = l /\ getr regs' 2 = Z_to_bv 64 su /\ getr regs' 1 = ret
    /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
    /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
    /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
    /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.
Proof.
  intros regs mem rom su f l bufp bufsz can ret s0v s1v s2v s3v s4v s5v s6v
         Hsp Hs0 Hs1 Hs5 SUlo SUhi Flo Fhi Hret
         M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz.
  unfold mem_sw2. eexists. split.
  - (* [comment removed for export] *)
    stepLD F_f36ac D_f36ac (word_to_le_bytes 8 bufp) bufp ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_f36b0 D_f36b0 (word_to_le_bytes 8 bufsz) bufsz ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepn F_f36b4 D_f36b4.
    (* [comment removed for export] *)
    stepST F_f36b8 D_f36b8 (Z_to_bv 64 (f + 32)) (v_add bufp bufsz) ltac:(sok_data).
    stepST F_f36bc D_f36bc (Z_to_bv 64 (f + 40)) bufp ltac:(sok_data).
    stepST F_f36c0 D_f36c0 (Z_to_bv 64 (f + 56)) bufp ltac:(sok_data).
    (* [comment removed for export] *)
    stepn F_f36c4 D_f36c4. rewrite Hs0.
    stepLD F_f36c8 D_f36c8 (word_to_le_bytes 8 can) can ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_f36cc D_f36cc (word_to_le_bytes 8 can) can ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepb_ft F_f36d0 D_f36d0 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD F_f36d4 D_f36d4 (word_to_le_bytes 8 ret) ret ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_f36d8 D_f36d8 (word_to_le_bytes 8 s0v) s0v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_f36dc D_f36dc (word_to_le_bytes 8 s1v) s1v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_f36e0 D_f36e0 (word_to_le_bytes 8 s2v) s2v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_f36e4 D_f36e4 (word_to_le_bytes 8 s3v) s3v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_f36e8 D_f36e8 (word_to_le_bytes 8 s4v) s4v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_f36ec D_f36ec (word_to_le_bytes 8 s5v) s5v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_f36f0 D_f36f0 (word_to_le_bytes 8 s6v) s6v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepn F_f36f4 D_f36f4. rewrite Hsp. sp_renorm.
    replace (su - 0)%Z with su by lia.
    stepret F_f36f8 D_f36f8 ret ltac:(reflexivity).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
End FPGen1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
