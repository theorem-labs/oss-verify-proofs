(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.InstrEnc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Bo_code_7005c_70b0c.
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
Definition W_7006c : bv 32 := @BV 32 0x0009e517%Z I.
Lemma F_7006c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7006c%Z I : word) = Some W_7006c.
Proof. vm_refl. Qed.
Lemma D_7006c : decode_any W_7006c = Some (Auipc (@BV 5 10%Z I) (@BV 20 158%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70070 : bv 32 := @BV 32 0x9b050503%Z I.
Lemma F_70070 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x70070%Z I : word) = Some W_70070.
Proof. vm_refl. Qed.
Lemma D_70070 : decode_any W_70070 = Some (Load SZ1 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 2480%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70074 : bv 32 := @BV 32 0x0230000f%Z I.

Lemma D_70074 : decode_any W_70074 = Some (Fence (@BV 4 0%Z I) (@BV 4 2%Z I) (@BV 4 3%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70078 : bv 32 := @BV 32 0x00a03533%Z I.

Lemma D_70078 : decode_any W_70078 = Some (Op ALU_SLTU (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7007c : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_7007c : decode_any W_7007c = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.











































































































































































































































































































































































































































































































































































































































































































































































End Bo_code_7005c_70b0c.
Module Bo_code_7d08c_7db0c.
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
Definition W_7d08c : bv 32 := @BV 32 0x00089597%Z I.
Lemma F_7d08c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d08c%Z I : word) = Some W_7d08c.
Proof. vm_refl. Qed.
Lemma D_7d08c : decode_any W_7d08c = Some (Auipc (@BV 5 11%Z I) (@BV 20 137%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d090 : bv 32 := @BV 32 0xe7c5b583%Z I.
Lemma F_7d090 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d090%Z I : word) = Some W_7d090.
Proof. vm_refl. Qed.
Lemma D_7d090 : decode_any W_7d090 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 3708%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d094 : bv 32 := @BV 32 0x0905b583%Z I.
Lemma F_7d094 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d094%Z I : word) = Some W_7d094.
Proof. vm_refl. Qed.
Lemma D_7d094 : decode_any W_7d094 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 144%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d098 : bv 32 := @BV 32 0x00058e63%Z I.
Lemma F_7d098 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d098%Z I : word) = Some W_7d098.
Proof. vm_refl. Qed.
Lemma D_7d098 : decode_any W_7d098 = Some (Branch BC_EQ (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 28%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d0b4 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_7d0b4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d0b4%Z I : word) = Some W_7d0b4.
Proof. vm_refl. Qed.
Lemma D_7d0b4 : decode_any W_7d0b4 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d0d0 : bv 32 := @BV 32 0x00089597%Z I.
Lemma F_7d0d0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d0d0%Z I : word) = Some W_7d0d0.
Proof. vm_refl. Qed.
Lemma D_7d0d0 : decode_any W_7d0d0 = Some (Auipc (@BV 5 11%Z I) (@BV 20 137%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d0d4 : bv 32 := @BV 32 0xe385b583%Z I.
Lemma F_7d0d4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d0d4%Z I : word) = Some W_7d0d4.
Proof. vm_refl. Qed.
Lemma D_7d0d4 : decode_any W_7d0d4 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 3640%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d0d8 : bv 32 := @BV 32 0x0905b583%Z I.
Lemma F_7d0d8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d0d8%Z I : word) = Some W_7d0d8.
Proof. vm_refl. Qed.
Lemma D_7d0d8 : decode_any W_7d0d8 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 144%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d0dc : bv 32 := @BV 32 0x00058a63%Z I.
Lemma F_7d0dc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d0dc%Z I : word) = Some W_7d0dc.
Proof. vm_refl. Qed.
Lemma D_7d0dc : decode_any W_7d0dc = Some (Branch BC_EQ (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d0f0 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_7d0f0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d0f0%Z I : word) = Some W_7d0f0.
Proof. vm_refl. Qed.
Lemma D_7d0f0 : decode_any W_7d0f0 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d600 : bv 32 := @BV 32 0xfe010113%Z I.

Lemma D_7d600 : decode_any W_7d600 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4064%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d604 : bv 32 := @BV 32 0x00113c23%Z I.

Lemma D_7d604 : decode_any W_7d604 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d608 : bv 32 := @BV 32 0x00813823%Z I.

Lemma D_7d608 : decode_any W_7d608 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d60c : bv 32 := @BV 32 0x00913423%Z I.

Lemma D_7d60c : decode_any W_7d60c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d610 : bv 32 := @BV 32 0x01213023%Z I.

Lemma D_7d610 : decode_any W_7d610 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d614 : bv 32 := @BV 32 0x00058413%Z I.

Lemma D_7d614 : decode_any W_7d614 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d618 : bv 32 := @BV 32 0x00050493%Z I.

Lemma D_7d618 : decode_any W_7d618 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d61c : bv 32 := @BV 32 0x09c000ef%Z I.

Lemma D_7d61c : decode_any W_7d61c = Some (Jal (@BV 5 1%Z I) (@BV 21 156%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d620 : bv 32 := @BV 32 0x00122517%Z I.
Lemma F_7d620 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d620%Z I : word) = Some W_7d620.
Proof. vm_refl. Qed.
Lemma D_7d620 : decode_any W_7d620 = Some (Auipc (@BV 5 10%Z I) (@BV 20 290%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d624 : bv 32 := @BV 32 0x66050913%Z I.
Lemma F_7d624 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d624%Z I : word) = Some W_7d624.
Proof. vm_refl. Qed.
Lemma D_7d624 : decode_any W_7d624 = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 10%Z I) (@BV 12 1632%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d628 : bv 32 := @BV 32 0x00093603%Z I.

Lemma D_7d628 : decode_any W_7d628 = Some (Load SZ8 true (@BV 5 12%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d62c : bv 32 := @BV 32 0x06060a63%Z I.

Lemma D_7d62c : decode_any W_7d62c = Some (Branch BC_EQ (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 13 116%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d630 : bv 32 := @BV 32 0x00048513%Z I.



(* [comment removed for export] *)
Definition W_7d634 : bv 32 := @BV 32 0x00040593%Z I.



(* [comment removed for export] *)
Definition W_7d638 : bv 32 := @BV 32 0x000600e7%Z I.



(* [comment removed for export] *)
Definition W_7d63c : bv 32 := @BV 32 0x01093603%Z I.



(* [comment removed for export] *)
Definition W_7d640 : bv 32 := @BV 32 0x06060063%Z I.



(* [comment removed for export] *)
Definition W_7d644 : bv 32 := @BV 32 0x00048513%Z I.



(* [comment removed for export] *)
Definition W_7d648 : bv 32 := @BV 32 0x00040593%Z I.



(* [comment removed for export] *)
Definition W_7d64c : bv 32 := @BV 32 0x000600e7%Z I.



(* [comment removed for export] *)
Definition W_7d650 : bv 32 := @BV 32 0x02093603%Z I.



(* [comment removed for export] *)
Definition W_7d654 : bv 32 := @BV 32 0x04060663%Z I.



(* [comment removed for export] *)
Definition W_7d658 : bv 32 := @BV 32 0x00048513%Z I.



(* [comment removed for export] *)
Definition W_7d65c : bv 32 := @BV 32 0x00040593%Z I.



(* [comment removed for export] *)
Definition W_7d660 : bv 32 := @BV 32 0x000600e7%Z I.



(* [comment removed for export] *)
Definition W_7d664 : bv 32 := @BV 32 0x03093603%Z I.



(* [comment removed for export] *)
Definition W_7d668 : bv 32 := @BV 32 0x02060c63%Z I.



(* [comment removed for export] *)
Definition W_7d66c : bv 32 := @BV 32 0x00048513%Z I.



(* [comment removed for export] *)
Definition W_7d670 : bv 32 := @BV 32 0x00040593%Z I.



(* [comment removed for export] *)
Definition W_7d674 : bv 32 := @BV 32 0x000600e7%Z I.



(* [comment removed for export] *)
Definition W_7d678 : bv 32 := @BV 32 0x04093303%Z I.



(* [comment removed for export] *)
Definition W_7d67c : bv 32 := @BV 32 0x02030263%Z I.



(* [comment removed for export] *)
Definition W_7d680 : bv 32 := @BV 32 0x00048513%Z I.



(* [comment removed for export] *)
Definition W_7d684 : bv 32 := @BV 32 0x00040593%Z I.



(* [comment removed for export] *)
Definition W_7d688 : bv 32 := @BV 32 0x01813083%Z I.



(* [comment removed for export] *)
Definition W_7d68c : bv 32 := @BV 32 0x01013403%Z I.



(* [comment removed for export] *)
Definition W_7d690 : bv 32 := @BV 32 0x00813483%Z I.



(* [comment removed for export] *)
Definition W_7d694 : bv 32 := @BV 32 0x00013903%Z I.



(* [comment removed for export] *)
Definition W_7d698 : bv 32 := @BV 32 0x02010113%Z I.



(* [comment removed for export] *)
Definition W_7d69c : bv 32 := @BV 32 0x00030067%Z I.



(* [comment removed for export] *)
Definition W_7d6a0 : bv 32 := @BV 32 0x01813083%Z I.

Lemma D_7d6a0 : decode_any W_7d6a0 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d6a4 : bv 32 := @BV 32 0x01013403%Z I.

Lemma D_7d6a4 : decode_any W_7d6a4 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d6a8 : bv 32 := @BV 32 0x00813483%Z I.

Lemma D_7d6a8 : decode_any W_7d6a8 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d6ac : bv 32 := @BV 32 0x00013903%Z I.

Lemma D_7d6ac : decode_any W_7d6ac = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d6b0 : bv 32 := @BV 32 0x02010113%Z I.

Lemma D_7d6b0 : decode_any W_7d6b0 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d6b4 : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_7d6b4 : decode_any W_7d6b4 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d6b8 : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_7d6b8 : decode_any W_7d6b8 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d6bc : bv 32 := @BV 32 0xfe010113%Z I.
Lemma F_7d6bc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d6bc%Z I : word) = Some W_7d6bc.
Proof. vm_refl. Qed.
Lemma D_7d6bc : decode_any W_7d6bc = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4064%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d6c0 : bv 32 := @BV 32 0x00113c23%Z I.
Lemma F_7d6c0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d6c0%Z I : word) = Some W_7d6c0.
Proof. vm_refl. Qed.
Lemma D_7d6c0 : decode_any W_7d6c0 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d6c4 : bv 32 := @BV 32 0x00813823%Z I.
Lemma F_7d6c4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d6c4%Z I : word) = Some W_7d6c4.
Proof. vm_refl. Qed.
Lemma D_7d6c4 : decode_any W_7d6c4 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d6c8 : bv 32 := @BV 32 0x00913423%Z I.
Lemma F_7d6c8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d6c8%Z I : word) = Some W_7d6c8.
Proof. vm_refl. Qed.
Lemma D_7d6c8 : decode_any W_7d6c8 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d6cc : bv 32 := @BV 32 0x00050413%Z I.
Lemma F_7d6cc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d6cc%Z I : word) = Some W_7d6cc.
Proof. vm_refl. Qed.
Lemma D_7d6cc : decode_any W_7d6cc = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d6d0 : bv 32 := @BV 32 0x098000ef%Z I.
Lemma F_7d6d0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d6d0%Z I : word) = Some W_7d6d0.
Proof. vm_refl. Qed.
Lemma D_7d6d0 : decode_any W_7d6d0 = Some (Jal (@BV 5 1%Z I) (@BV 21 152%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d6d4 : bv 32 := @BV 32 0x00050e63%Z I.
Lemma F_7d6d4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d6d4%Z I : word) = Some W_7d6d4.
Proof. vm_refl. Qed.
Lemma D_7d6d4 : decode_any W_7d6d4 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 28%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d6f0 : bv 32 := @BV 32 0x00040513%Z I.
Lemma F_7d6f0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d6f0%Z I : word) = Some W_7d6f0.
Proof. vm_refl. Qed.
Lemma D_7d6f0 : decode_any W_7d6f0 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d6f4 : bv 32 := @BV 32 0x07c000ef%Z I.
Lemma F_7d6f4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d6f4%Z I : word) = Some W_7d6f4.
Proof. vm_refl. Qed.
Lemma D_7d6f4 : decode_any W_7d6f4 = Some (Jal (@BV 5 1%Z I) (@BV 21 124%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d6f8 : bv 32 := @BV 32 0x00122517%Z I.
Lemma F_7d6f8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d6f8%Z I : word) = Some W_7d6f8.
Proof. vm_refl. Qed.
Lemma D_7d6f8 : decode_any W_7d6f8 = Some (Auipc (@BV 5 10%Z I) (@BV 20 290%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d6fc : bv 32 := @BV 32 0x58850493%Z I.
Lemma F_7d6fc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d6fc%Z I : word) = Some W_7d6fc.
Proof. vm_refl. Qed.
Lemma D_7d6fc : decode_any W_7d6fc = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 12 1416%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d700 : bv 32 := @BV 32 0x0084b583%Z I.
Lemma F_7d700 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d700%Z I : word) = Some W_7d700.
Proof. vm_refl. Qed.
Lemma D_7d700 : decode_any W_7d700 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d704 : bv 32 := @BV 32 0x04058663%Z I.
Lemma F_7d704 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d704%Z I : word) = Some W_7d704.
Proof. vm_refl. Qed.
Lemma D_7d704 : decode_any W_7d704 = Some (Branch BC_EQ (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 76%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d750 : bv 32 := @BV 32 0x00000513%Z I.
Lemma F_7d750 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d750%Z I : word) = Some W_7d750.
Proof. vm_refl. Qed.
Lemma D_7d750 : decode_any W_7d750 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d754 : bv 32 := @BV 32 0x01813083%Z I.
Lemma F_7d754 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d754%Z I : word) = Some W_7d754.
Proof. vm_refl. Qed.
Lemma D_7d754 : decode_any W_7d754 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d758 : bv 32 := @BV 32 0x01013403%Z I.
Lemma F_7d758 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d758%Z I : word) = Some W_7d758.
Proof. vm_refl. Qed.
Lemma D_7d758 : decode_any W_7d758 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d75c : bv 32 := @BV 32 0x00813483%Z I.
Lemma F_7d75c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d75c%Z I : word) = Some W_7d75c.
Proof. vm_refl. Qed.
Lemma D_7d75c : decode_any W_7d75c = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d760 : bv 32 := @BV 32 0x02010113%Z I.
Lemma F_7d760 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d760%Z I : word) = Some W_7d760.
Proof. vm_refl. Qed.
Lemma D_7d760 : decode_any W_7d760 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d764 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_7d764 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d764%Z I : word) = Some W_7d764.
Proof. vm_refl. Qed.
Lemma D_7d764 : decode_any W_7d764 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d768 : bv 32 := @BV 32 0x00000513%Z I.
Lemma F_7d768 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d768%Z I : word) = Some W_7d768.
Proof. vm_refl. Qed.
Lemma D_7d768 : decode_any W_7d768 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d76c : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_7d76c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d76c%Z I : word) = Some W_7d76c.
Proof. vm_refl. Qed.
Lemma D_7d76c : decode_any W_7d76c = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d770 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_7d770 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7d770%Z I : word) = Some W_7d770.
Proof. vm_refl. Qed.
Lemma D_7d770 : decode_any W_7d770 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_7d08c_7db0c.
Module Bo_code_9c9f0_9ca08.
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
Definition W_9c9f0 : bv 32 := @BV 32 0x0006a517%Z I.
Lemma F_9c9f0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x9c9f0%Z I : word) = Some W_9c9f0.
Proof. vm_refl. Qed.
Lemma D_9c9f0 : decode_any W_9c9f0 = Some (Auipc (@BV 5 10%Z I) (@BV 20 106%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c9f4 : bv 32 := @BV 32 0x18053503%Z I.
Lemma F_9c9f4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x9c9f4%Z I : word) = Some W_9c9f4.
Proof. vm_refl. Qed.
Lemma D_9c9f4 : decode_any W_9c9f4 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 384%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c9f8 : bv 32 := @BV 32 0x00450533%Z I.

Lemma D_9c9f8 : decode_any W_9c9f8 = Some (Op ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 5 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c9fc : bv 32 := @BV 32 0x00052503%Z I.

Lemma D_9c9fc : decode_any W_9c9fc = Some (Load SZ4 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ca00 : bv 32 := @BV 32 0x00a02533%Z I.

Lemma D_9ca00 : decode_any W_9ca00 = Some (Op ALU_SLT (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ca04 : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_9ca04 : decode_any W_9ca04 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_9c9f0_9ca08.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_51a9c_52858 OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_77ff8_78b0c. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_51a9c_52858 Bo_code_7005c_70b0c OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_77ff8_78b0c OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT.Bo_code_7ab0c_7b3f4 Bo_code_7d08c_7db0c Bo_code_9c9f0_9ca08.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
Section FPGen0.
Context {fx : FPState}.
Definition gauipc_addi (segs : list Segment) (base : word) (off1 off2 : Z) (rt rd : reg) (v : word) : Prop :=
  exists x : word,
    (forall regs mem rom,
        msteps segs (mkst regs (at_ base off1) mem rom) (mkst (regupd regs rt x) (at_ base (off1 + 4)) mem rom))
    /\ (forall regs mem rom,
           getr regs rt = x ->
           msteps segs (mkst regs (at_ base off2) mem rom) (mkst (regupd regs rd v) (at_ base (off2 + 4)) mem rom)).
End FPGen0.
Ltac gauipc_addi_tac Fa Da Fb Db :=
  let regs := fresh "regs" in let mem := fresh "mem" in let rom := fresh "rom" in
  let Hx := fresh "Hx" in
  wd_eexists; split;
  [ intros regs mem rom; lit_pc;
    (chain_step; [ reflexivity | eapply step_auipc; [exact Fa | reflexivity | exact Da] | step_simpl ]);
    gres; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_auipc in G in change_no_check G' end); vals_lit; close_eq
  | intros regs mem rom Hx; lit_pc;
    (chain_step; [ reflexivity | eapply step_addi; [exact Fb | reflexivity | exact Db] | step_simpl ]);
    gres; rewrite Hx; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); vals_lit; close_eq ].

Section FPGen1.
Context {fx : FPState}.

Definition rzl_words : list (option (bv 32)) :=
  [Some W_51bb4; Some W_51bb8; Some W_51bbc; Some W_51bc0; Some W_51bc4; Some W_51bc8; Some W_51bcc; Some W_51bd0;
   Some W_51bd4; Some W_51bd8; Some W_51bdc; Some W_51be0; Some W_51be4; None; None; None; Some W_51bf4; None;
   Some W_51bfc; Some W_51c00; Some W_51c04; Some W_51c08; Some W_51c0c; Some W_51c10; Some W_51c14; Some W_51c18;
   Some W_51c1c; Some W_51c20; Some W_51c24; Some W_51c28; Some W_51c2c; Some W_51c30]%list.

Definition rss_words : list (option (bv 32)) := [None; None; Some W_7b3ec; Some W_7b3f0]%list.
Definition cpm_words : list (option (bv 32)) := [None; None; Some W_70074; Some W_70078; Some W_7007c]%list.
Definition gts_words : list (option (bv 32)) :=
  [Some W_77ff8; Some W_77ffc; Some W_78000; Some W_78004; Some W_78008; Some W_7800c; Some W_78010; Some W_78014;
   Some W_78018]%list.
Definition rmh_words : list (option (bv 32)) :=
  [Some W_7d600; Some W_7d604; Some W_7d608; Some W_7d60c; Some W_7d610; Some W_7d614; Some W_7d618; Some W_7d61c;
   None; None; Some W_7d628; Some W_7d62c; Some W_7d630; Some W_7d634; Some W_7d638; Some W_7d63c; Some W_7d640;
   Some W_7d644; Some W_7d648; Some W_7d64c; Some W_7d650; Some W_7d654; Some W_7d658; Some W_7d65c; Some W_7d660;
   Some W_7d664; Some W_7d668; Some W_7d66c; Some W_7d670; Some W_7d674; Some W_7d678; Some W_7d67c; Some W_7d680;
   Some W_7d684; Some W_7d688; Some W_7d68c; Some W_7d690; Some W_7d694; Some W_7d698; Some W_7d69c; Some W_7d6a0;
   Some W_7d6a4; Some W_7d6a8; Some W_7d6ac; Some W_7d6b0; Some W_7d6b4]%list.
Definition lsn_words : list (option (bv 32)) :=
  [None; None; Some W_9c9f8; Some W_9c9fc; Some W_9ca00; Some W_9ca04]%list.


Section LEAVES.
  Variable segs : list Segment.
  Variable rb : word.
  Variables (g_rss g_cpm g_lsan : Z) (hooks : word).
  Hypothesis HRSS : code_ato segs rb 0x7b3e4 rss_words.
  Hypothesis GRSS : gloadb segs rb 0x7b3e4 10 g_rss.
  Hypothesis HCPM : code_ato segs rb 0x7006c cpm_words.
  Hypothesis GCPM : gloadb segs rb 0x7006c 10 g_cpm.
  Hypothesis HGTS : code_ato segs rb 0x77ff8 gts_words.
  Hypothesis HRMH : code_ato segs rb 0x7d600 rmh_words.
  Hypothesis GRMH : gaddr2 segs rb 0x7d620 10 18 hooks.
  Hypothesis HHK : code_ato segs rb 0x7d6b8 [Some W_7d6b8].         (* [comment removed for export] *)
  Hypothesis HLSN : code_ato segs rb 0x9c9f0 lsn_words.
  Hypothesis GLSN : gload segs rb 0x9c9f0 10 g_lsan.
  Hypothesis RBE : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.
  Variables (g_magic : Z) (TBL : word).                                (* [comment removed for export] *)
  Hypothesis HRZL : code_ato segs rb 0x51bb4 rzl_words.
  Hypothesis GRZM : gload segs rb 0x51be8 12 g_magic.
  Hypothesis GRZT : gauipc_addi segs rb 0x51bf0 0x51bf8 14 14 TBL.

  Lemma Ro8 : fetch_word segs (at_ rb 0x7b3ec) = Some W_7b3ec.  Proof using HRSS. exact (code_ato_get segs rb 0x7b3e4 rss_words 2 _ HRSS eq_refl). Qed.
  Lemma Ro12 : fetch_word segs (at_ rb 0x7b3f0) = Some W_7b3f0.  Proof using HRSS. exact (code_ato_get segs rb 0x7b3e4 rss_words 3 _ HRSS eq_refl). Qed.
  Lemma Co8 : fetch_word segs (at_ rb 0x70074) = Some W_70074.  Proof using HCPM. exact (code_ato_get segs rb 0x7006c cpm_words 2 _ HCPM eq_refl). Qed.
  Lemma Co12 : fetch_word segs (at_ rb 0x70078) = Some W_70078.  Proof using HCPM. exact (code_ato_get segs rb 0x7006c cpm_words 3 _ HCPM eq_refl). Qed.
  Lemma Co16 : fetch_word segs (at_ rb 0x7007c) = Some W_7007c.  Proof using HCPM. exact (code_ato_get segs rb 0x7006c cpm_words 4 _ HCPM eq_refl). Qed.
  Lemma If8968 : fetch_word segs (at_ rb 0x77ff8) = Some W_77ff8.  Proof using HGTS. exact (code_ato_get segs rb 0x77ff8 gts_words 0 _ HGTS eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If896c : fetch_word segs (at_ rb 0x77ffc) = Some W_77ffc.  Proof using HGTS. exact (code_ato_get segs rb 0x77ff8 gts_words 1 _ HGTS eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If8970 : fetch_word segs (at_ rb 0x78000) = Some W_78000.  Proof using HGTS. exact (code_ato_get segs rb 0x77ff8 gts_words 2 _ HGTS eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If8974 : fetch_word segs (at_ rb 0x78004) = Some W_78004.  Proof using HGTS. exact (code_ato_get segs rb 0x77ff8 gts_words 3 _ HGTS eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If8978 : fetch_word segs (at_ rb 0x78008) = Some W_78008.  Proof using HGTS. exact (code_ato_get segs rb 0x77ff8 gts_words 4 _ HGTS eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If897c : fetch_word segs (at_ rb 0x7800c) = Some W_7800c.  Proof using HGTS. exact (code_ato_get segs rb 0x77ff8 gts_words 5 _ HGTS eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If8980 : fetch_word segs (at_ rb 0x78010) = Some W_78010.  Proof using HGTS. exact (code_ato_get segs rb 0x77ff8 gts_words 6 _ HGTS eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If8984 : fetch_word segs (at_ rb 0x78014) = Some W_78014.  Proof using HGTS. exact (code_ato_get segs rb 0x77ff8 gts_words 7 _ HGTS eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If8988 : fetch_word segs (at_ rb 0x78018) = Some W_78018.  Proof using HGTS. exact (code_ato_get segs rb 0x77ff8 gts_words 8 _ HGTS eq_refl). Qed.   (* [comment removed for export] *)

  Lemma I10014c : fetch_word segs (at_ rb 0x7d600) = Some W_7d600.  Proof using HRMH. exact (code_ato_get segs rb 0x7d600 rmh_words 0 _ HRMH eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I100150 : fetch_word segs (at_ rb 0x7d604) = Some W_7d604.  Proof using HRMH. exact (code_ato_get segs rb 0x7d600 rmh_words 1 _ HRMH eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I100154 : fetch_word segs (at_ rb 0x7d608) = Some W_7d608.  Proof using HRMH. exact (code_ato_get segs rb 0x7d600 rmh_words 2 _ HRMH eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I100158 : fetch_word segs (at_ rb 0x7d60c) = Some W_7d60c.  Proof using HRMH. exact (code_ato_get segs rb 0x7d600 rmh_words 3 _ HRMH eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10015c : fetch_word segs (at_ rb 0x7d610) = Some W_7d610.  Proof using HRMH. exact (code_ato_get segs rb 0x7d600 rmh_words 4 _ HRMH eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I100160 : fetch_word segs (at_ rb 0x7d614) = Some W_7d614.  Proof using HRMH. exact (code_ato_get segs rb 0x7d600 rmh_words 5 _ HRMH eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I100164 : fetch_word segs (at_ rb 0x7d618) = Some W_7d618.  Proof using HRMH. exact (code_ato_get segs rb 0x7d600 rmh_words 6 _ HRMH eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I100168 : fetch_word segs (at_ rb 0x7d61c) = Some W_7d61c.  Proof using HRMH. exact (code_ato_get segs rb 0x7d600 rmh_words 7 _ HRMH eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I100174 : fetch_word segs (at_ rb 0x7d628) = Some W_7d628.  Proof using HRMH. exact (code_ato_get segs rb 0x7d600 rmh_words 10 _ HRMH eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I100178 : fetch_word segs (at_ rb 0x7d62c) = Some W_7d62c.  Proof using HRMH. exact (code_ato_get segs rb 0x7d600 rmh_words 11 _ HRMH eq_refl). Qed.



























   (* [comment removed for export] *)
  Lemma I1001ec : fetch_word segs (at_ rb 0x7d6a0) = Some W_7d6a0.  Proof using HRMH. exact (code_ato_get segs rb 0x7d600 rmh_words 40 _ HRMH eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I1001f0 : fetch_word segs (at_ rb 0x7d6a4) = Some W_7d6a4.  Proof using HRMH. exact (code_ato_get segs rb 0x7d600 rmh_words 41 _ HRMH eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I1001f4 : fetch_word segs (at_ rb 0x7d6a8) = Some W_7d6a8.  Proof using HRMH. exact (code_ato_get segs rb 0x7d600 rmh_words 42 _ HRMH eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I1001f8 : fetch_word segs (at_ rb 0x7d6ac) = Some W_7d6ac.  Proof using HRMH. exact (code_ato_get segs rb 0x7d600 rmh_words 43 _ HRMH eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I1001fc : fetch_word segs (at_ rb 0x7d6b0) = Some W_7d6b0.  Proof using HRMH. exact (code_ato_get segs rb 0x7d600 rmh_words 44 _ HRMH eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I100200 : fetch_word segs (at_ rb 0x7d6b4) = Some W_7d6b4.  Proof using HRMH. exact (code_ato_get segs rb 0x7d600 rmh_words 45 _ HRMH eq_refl). Qed.   (* [comment removed for export] *)

  Lemma I1213ac : fetch_word segs (at_ rb 0x9c9f8) = Some W_9c9f8.  Proof using HLSN. exact (code_ato_get segs rb 0x9c9f0 lsn_words 2 _ HLSN eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I1213b0 : fetch_word segs (at_ rb 0x9c9fc) = Some W_9c9fc.  Proof using HLSN. exact (code_ato_get segs rb 0x9c9f0 lsn_words 3 _ HLSN eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I1213b4 : fetch_word segs (at_ rb 0x9ca00) = Some W_9ca00.  Proof using HLSN. exact (code_ato_get segs rb 0x9c9f0 lsn_words 4 _ HLSN eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I1213b8 : fetch_word segs (at_ rb 0x9ca04) = Some W_9ca04.  Proof using HLSN. exact (code_ato_get segs rb 0x9c9f0 lsn_words 5 _ HLSN eq_refl). Qed.   (* [comment removed for export] *)


  Lemma I100204 : fetch_word segs (at_ rb 0x7d6b8) = Some W_7d6b8.  Proof using HHK. exact (code_ato_get segs rb 0x7d6b8 [Some W_7d6b8] 0 _ HHK eq_refl). Qed.
  Lemma RETrb : forall d, (d mod 2 = 0)%Z -> (0 <= d < 2 ^ 24)%Z -> ret_ok (at_ rb d).
  Proof using RBE. intros d Hd Hdr. destruct RBE as [E1 E2]. pose proof (u64_range rb). apply ret_ok_at; [exact E1 | exact Hd | lia]. Qed.

  (* [comment removed for export] *)
  Theorem rss_run : forall mem rom regs (ra : word),
    rdn segs mem (Z_to_bv 64 g_rss) 1 = Some [Z_to_bv 8 0] -> ret_ok ra -> getr regs 1 = ra ->
    exists r, msteps segs (mkst regs (at_ rb 0x7b3e4) mem rom) (mkst r ra mem rom)
      /\ getr r 10 = Z_to_bv 64 0 /\ regs_agree (fun x => In x [10]) regs r.
  Proof using GRSS HRSS.
    intros mem rom regs ra Rf Hret H1. wd_eexists. split; [|split].
    - eapply msteps_trans; [eapply GRSS; exact Rf|]. zlit_at.
      an Ro8 D_7b3ec.                                      (* [comment removed for export] *)
      aret Ro12 D_7b3f0 ra.
      wd_refl.
    - gres. reflexivity.
    - ra_solve.
  Qed.

  (* [comment removed for export] *)
  Theorem cpm_run : forall mem rom regs (ra : word),
    rdn segs mem (Z_to_bv 64 g_cpm) 1 = Some [Z_to_bv 8 1] -> ret_ok ra -> getr regs 1 = ra ->
    exists r, msteps segs (mkst regs (at_ rb 0x7006c) mem rom) (mkst r ra mem rom)
      /\ getr r 10 = Z_to_bv 64 1 /\ regs_agree (fun x => In x [10]) regs r.
  Proof using GCPM HCPM.
    intros mem rom regs ra Rf Hret H1. wd_eexists. split; [|split].
    - eapply msteps_trans; [eapply GCPM; exact Rf|]. zlit_at.
      afence Co8 D_70074.
      an Co12 D_70078.                                     (* [comment removed for export] *)
      aret Co16 D_7007c ra.
      wd_refl.
    - gres. reflexivity.
    - ra_solve.
  Qed.

  (* [comment removed for export] *)
  Theorem lsan_run : forall mem rom regs (ra tp : word) (off : Z),
    rdn segs mem (Z_to_bv 64 g_lsan) 8 = Some (LE8 (Z_to_bv 64 off)) -> (0 <= off)%Z -> (U tp + off + 4 <= 2 ^ 64)%Z ->
    rdn segs mem (at_ tp off) 4 = Some (LE4 0) ->
    ret_ok ra -> getr regs 1 = ra -> getr regs 4 = tp ->
    exists r, msteps segs (mkst regs (at_ rb 0x9c9f0) mem rom) (mkst r ra mem rom)
      /\ getr r 10 = Z_to_bv 64 0 /\ regs_agree (fun x => In x [10]) regs r.
  Proof using GLSN HLSN.
    intros mem rom regs ra tp off Rg Hoff Hnw Rc Hret H1 H4. pose proof (u64_range tp). wd_eexists. split; [|split].
    - eapply msteps_trans; [eapply GLSN; exact Rg|]. zlit_at.
      av I1213ac D_9c9f8 (at_ tp off) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add, at_ in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := LE4 0) (v := Z_to_bv 64 0);
          [exact I1213b0 | reflexivity | exact D_9c9fc | gres; rwH; imm_norm; rewrite ?v_addi_0; exact Rc | apply bytes4_small; lia]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      an I1213b4 D_9ca00.                                 (* [comment removed for export] *)
      aret I1213b8 D_9ca04 ra.
      wd_refl.
    - gres. reflexivity.
    - ra_solve.
  Qed.

  (* [comment removed for export] *)
  Theorem gts_run : forall t mem rom regs (ra sp tp tsdp tctx thr : word),
    gct_tab_ok segs t -> gt_rb t = rb ->
    gctH segs t mem (at_ sp (-16)) tp tsdp tctx thr ->
    store_ok segs mem (at_ sp (-8)) 8 = true -> (2 ^ 32 + 32 <= U sp)%Z -> (4096 <= U thr)%Z -> (U thr + 4096 <= 2 ^ 64)%Z ->
    ret_ok ra -> getr regs 1 = ra -> getr regs 2 = sp -> getr regs 4 = tp ->
    exists r, msteps segs (mkst regs (at_ rb 0x77ff8) mem rom)
                         (mkst r ra (wbytes (wbytes mem (at_ sp (-8)) (LE8 ra)) (at_ sp (-24)) (LE8 (at_ rb 0x78004))) rom)
      /\ getr r 10 = at_ thr 2800 /\ regs_agree (fun x => In x [10; 11]) regs r.
  Proof using RBE HGTS.
    intros t mem rom regs ra sp tp tsdp tctx thr TOK TRB GH SOK Gsp Gthr0 Gthr Hret H1 H2 H4.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range thr).
    set (M1 := wbytes mem (at_ sp (-8)) (LE8 ra)).
    assert (GH1 : gctH segs t M1 (at_ sp (-16)) tp tsdp tctx thr).
    { apply (gctH_keep segs t mem M1 _ _ _ _ _ GH); [| (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply wbytes_grows].
      intros x Hx. rewrite at_u in Hx by lia. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). rewrite wbytes_outside; [reflexivity | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    assert (W1 : exists r1, msteps segs (mkst regs (at_ rb 0x77ff8) mem rom) (mkst r1 (at_ rb 0x78e2c) M1 rom)
                 /\ getr r1 1 = at_ rb 0x78004 /\ getr r1 2 = at_ sp (-16) /\ getr r1 4 = tp /\ regs_agree (fun x => In x [1; 2; 10; 11]) regs r1).
    { wd_eexists. split.
      { an If8968 D_77ff8.                                 (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sd_at with (a := at_ sp (-8));
            [exact If896c | reflexivity | exact D_77ffc | gres; rwH; imm_norm; rewrite ?at_addi; f_equal; lia | gres; rwH; reflexivity | exact SOK]
          | step_simpl]; vn.                                (* [comment removed for export] *)
        change (wbytes _ _ _) with M1.
        an If8970 D_78000.                                 (* [comment removed for export] *)
        wd_refl. }
      post. ra_solve. }
    destruct W1 as (r1 & RUN1 & A1 & A2 & A4 & AG1).
    destruct (gct_run segs t TOK M1 rom r1 (at_ rb 0x78004) (at_ sp (-16)) tp tsdp tctx thr GH1 (RETrb 0x78004 eq_refl ltac:(lia))
                A1 A2 A4) as (r2 & RUN2 & B10 & B11 & AG2).
    rewrite TRB, at_at in RUN2. cbn [Z.add] in RUN2.
    pose proof (gh_tctx_nz _ _ _ _ _ _ _ _ GH) as NZ.
    wd_eexists. split; [|split].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
      ab_ft If8974 D_78004 ltac:(condz).                 (* [comment removed for export] *)
      an If8978 D_78008. an If897c D_7800c.              (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 ra) (v := ra);
          [exact If8980 | reflexivity | exact D_78010
          | gres; rwH; rewrite (AG2 2) by notin_list; rwH; imm_norm; rewrite ?at_addi; zlit_at;
            rewrite rdn_wbytes_out; [apply rdn_wbytes_hit8; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]]
          | apply bytes_le_to_Z_8 ]
        | step_simpl]; vn.                                  (* [comment removed for export] *)
      an If8984 D_78014.                                    (* [comment removed for export] *)
      aret If8988 D_78018 ra.
      wd_refl.
    - gres. rewrite ?B10, ?at_at. first [reflexivity | f_equal; lia].
    - apply (regs_agree_strengthen [10; 11] [1; 2; 10; 11] regs).
      + eapply regs_agree_trans; [exact AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG2|]. ra_solve.
      + intros i Hi Hni. cbn [In] in Hi.
        repeat (destruct Hi as [<-|Hi]; [gres; rewrite ?(AG2 2) by notin_list; rwH; rewrite ?at_addi, ?at_0; first [reflexivity | symmetry; assumption | f_equal; lia | exfalso; apply Hni; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto] |]).
        destruct Hi.
  Qed.

  (* [comment removed for export] *)
  Theorem rmh_run : forall mem rom regs (ra sp : word),
    rdn segs mem hooks 8 = Some (LE8 (Z_to_bv 64 0)) -> (U hooks + 8 <= 2 ^ 32)%Z ->
    store_ok segs mem (at_ sp (-32)) 32 = true -> (2 ^ 32 + 32 <= U sp)%Z ->
    ret_ok ra -> getr regs 1 = ra -> getr regs 2 = sp ->
    exists r, msteps segs (mkst regs (at_ rb 0x7d600) mem rom)
                         (mkst r ra (wbytes (wbytes (wbytes (wbytes mem (at_ sp (-8)) (LE8 ra)) (at_ sp (-16)) (LE8 (getr regs 8)))
                                               (at_ sp (-24)) (LE8 (getr regs 9))) (at_ sp (-32)) (LE8 (getr regs 18))) rom)
      /\ regs_agree (fun x => In x [10; 11; 12]) regs r.
  Proof using RBE HHK GRMH HRMH.
    intros mem rom regs ra sp Rh Hh SOK Gsp Hret H1 H2. pose proof (u64_range sp) as Hspr. pose proof (u64_range hooks).
    destruct GRMH as [gx GA].
    Ltac fsdh F D aa Hs lo :=
      chain_step; [reflexivity
        | eapply step_sd_at with (a := aa);
          [exact F | reflexivity | exact D | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia] | gres; rwH; reflexivity
          | repeat (eapply store_ok_mono; [apply wbytes_grows|]);
            eapply (store_ok_sub segs _ lo _ 32); [rewrite at_u; lia | exact Hs | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia] ]
        | step_simpl]; vn.
    wd_eexists. split.
    - an I10014c D_7d600.                                    (* [comment removed for export] *)
      fsdh I100150 D_7d604 (at_ sp (-8)) SOK (at_ sp (-32)).
      fsdh I100154 D_7d608 (at_ sp (-16)) SOK (at_ sp (-32)).
      fsdh I100158 D_7d60c (at_ sp (-24)) SOK (at_ sp (-32)).
      fsdh I10015c D_7d610 (at_ sp (-32)) SOK (at_ sp (-32)).
      an I100160 D_7d614. an I100164 D_7d618.               (* [comment removed for export] *)
      an I100168 D_7d61c.                                    (* [comment removed for export] *)
      pose proof (RETrb 0x7d620 eq_refl ltac:(lia)) as RT1.
      aret I100204 D_7d6b8 (at_ rb 0x7d620).                 (* [comment removed for export] *)
      eapply msteps_trans; [apply GA|]. zlit_at.             (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
          [exact I100174 | reflexivity | exact D_7d628
          | gres; rwH; imm_norm; rewrite ?v_addi_0; rewrite <- Rh; apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x Hx; cbn in Hx;
              rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia; reflexivity]
          | apply bytes_le_to_Z_8 ]
        | step_simpl]; vn.                                  (* [comment removed for export] *)
      ab_tk I100178 D_7d62c ltac:(condz).                   (* [comment removed for export] *)
      Ltac rl F D vv := chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 vv) (v := vv);
          [exact F | reflexivity | exact D | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; rd8_chain | apply bytes_le_to_Z_8]
        | step_simpl]; vn.
      rl I1001ec D_7d6a0 ra. rl I1001f0 D_7d6a4 (getr regs 8). rl I1001f4 D_7d6a8 (getr regs 9). rl I1001f8 D_7d6ac (getr regs 18).
      an I1001fc D_7d6b0.                                    (* [comment removed for export] *)
      aret I100200 D_7d6b4 ra.
      wd_refl.
    - apply (regs_agree_strengthen [10; 11; 12] [1; 2; 8; 9; 18; 10; 11; 12] regs).
      + ra_solve.
      + intros i Hi Hni. cbn [In] in Hi.
        repeat (destruct Hi as [<-|Hi]; [gres; rwH; rewrite ?at_addi, ?at_0; first [reflexivity | symmetry; assumption | f_equal; lia | exfalso; apply Hni; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto] |]).
        destruct Hi.
  Qed.
  Lemma I6d430 : fetch_word segs (at_ rb 0x51bb4) = Some W_51bb4.  Proof using HRZL. exact (code_ato_get segs rb 0x51bb4 rzl_words 0 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6d434 : fetch_word segs (at_ rb 0x51bb8) = Some W_51bb8.  Proof using HRZL. exact (code_ato_get segs rb 0x51bb4 rzl_words 1 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6d438 : fetch_word segs (at_ rb 0x51bbc) = Some W_51bbc.  Proof using HRZL. exact (code_ato_get segs rb 0x51bb4 rzl_words 2 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6d43c : fetch_word segs (at_ rb 0x51bc0) = Some W_51bc0.  Proof using HRZL. exact (code_ato_get segs rb 0x51bb4 rzl_words 3 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6d440 : fetch_word segs (at_ rb 0x51bc4) = Some W_51bc4.  Proof using HRZL. exact (code_ato_get segs rb 0x51bb4 rzl_words 4 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6d444 : fetch_word segs (at_ rb 0x51bc8) = Some W_51bc8.  Proof using HRZL. exact (code_ato_get segs rb 0x51bb4 rzl_words 5 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6d448 : fetch_word segs (at_ rb 0x51bcc) = Some W_51bcc.  Proof using HRZL. exact (code_ato_get segs rb 0x51bb4 rzl_words 6 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6d44c : fetch_word segs (at_ rb 0x51bd0) = Some W_51bd0.  Proof using HRZL. exact (code_ato_get segs rb 0x51bb4 rzl_words 7 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6d450 : fetch_word segs (at_ rb 0x51bd4) = Some W_51bd4.  Proof using HRZL. exact (code_ato_get segs rb 0x51bb4 rzl_words 8 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6d454 : fetch_word segs (at_ rb 0x51bd8) = Some W_51bd8.  Proof using HRZL. exact (code_ato_get segs rb 0x51bb4 rzl_words 9 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6d458 : fetch_word segs (at_ rb 0x51bdc) = Some W_51bdc.  Proof using HRZL. exact (code_ato_get segs rb 0x51bb4 rzl_words 10 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6d45c : fetch_word segs (at_ rb 0x51be0) = Some W_51be0.  Proof using HRZL. exact (code_ato_get segs rb 0x51bb4 rzl_words 11 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6d460 : fetch_word segs (at_ rb 0x51be4) = Some W_51be4.  Proof using HRZL. exact (code_ato_get segs rb 0x51bb4 rzl_words 12 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6d470 : fetch_word segs (at_ rb 0x51bf4) = Some W_51bf4.  Proof using HRZL. exact (code_ato_get segs rb 0x51bb4 rzl_words 16 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6d478 : fetch_word segs (at_ rb 0x51bfc) = Some W_51bfc.  Proof using HRZL. exact (code_ato_get segs rb 0x51bb4 rzl_words 18 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6d47c : fetch_word segs (at_ rb 0x51c00) = Some W_51c00.  Proof using HRZL. exact (code_ato_get segs rb 0x51bb4 rzl_words 19 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6d480 : fetch_word segs (at_ rb 0x51c04) = Some W_51c04.  Proof using HRZL. exact (code_ato_get segs rb 0x51bb4 rzl_words 20 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6d484 : fetch_word segs (at_ rb 0x51c08) = Some W_51c08.  Proof using HRZL. exact (code_ato_get segs rb 0x51bb4 rzl_words 21 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6d488 : fetch_word segs (at_ rb 0x51c0c) = Some W_51c0c.  Proof using HRZL. exact (code_ato_get segs rb 0x51bb4 rzl_words 22 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6d48c : fetch_word segs (at_ rb 0x51c10) = Some W_51c10.  Proof using HRZL. exact (code_ato_get segs rb 0x51bb4 rzl_words 23 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6d490 : fetch_word segs (at_ rb 0x51c14) = Some W_51c14.  Proof using HRZL. exact (code_ato_get segs rb 0x51bb4 rzl_words 24 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6d494 : fetch_word segs (at_ rb 0x51c18) = Some W_51c18.  Proof using HRZL. exact (code_ato_get segs rb 0x51bb4 rzl_words 25 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6d498 : fetch_word segs (at_ rb 0x51c1c) = Some W_51c1c.  Proof using HRZL. exact (code_ato_get segs rb 0x51bb4 rzl_words 26 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6d49c : fetch_word segs (at_ rb 0x51c20) = Some W_51c20.  Proof using HRZL. exact (code_ato_get segs rb 0x51bb4 rzl_words 27 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6d4a0 : fetch_word segs (at_ rb 0x51c24) = Some W_51c24.  Proof using HRZL. exact (code_ato_get segs rb 0x51bb4 rzl_words 28 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6d4a4 : fetch_word segs (at_ rb 0x51c28) = Some W_51c28.  Proof using HRZL. exact (code_ato_get segs rb 0x51bb4 rzl_words 29 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6d4a8 : fetch_word segs (at_ rb 0x51c2c) = Some W_51c2c.  Proof using HRZL. exact (code_ato_get segs rb 0x51bb4 rzl_words 30 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6d4ac : fetch_word segs (at_ rb 0x51c30) = Some W_51c30.  Proof using HRZL. exact (code_ato_get segs rb 0x51bb4 rzl_words 31 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)


  Definition MAGICw : word := Z_to_bv 64 0x0218a392cd3d5dbf.

  (* [comment removed for export] *)
  Section RZL.
    Variables (mem rom : word -> option byte) (regs : bvmap 5 word) (ra sp : word).
    Hypothesis Rm : rdn segs mem (Z_to_bv 64 g_magic) 8 = Some (LE8 MAGICw).
    Hypothesis GT : (U TBL + 64 <= 2 ^ 64)%Z.
    Hypothesis SOK : store_ok segs mem (at_ sp (-8)) 8 = true.
    Hypothesis Gsp : (8 <= U sp)%Z.
    Hypothesis Gsep : (U sp <= U TBL \/ U TBL + 64 <= U sp - 8)%Z.
    Hypothesis Gm : (0 <= g_magic /\ g_magic + 8 <= U sp - 8)%Z.
    Hypothesis Hret : ret_ok ra.
    Hypothesis H1 : getr regs 1 = ra.
    Hypothesis H2 : getr regs 2 = sp.
    Definition rzM1 := wbytes mem (at_ sp (-8)) (LE8 ra).
    Lemma rzM1_out : forall y : word, (U y < U sp - 8 \/ U sp <= U y)%Z -> rzM1 y = mem y.
    Proof using Gsp rb.
      intros y Hy. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold rzM1 in G in change_no_check G' end).
      rewrite wbytes_outside; [reflexivity | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    Qed.
    Lemma rzRm1 : rdn segs rzM1 (Z_to_bv 64 g_magic) 8 = Some (LE8 MAGICw).
    Proof using Gm Gsp GT Rm TBL rb. pose proof (u64_range sp). rewrite <- Rm. apply rdn_ext; [wd_ulia_c | intros y Hy; apply rzM1_out; revert Hy; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hy; lia]. Qed.
    Lemma rzRt1 : forall idx L, (0 <= idx < 63)%Z -> rdn segs mem (at_ TBL idx) 1 = Some [Z_to_bv 8 L] -> rdn segs rzM1 (at_ TBL idx) 1 = Some [Z_to_bv 8 L].
    Proof using Gm Gsep Gsp GT g_magic rb.
      intros idx L Hidx Rt. pose proof (u64_range sp). pose proof (u64_range TBL).
      rewrite <- Rt. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros y Hy; apply rzM1_out; rewrite at_u in Hy by lia; cbn in Hy; lia].
    Qed.

    Ltac rzl_walk Rt1 GA GB :=
      an I6d430 D_51bb4;                                     (* [comment removed for export] *)
      (chain_step; [reflexivity
        | eapply step_sd_at with (a := at_ sp (-8));
          [exact I6d434 | reflexivity | exact D_51bb8 | gres; rwH; imm_norm; rewrite ?at_addi; f_equal; lia | gres; rwH; reflexivity | exact SOK]
        | step_simpl]); vn;                                 (* [comment removed for export] *)
      change (wbytes _ _ _) with rzM1;
      an I6d438 D_51bbc; an I6d43c D_51bc0; an I6d440 D_51bc4;   (* [comment removed for export] *)
      ab_ft I6d444 D_51bc8 ltac:(condz);                    (* [comment removed for export] *)
      an I6d448 D_51bcc; an I6d44c D_51bd0;
      ab_ft I6d450 D_51bd4 ltac:(condz);                    (* [comment removed for export] *)
      an I6d454 D_51bd8; an I6d458 D_51bdc;
      ab_ft I6d45c D_51be0 ltac:(condz);                    (* [comment removed for export] *)
      an I6d460 D_51be4;                                     (* [comment removed for export] *)
      (eapply msteps_trans; [eapply GRZM; exact rzRm1|]); zlit_at;   (* [comment removed for export] *)
      (eapply msteps_trans; [apply GA|]); zlit_at;           (* [comment removed for export] *)
      an I6d470 D_51bf4;                                     (* [comment removed for export] *)
      (eapply msteps_trans; [apply GB; gres; reflexivity|]); zlit_at;   (* [comment removed for export] *)
      rewrite ?regupd_regupd_same;
      an I6d478 D_51bfc;                                     (* [comment removed for export] *)
      an I6d47c D_51c00;                                     (* [comment removed for export] *)
      match goal with |- context [regupd _ 11 (Z_to_bv 64 ?i)] =>
        av I6d480 D_51c04 (at_ TBL i) ltac:(apply v_add_at; lia) end;   (* [comment removed for export] *)
      (chain_step; [reflexivity
        | eapply step_lbu; [exact I6d484 | reflexivity | exact D_51c08 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact Rt1]
        | step_simpl]); vn;                                 (* [comment removed for export] *)
      an I6d488 D_51c0c; an I6d48c D_51c10;                 (* [comment removed for export] *)
      ab_ft I6d490 D_51c14 ltac:(condz);                    (* [comment removed for export] *)
      an I6d494 D_51c18; an I6d498 D_51c1c;                 (* [comment removed for export] *)
      ab_ft I6d49c D_51c20 ltac:(condz);                    (* [comment removed for export] *)
      an I6d4a0 D_51c24;                                     (* [comment removed for export] *)
      (chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 ra) (v := ra);
          [exact I6d4a4 | reflexivity | exact D_51c28 | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold rzM1 in G in change_no_check G' end); apply rdn_wbytes_hit8; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | apply bytes_le_to_Z_8]
        | step_simpl]); vn;                                 (* [comment removed for export] *)
      an I6d4a8 D_51c2c;                                     (* [comment removed for export] *)
      aret I6d4ac D_51c30 ra;
      wd_refl.
    Ltac rzl_post :=
      apply (regs_agree_strengthen [10; 11; 12; 13; 14] [1; 2; 10; 11; 12; 13; 14] regs); [ra_solve|];
      intros i Hi Hni; cbn [In] in Hi;
      repeat (destruct Hi as [<-|Hi]; [gres; rwH; rewrite ?at_addi, ?at_0; first [reflexivity | symmetry; assumption | f_equal; lia | exfalso; apply Hni; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto] |]);
      destruct Hi.

    Theorem rzl16_run : rdn segs mem (at_ TBL 8) 1 = Some [Z_to_bv 8 4] -> getr regs 10 = Z_to_bv 64 16 ->
      exists r, msteps segs (mkst regs (at_ rb 0x51bb4) mem rom) (mkst r ra rzM1 rom)
        /\ getr r 10 = Z_to_bv 64 0 /\ regs_agree (fun r => In r [10; 11; 12; 13; 14]) regs r.
    Proof using H2 H1 Hret Gm Gsep Gsp SOK GT Rm GRZT GRZM HRZL g_magic RBE.
      intros Rt H10. pose proof (u64_range sp) as Hspr. pose proof (u64_range TBL) as HT.
      pose proof (rzRt1 8 4 ltac:(lia) Rt) as Rt1. destruct GRZT as [gx [GA GB]].
      wd_eexists. split; [|split]; [rzl_walk Rt1 GA GB | gres; reflexivity | rzl_post].
    Qed.
    Theorem rzl2048_run : rdn segs mem (at_ TBL 49) 1 = Some [Z_to_bv 8 11] -> getr regs 10 = Z_to_bv 64 2048 ->
      exists r, msteps segs (mkst regs (at_ rb 0x51bb4) mem rom) (mkst r ra rzM1 rom)
        /\ getr r 10 = Z_to_bv 64 7 /\ regs_agree (fun r => In r [10; 11; 12; 13; 14]) regs r.
    Proof using H2 H1 Hret Gm Gsep Gsp SOK GT Rm GRZT GRZM HRZL g_magic RBE.
      intros Rt H10. pose proof (u64_range sp) as Hspr. pose proof (u64_range TBL) as HT.
      pose proof (rzRt1 49 11 ltac:(lia) Rt) as Rt1. destruct GRZT as [gx [GA GB]].
      wd_eexists. split; [|split]; [rzl_walk Rt1 GA GB | gres; reflexivity | rzl_post].
    Qed.
  End RZL.
End LEAVES.
End FPGen1.
