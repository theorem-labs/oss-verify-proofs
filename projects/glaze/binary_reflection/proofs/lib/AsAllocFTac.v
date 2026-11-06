(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.Asan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.InstrEnc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsCodeM0.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Asan.

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

(* [comment removed for export] *)
Definition W_4b7e0 : bv 32 := @BV 32 0x00060793%Z I.
Lemma F_4b7e0 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b7e8%Z I : word) = Some W_4b7e0.
Proof. vm_refl. Qed.
Lemma D_4b7e0 : decode_any W_4b7e0 = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b7e4 : bv 32 := @BV 32 0x00058713%Z I.
Lemma F_4b7e4 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b7ec%Z I : word) = Some W_4b7e4.
Proof. vm_refl. Qed.
Lemma D_4b7e4 : decode_any W_4b7e4 = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b7e8 : bv 32 := @BV 32 0x000b8597%Z I.
Lemma F_4b7e8 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b7f0%Z I : word) = Some W_4b7e8.
Proof. vm_refl. Qed.
Lemma D_4b7e8 : decode_any W_4b7e8 = Some (Auipc (@BV 5 11%Z I) (@BV 20 184%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b7ec : bv 32 := @BV 32 0x72858593%Z I.
Lemma F_4b7ec : fetch_word Asan.M.loaded_segments (@BV 64 0x4b7f4%Z I : word) = Some W_4b7ec.
Proof. vm_refl. Qed.
Lemma D_4b7ec : decode_any W_4b7ec = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 1832%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b7f0 : bv 32 := @BV 32 0x00050613%Z I.
Lemma F_4b7f0 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b7f8%Z I : word) = Some W_4b7f0.
Proof. vm_refl. Qed.
Lemma D_4b7f0 : decode_any W_4b7f0 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b7f4 : bv 32 := @BV 32 0x00058513%Z I.
Lemma F_4b7f4 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b7fc%Z I : word) = Some W_4b7f4.
Proof. vm_refl. Qed.
Lemma D_4b7f4 : decode_any W_4b7f4 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b7f8 : bv 32 := @BV 32 0x00060593%Z I.
Lemma F_4b7f8 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b800%Z I : word) = Some W_4b7f8.
Proof. vm_refl. Qed.
Lemma D_4b7f8 : decode_any W_4b7f8 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b7fc : bv 32 := @BV 32 0x00000613%Z I.
Lemma F_4b7fc : fetch_word Asan.M.loaded_segments (@BV 64 0x4b804%Z I : word) = Some W_4b7fc.
Proof. vm_refl. Qed.
Lemma D_4b7fc : decode_any W_4b7fc = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b800 : bv 32 := @BV 32 0x00000693%Z I.
Lemma F_4b800 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b808%Z I : word) = Some W_4b800.
Proof. vm_refl. Qed.
Lemma D_4b800 : decode_any W_4b800 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b804 : bv 32 := @BV 32 0x0040006f%Z I.
Lemma F_4b804 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b80c%Z I : word) = Some W_4b804.
Proof. vm_refl. Qed.
Lemma D_4b804 : decode_any W_4b804 = Some (Jal (@BV 5 0%Z I) (@BV 21 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b808 : bv 32 := @BV 32 0xfc010113%Z I.
Lemma F_4b808 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b810%Z I : word) = Some W_4b808.
Proof. vm_refl. Qed.
Lemma D_4b808 : decode_any W_4b808 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4032%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b80c : bv 32 := @BV 32 0x02113c23%Z I.
Lemma F_4b80c : fetch_word Asan.M.loaded_segments (@BV 64 0x4b814%Z I : word) = Some W_4b80c.
Proof. vm_refl. Qed.
Lemma D_4b80c : decode_any W_4b80c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b810 : bv 32 := @BV 32 0x02813823%Z I.
Lemma F_4b810 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b818%Z I : word) = Some W_4b810.
Proof. vm_refl. Qed.
Lemma D_4b810 : decode_any W_4b810 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b814 : bv 32 := @BV 32 0x02913423%Z I.
Lemma F_4b814 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b81c%Z I : word) = Some W_4b814.
Proof. vm_refl. Qed.
Lemma D_4b814 : decode_any W_4b814 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b818 : bv 32 := @BV 32 0x03213023%Z I.
Lemma F_4b818 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b820%Z I : word) = Some W_4b818.
Proof. vm_refl. Qed.
Lemma D_4b818 : decode_any W_4b818 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b81c : bv 32 := @BV 32 0x01313c23%Z I.
Lemma F_4b81c : fetch_word Asan.M.loaded_segments (@BV 64 0x4b824%Z I : word) = Some W_4b81c.
Proof. vm_refl. Qed.
Lemma D_4b81c : decode_any W_4b81c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 19%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b820 : bv 32 := @BV 32 0x01413823%Z I.
Lemma F_4b820 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b828%Z I : word) = Some W_4b820.
Proof. vm_refl. Qed.
Lemma D_4b820 : decode_any W_4b820 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 20%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b824 : bv 32 := @BV 32 0x01513423%Z I.
Lemma F_4b824 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b82c%Z I : word) = Some W_4b824.
Proof. vm_refl. Qed.
Lemma D_4b824 : decode_any W_4b824 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 21%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b828 : bv 32 := @BV 32 0x01613023%Z I.
Lemma F_4b828 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b830%Z I : word) = Some W_4b828.
Proof. vm_refl. Qed.
Lemma D_4b828 : decode_any W_4b828 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 22%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b82c : bv 32 := @BV 32 0x02058e63%Z I.
Lemma F_4b82c : fetch_word Asan.M.loaded_segments (@BV 64 0x4b834%Z I : word) = Some W_4b82c.
Proof. vm_refl. Qed.
Lemma D_4b82c : decode_any W_4b82c = Some (Branch BC_EQ (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 60%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b830 : bv 32 := @BV 32 0x00078a13%Z I.
Lemma F_4b830 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b838%Z I : word) = Some W_4b830.
Proof. vm_refl. Qed.
Lemma D_4b830 : decode_any W_4b830 = Some (OpImm ALU_ADD (@BV 5 20%Z I) (@BV 5 15%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b834 : bv 32 := @BV 32 0x00070413%Z I.
Lemma F_4b834 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b83c%Z I : word) = Some W_4b834.
Proof. vm_refl. Qed.
Lemma D_4b834 : decode_any W_4b834 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 14%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b838 : bv 32 := @BV 32 0x00058493%Z I.
Lemma F_4b838 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b840%Z I : word) = Some W_4b838.
Proof. vm_refl. Qed.
Lemma D_4b838 : decode_any W_4b838 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b83c : bv 32 := @BV 32 0x00050993%Z I.
Lemma F_4b83c : fetch_word Asan.M.loaded_segments (@BV 64 0x4b844%Z I : word) = Some W_4b83c.
Proof. vm_refl. Qed.
Lemma D_4b83c : decode_any W_4b83c = Some (OpImm ALU_ADD (@BV 5 19%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b840 : bv 32 := @BV 32 0x00060a93%Z I.
Lemma F_4b840 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b848%Z I : word) = Some W_4b840.
Proof. vm_refl. Qed.
Lemma D_4b840 : decode_any W_4b840 = Some (OpImm ALU_ADD (@BV 5 21%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b844 : bv 32 := @BV 32 0x00068b13%Z I.
Lemma F_4b844 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b84c%Z I : word) = Some W_4b844.
Proof. vm_refl. Qed.
Lemma D_4b844 : decode_any W_4b844 = Some (OpImm ALU_ADD (@BV 5 22%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b848 : bv 32 := @BV 32 0xff058913%Z I.
Lemma F_4b848 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b850%Z I : word) = Some W_4b848.
Proof. vm_refl. Qed.
Lemma D_4b848 : decode_any W_4b848 = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 11%Z I) (@BV 12 4080%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b84c : bv 32 := @BV 32 0x00058513%Z I.
Lemma F_4b84c : fetch_word Asan.M.loaded_segments (@BV 64 0x4b854%Z I : word) = Some W_4b84c.
Proof. vm_refl. Qed.
Lemma D_4b84c : decode_any W_4b84c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b850 : bv 32 := @BV 32 0x3f4310ef%Z I.
Lemma F_4b850 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b858%Z I : word) = Some W_4b850.
Proof. vm_refl. Qed.
Lemma D_4b850 : decode_any W_4b850 = Some (Jal (@BV 5 1%Z I) (@BV 21 201716%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b854 : bv 32 := @BV 32 0x02050e63%Z I.
Lemma F_4b854 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b85c%Z I : word) = Some W_4b854.
Proof. vm_refl. Qed.
Lemma D_4b854 : decode_any W_4b854 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 60%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b868 : bv 32 := @BV 32 0x03813083%Z I.
Lemma F_4b868 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b870%Z I : word) = Some W_4b868.
Proof. vm_refl. Qed.
Lemma D_4b868 : decode_any W_4b868 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b86c : bv 32 := @BV 32 0x03013403%Z I.
Lemma F_4b86c : fetch_word Asan.M.loaded_segments (@BV 64 0x4b874%Z I : word) = Some W_4b86c.
Proof. vm_refl. Qed.
Lemma D_4b86c : decode_any W_4b86c = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b870 : bv 32 := @BV 32 0x02813483%Z I.
Lemma F_4b870 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b878%Z I : word) = Some W_4b870.
Proof. vm_refl. Qed.
Lemma D_4b870 : decode_any W_4b870 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b874 : bv 32 := @BV 32 0x02013903%Z I.
Lemma F_4b874 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b87c%Z I : word) = Some W_4b874.
Proof. vm_refl. Qed.
Lemma D_4b874 : decode_any W_4b874 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b878 : bv 32 := @BV 32 0x01813983%Z I.
Lemma F_4b878 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b880%Z I : word) = Some W_4b878.
Proof. vm_refl. Qed.
Lemma D_4b878 : decode_any W_4b878 = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b87c : bv 32 := @BV 32 0x01013a03%Z I.
Lemma F_4b87c : fetch_word Asan.M.loaded_segments (@BV 64 0x4b884%Z I : word) = Some W_4b87c.
Proof. vm_refl. Qed.
Lemma D_4b87c : decode_any W_4b87c = Some (Load SZ8 true (@BV 5 20%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b880 : bv 32 := @BV 32 0x00813a83%Z I.
Lemma F_4b880 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b888%Z I : word) = Some W_4b880.
Proof. vm_refl. Qed.
Lemma D_4b880 : decode_any W_4b880 = Some (Load SZ8 true (@BV 5 21%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b884 : bv 32 := @BV 32 0x00013b03%Z I.
Lemma F_4b884 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b88c%Z I : word) = Some W_4b884.
Proof. vm_refl. Qed.
Lemma D_4b884 : decode_any W_4b884 = Some (Load SZ8 true (@BV 5 22%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b888 : bv 32 := @BV 32 0x04010113%Z I.
Lemma F_4b888 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b890%Z I : word) = Some W_4b888.
Proof. vm_refl. Qed.
Lemma D_4b888 : decode_any W_4b888 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b88c : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_4b88c : fetch_word Asan.M.loaded_segments (@BV 64 0x4b894%Z I : word) = Some W_4b88c.
Proof. vm_refl. Qed.
Lemma D_4b88c : decode_any W_4b88c = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b890 : bv 32 := @BV 32 0xffc97693%Z I.
Lemma F_4b890 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b898%Z I : word) = Some W_4b890.
Proof. vm_refl. Qed.
Lemma D_4b890 : decode_any W_4b890 = Some (OpImm ALU_AND (@BV 5 13%Z I) (@BV 5 18%Z I) (@BV 12 4092%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b894 : bv 32 := @BV 32 0x00391513%Z I.
Lemma F_4b894 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b89c%Z I : word) = Some W_4b894.
Proof. vm_refl. Qed.
Lemma D_4b894 : decode_any W_4b894 = Some (ShiftImm ALU_SLL (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 6 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b898 : bv 32 := @BV 32 0x0ff00613%Z I.
Lemma F_4b898 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b8a0%Z I : word) = Some W_4b898.
Proof. vm_refl. Qed.
Lemma D_4b898 : decode_any W_4b898 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 255%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b89c : bv 32 := @BV 32 0x00200713%Z I.
Lemma F_4b89c : fetch_word Asan.M.loaded_segments (@BV 64 0x4b8a4%Z I : word) = Some W_4b89c.
Proof. vm_refl. Qed.
Lemma D_4b89c : decode_any W_4b89c = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 12 2%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b8a0 : bv 32 := @BV 32 0x00300593%Z I.
Lemma F_4b8a0 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b8a8%Z I : word) = Some W_4b8a0.
Proof. vm_refl. Qed.
Lemma D_4b8a0 : decode_any W_4b8a0 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b8a4 : bv 32 := @BV 32 0x00a617bb%Z I.
Lemma F_4b8a4 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b8ac%Z I : word) = Some W_4b8a4.
Proof. vm_refl. Qed.
Lemma D_4b8a4 : decode_any W_4b8a4 = Some (Op32 ALU_SLL (@BV 5 15%Z I) (@BV 5 12%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b8a8 : bv 32 := @BV 32 0x00a7173b%Z I.
Lemma F_4b8a8 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b8b0%Z I : word) = Some W_4b8a8.
Proof. vm_refl. Qed.
Lemma D_4b8a8 : decode_any W_4b8a8 = Some (Op32 ALU_SLL (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b8ac : bv 32 := @BV 32 0x00a5983b%Z I.
Lemma F_4b8ac : fetch_word Asan.M.loaded_segments (@BV 64 0x4b8b4%Z I : word) = Some W_4b8ac.
Proof. vm_refl. Qed.
Lemma D_4b8ac : decode_any W_4b8ac = Some (Op32 ALU_SLL (@BV 5 16%Z I) (@BV 5 11%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b8b0 : bv 32 := @BV 32 0x1606a62f%Z I.
Lemma F_4b8b0 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b8b8%Z I : word) = Some W_4b8b0.
Proof. vm_refl. Qed.
Lemma D_4b8b0 : decode_any W_4b8b0 = Some (Lr AW true true (@BV 5 12%Z I) (@BV 5 13%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b8b4 : bv 32 := @BV 32 0x00f678b3%Z I.
Lemma F_4b8b4 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b8bc%Z I : word) = Some W_4b8b4.
Proof. vm_refl. Qed.
Lemma D_4b8b4 : decode_any W_4b8b4 = Some (Op ALU_AND (@BV 5 17%Z I) (@BV 5 12%Z I) (@BV 5 15%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b8b8 : bv 32 := @BV 32 0x08e89063%Z I.
Lemma F_4b8b8 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b8c0%Z I : word) = Some W_4b8b8.
Proof. vm_refl. Qed.
Lemma D_4b8b8 : decode_any W_4b8b8 = Some (Branch BC_NE (@BV 5 17%Z I) (@BV 5 14%Z I) (@BV 13 128%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b8bc : bv 32 := @BV 32 0x010648b3%Z I.
Lemma F_4b8bc : fetch_word Asan.M.loaded_segments (@BV 64 0x4b8c4%Z I : word) = Some W_4b8bc.
Proof. vm_refl. Qed.
Lemma D_4b8bc : decode_any W_4b8bc = Some (Op ALU_XOR (@BV 5 17%Z I) (@BV 5 12%Z I) (@BV 5 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b8c0 : bv 32 := @BV 32 0x00f8f8b3%Z I.
Lemma F_4b8c0 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b8c8%Z I : word) = Some W_4b8c0.
Proof. vm_refl. Qed.
Lemma D_4b8c0 : decode_any W_4b8c0 = Some (Op ALU_AND (@BV 5 17%Z I) (@BV 5 17%Z I) (@BV 5 15%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b8c4 : bv 32 := @BV 32 0x011648b3%Z I.
Lemma F_4b8c4 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b8cc%Z I : word) = Some W_4b8c4.
Proof. vm_refl. Qed.
Lemma D_4b8c4 : decode_any W_4b8c4 = Some (Op ALU_XOR (@BV 5 17%Z I) (@BV 5 12%Z I) (@BV 5 17%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b8c8 : bv 32 := @BV 32 0x1b16a8af%Z I.
Lemma F_4b8c8 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b8d0%Z I : word) = Some W_4b8c8.
Proof. vm_refl. Qed.
Lemma D_4b8c8 : decode_any W_4b8c8 = Some (Sc AW false true (@BV 5 17%Z I) (@BV 5 13%Z I) (@BV 5 17%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b8cc : bv 32 := @BV 32 0xfe0892e3%Z I.
Lemma F_4b8cc : fetch_word Asan.M.loaded_segments (@BV 64 0x4b8d4%Z I : word) = Some W_4b8cc.
Proof. vm_refl. Qed.
Lemma D_4b8cc : decode_any W_4b8cc = Some (Branch BC_NE (@BV 5 17%Z I) (@BV 5 0%Z I) (@BV 13 8164%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b8d0 : bv 32 := @BV 32 0xfff00513%Z I.
Lemma F_4b8d0 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b8d8%Z I : word) = Some W_4b8d0.
Proof. vm_refl. Qed.
Lemma D_4b8d0 : decode_any W_4b8d0 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b8d4 : bv 32 := @BV 32 0x02051513%Z I.
Lemma F_4b8d4 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b8dc%Z I : word) = Some W_4b8d4.
Proof. vm_refl. Qed.
Lemma D_4b8d4 : decode_any W_4b8d4 = Some (ShiftImm ALU_SLL (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b8d8 : bv 32 := @BV 32 0x00a93823%Z I.
Lemma F_4b8d8 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b8e0%Z I : word) = Some W_4b8d8.
Proof. vm_refl. Qed.
Lemma D_4b8d8 : decode_any W_4b8d8 = Some (Store SZ8 (@BV 5 18%Z I) (@BV 5 10%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b8dc : bv 32 := @BV 32 0x00194503%Z I.
Lemma F_4b8dc : fetch_word Asan.M.loaded_segments (@BV 64 0x4b8e4%Z I : word) = Some W_4b8dc.
Proof. vm_refl. Qed.
Lemma D_4b8dc : decode_any W_4b8dc = Some (Load SZ1 false (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b8e0 : bv 32 := @BV 32 0x00357593%Z I.
Lemma F_4b8e0 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b8e8%Z I : word) = Some W_4b8e0.
Proof. vm_refl. Qed.
Lemma D_4b8e0 : decode_any W_4b8e0 = Some (OpImm ALU_AND (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b8e4 : bv 32 := @BV 32 0x08ba1863%Z I.
Lemma F_4b8e4 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b8ec%Z I : word) = Some W_4b8e4.
Proof. vm_refl. Qed.
Lemma D_4b8e4 : decode_any W_4b8e4 = Some (Branch BC_NE (@BV 5 20%Z I) (@BV 5 11%Z I) (@BV 13 144%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b8e8 : bv 32 := @BV 32 0xffea7693%Z I.
Lemma F_4b8e8 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b8f0%Z I : word) = Some W_4b8e8.
Proof. vm_refl. Qed.
Lemma D_4b8e8 : decode_any W_4b8e8 = Some (OpImm ALU_AND (@BV 5 13%Z I) (@BV 5 20%Z I) (@BV 12 4094%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b8ec : bv 32 := @BV 32 0x00200713%Z I.
Lemma F_4b8ec : fetch_word Asan.M.loaded_segments (@BV 64 0x4b8f4%Z I : word) = Some W_4b8ec.
Proof. vm_refl. Qed.
Lemma D_4b8ec : decode_any W_4b8ec = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 12 2%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4b8f0 : bv 32 := @BV 32 0x14e69663%Z I.
Lemma F_4b8f0 : fetch_word Asan.M.loaded_segments (@BV 64 0x4b8f8%Z I : word) = Some W_4b8f0.
Proof. vm_refl. Qed.
Lemma D_4b8f0 : decode_any W_4b8f0 = Some (Branch BC_NE (@BV 5 13%Z I) (@BV 5 14%Z I) (@BV 13 332%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4ba3c : bv 32 := @BV 32 0x3452b0ef%Z I.
Lemma F_4ba3c : fetch_word Asan.M.loaded_segments (@BV 64 0x4ba44%Z I : word) = Some W_4ba3c.
Proof. vm_refl. Qed.
Lemma D_4ba3c : decode_any W_4ba3c = Some (Jal (@BV 5 1%Z I) (@BV 21 179012%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4ba40 : bv 32 := @BV 32 0xff24d583%Z I.
Lemma F_4ba40 : fetch_word Asan.M.loaded_segments (@BV 64 0x4ba48%Z I : word) = Some W_4ba40.
Proof. vm_refl. Qed.
Lemma D_4ba40 : decode_any W_4ba40 = Some (Load SZ2 false (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 12 4082%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4ba44 : bv 32 := @BV 32 0xff44e603%Z I.
Lemma F_4ba44 : fetch_word Asan.M.loaded_segments (@BV 64 0x4ba4c%Z I : word) = Some W_4ba44.
Proof. vm_refl. Qed.
Lemma D_4ba44 : decode_any W_4ba44 = Some (Load SZ4 false (@BV 5 12%Z I) (@BV 5 9%Z I) (@BV 12 4084%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4ba48 : bv 32 := @BV 32 0x02053683%Z I.
Lemma F_4ba48 : fetch_word Asan.M.loaded_segments (@BV 64 0x4ba50%Z I : word) = Some W_4ba48.
Proof. vm_refl. Qed.
Lemma D_4ba48 : decode_any W_4ba48 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 10%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4ba4c : bv 32 := @BV 32 0x01853703%Z I.
Lemma F_4ba4c : fetch_word Asan.M.loaded_segments (@BV 64 0x4ba54%Z I : word) = Some W_4ba4c.
Proof. vm_refl. Qed.
Lemma D_4ba4c : decode_any W_4ba4c = Some (Load SZ8 true (@BV 5 14%Z I) (@BV 5 10%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4ba50 : bv 32 := @BV 32 0x02059593%Z I.
Lemma F_4ba50 : fetch_word Asan.M.loaded_segments (@BV 64 0x4ba58%Z I : word) = Some W_4ba50.
Proof. vm_refl. Qed.
Lemma D_4ba50 : decode_any W_4ba50 = Some (ShiftImm ALU_SLL (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4ba54 : bv 32 := @BV 32 0x00c5e5b3%Z I.
Lemma F_4ba54 : fetch_word Asan.M.loaded_segments (@BV 64 0x4ba5c%Z I : word) = Some W_4ba54.
Proof. vm_refl. Qed.
Lemma D_4ba54 : decode_any W_4ba54 = Some (Op ALU_OR (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4ba58 : bv 32 := @BV 32 0x00d585b3%Z I.
Lemma F_4ba58 : fetch_word Asan.M.loaded_segments (@BV 64 0x4ba60%Z I : word) = Some W_4ba58.
Proof. vm_refl. Qed.
Lemma D_4ba58 : decode_any W_4ba58 = Some (Op ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 13%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4ba5c : bv 32 := @BV 32 0x00170713%Z I.
Lemma F_4ba5c : fetch_word Asan.M.loaded_segments (@BV 64 0x4ba64%Z I : word) = Some W_4ba5c.
Proof. vm_refl. Qed.
Lemma D_4ba5c : decode_any W_4ba5c = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4ba60 : bv 32 := @BV 32 0x00e53c23%Z I.
Lemma F_4ba60 : fetch_word Asan.M.loaded_segments (@BV 64 0x4ba68%Z I : word) = Some W_4ba60.
Proof. vm_refl. Qed.
Lemma D_4ba60 : decode_any W_4ba60 = Some (Store SZ8 (@BV 5 10%Z I) (@BV 5 14%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4ba64 : bv 32 := @BV 32 0x02b53023%Z I.
Lemma F_4ba64 : fetch_word Asan.M.loaded_segments (@BV 64 0x4ba6c%Z I : word) = Some W_4ba64.
Proof. vm_refl. Qed.
Lemma D_4ba64 : decode_any W_4ba64 = Some (Store SZ8 (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4ba68 : bv 32 := @BV 32 0x00098513%Z I.
Lemma F_4ba68 : fetch_word Asan.M.loaded_segments (@BV 64 0x4ba70%Z I : word) = Some W_4ba68.
Proof. vm_refl. Qed.
Lemma D_4ba68 : decode_any W_4ba68 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4ba6c : bv 32 := @BV 32 0x00090593%Z I.
Lemma F_4ba6c : fetch_word Asan.M.loaded_segments (@BV 64 0x4ba74%Z I : word) = Some W_4ba6c.
Proof. vm_refl. Qed.
Lemma D_4ba6c : decode_any W_4ba6c = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4ba70 : bv 32 := @BV 32 0x00048613%Z I.
Lemma F_4ba70 : fetch_word Asan.M.loaded_segments (@BV 64 0x4ba78%Z I : word) = Some W_4ba70.
Proof. vm_refl. Qed.
Lemma D_4ba70 : decode_any W_4ba70 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4ba74 : bv 32 := @BV 32 0x00040693%Z I.
Lemma F_4ba74 : fetch_word Asan.M.loaded_segments (@BV 64 0x4ba7c%Z I : word) = Some W_4ba74.
Proof. vm_refl. Qed.
Lemma D_4ba74 : decode_any W_4ba74 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4ba78 : bv 32 := @BV 32 0x03813083%Z I.
Lemma F_4ba78 : fetch_word Asan.M.loaded_segments (@BV 64 0x4ba80%Z I : word) = Some W_4ba78.
Proof. vm_refl. Qed.
Lemma D_4ba78 : decode_any W_4ba78 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4ba7c : bv 32 := @BV 32 0x03013403%Z I.
Lemma F_4ba7c : fetch_word Asan.M.loaded_segments (@BV 64 0x4ba84%Z I : word) = Some W_4ba7c.
Proof. vm_refl. Qed.
Lemma D_4ba7c : decode_any W_4ba7c = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4ba80 : bv 32 := @BV 32 0x02813483%Z I.
Lemma F_4ba80 : fetch_word Asan.M.loaded_segments (@BV 64 0x4ba88%Z I : word) = Some W_4ba80.
Proof. vm_refl. Qed.
Lemma D_4ba80 : decode_any W_4ba80 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4ba84 : bv 32 := @BV 32 0x02013903%Z I.
Lemma F_4ba84 : fetch_word Asan.M.loaded_segments (@BV 64 0x4ba8c%Z I : word) = Some W_4ba84.
Proof. vm_refl. Qed.
Lemma D_4ba84 : decode_any W_4ba84 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4ba88 : bv 32 := @BV 32 0x01813983%Z I.
Lemma F_4ba88 : fetch_word Asan.M.loaded_segments (@BV 64 0x4ba90%Z I : word) = Some W_4ba88.
Proof. vm_refl. Qed.
Lemma D_4ba88 : decode_any W_4ba88 = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4ba8c : bv 32 := @BV 32 0x01013a03%Z I.
Lemma F_4ba8c : fetch_word Asan.M.loaded_segments (@BV 64 0x4ba94%Z I : word) = Some W_4ba8c.
Proof. vm_refl. Qed.
Lemma D_4ba8c : decode_any W_4ba8c = Some (Load SZ8 true (@BV 5 20%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4ba90 : bv 32 := @BV 32 0x00813a83%Z I.
Lemma F_4ba90 : fetch_word Asan.M.loaded_segments (@BV 64 0x4ba98%Z I : word) = Some W_4ba90.
Proof. vm_refl. Qed.
Lemma D_4ba90 : decode_any W_4ba90 = Some (Load SZ8 true (@BV 5 21%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4ba94 : bv 32 := @BV 32 0x00013b03%Z I.
Lemma F_4ba94 : fetch_word Asan.M.loaded_segments (@BV 64 0x4ba9c%Z I : word) = Some W_4ba94.
Proof. vm_refl. Qed.
Lemma D_4ba94 : decode_any W_4ba94 = Some (Load SZ8 true (@BV 5 22%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4ba98 : bv 32 := @BV 32 0x04010113%Z I.
Lemma F_4ba98 : fetch_word Asan.M.loaded_segments (@BV 64 0x4baa0%Z I : word) = Some W_4ba98.
Proof. vm_refl. Qed.
Lemma D_4ba98 : decode_any W_4ba98 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4ba9c : bv 32 := @BV 32 0x2cc0406f%Z I.
Lemma F_4ba9c : fetch_word Asan.M.loaded_segments (@BV 64 0x4baa4%Z I : word) = Some W_4ba9c.
Proof. vm_refl. Qed.
Lemma D_4ba9c : decode_any W_4ba9c = Some (Jal (@BV 5 0%Z I) (@BV 21 17100%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bac0 : bv 32 := @BV 32 0xff010113%Z I.

Lemma D_4bac0 : decode_any W_4bac0 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4080%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bac4 : bv 32 := @BV 32 0x00113423%Z I.

Lemma D_4bac4 : decode_any W_4bac4 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bac8 : bv 32 := @BV 32 0x00813023%Z I.

Lemma D_4bac8 : decode_any W_4bac8 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bacc : bv 32 := @BV 32 0x00058693%Z I.

Lemma D_4bacc : decode_any W_4bacc = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bad0 : bv 32 := @BV 32 0x00050593%Z I.

Lemma D_4bad0 : decode_any W_4bad0 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bad4 : bv 32 := @BV 32 0x000b8517%Z I.
Lemma F_4bad4 : fetch_word Asan.M.loaded_segments (@BV 64 0x4badc%Z I : word) = Some W_4bad4.
Proof. vm_refl. Qed.
Lemma D_4bad4 : decode_any W_4bad4 = Some (Auipc (@BV 5 10%Z I) (@BV 20 184%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bad8 : bv 32 := @BV 32 0x00800613%Z I.

Lemma D_4bad8 : decode_any W_4bad8 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4badc : bv 32 := @BV 32 0x00100713%Z I.

Lemma D_4badc : decode_any W_4badc = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bae0 : bv 32 := @BV 32 0x43c50513%Z I.
Lemma F_4bae0 : fetch_word Asan.M.loaded_segments (@BV 64 0x4bae8%Z I : word) = Some W_4bae0.
Proof. vm_refl. Qed.
Lemma D_4bae0 : decode_any W_4bae0 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 1084%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bae4 : bv 32 := @BV 32 0x00100793%Z I.

Lemma D_4bae4 : decode_any W_4bae4 = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bae8 : bv 32 := @BV 32 0x034000ef%Z I.

Lemma D_4bae8 : decode_any W_4bae8 = Some (Jal (@BV 5 1%Z I) (@BV 21 52%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4baec : bv 32 := @BV 32 0x00050a63%Z I.
Lemma F_4baec : fetch_word Asan.M.loaded_segments (@BV 64 0x4baf4%Z I : word) = Some W_4baec.
Proof. vm_refl. Qed.
Lemma D_4baec : decode_any W_4baec = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4baf0 : bv 32 := @BV 32 0x00813083%Z I.

Lemma D_4baf0 : decode_any W_4baf0 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4baf4 : bv 32 := @BV 32 0x00013403%Z I.

Lemma D_4baf4 : decode_any W_4baf4 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4baf8 : bv 32 := @BV 32 0x01010113%Z I.

Lemma D_4baf8 : decode_any W_4baf8 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bafc : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_4bafc : decode_any W_4bafc = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb00 : bv 32 := @BV 32 0x00050413%Z I.
Lemma F_4bb00 : fetch_word Asan.M.loaded_segments (@BV 64 0x4bb08%Z I : word) = Some W_4bb00.
Proof. vm_refl. Qed.
Lemma D_4bb00 : decode_any W_4bb00 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb04 : bv 32 := @BV 32 0x50d3c0ef%Z I.
Lemma F_4bb04 : fetch_word Asan.M.loaded_segments (@BV 64 0x4bb0c%Z I : word) = Some W_4bb04.
Proof. vm_refl. Qed.
Lemma D_4bb04 : decode_any W_4bb04 = Some (Jal (@BV 5 1%Z I) (@BV 21 249100%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb08 : bv 32 := @BV 32 0x00040513%Z I.
Lemma F_4bb08 : fetch_word Asan.M.loaded_segments (@BV 64 0x4bb10%Z I : word) = Some W_4bb08.
Proof. vm_refl. Qed.
Lemma D_4bb08 : decode_any W_4bb08 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb0c : bv 32 := @BV 32 0x00813083%Z I.
Lemma F_4bb0c : fetch_word Asan.M.loaded_segments (@BV 64 0x4bb14%Z I : word) = Some W_4bb0c.
Proof. vm_refl. Qed.
Lemma D_4bb0c : decode_any W_4bb0c = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb10 : bv 32 := @BV 32 0x00013403%Z I.
Lemma F_4bb10 : fetch_word Asan.M.loaded_segments (@BV 64 0x4bb18%Z I : word) = Some W_4bb10.
Proof. vm_refl. Qed.
Lemma D_4bb10 : decode_any W_4bb10 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb14 : bv 32 := @BV 32 0x01010113%Z I.
Lemma F_4bb14 : fetch_word Asan.M.loaded_segments (@BV 64 0x4bb1c%Z I : word) = Some W_4bb14.
Proof. vm_refl. Qed.
Lemma D_4bb14 : decode_any W_4bb14 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb18 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_4bb18 : fetch_word Asan.M.loaded_segments (@BV 64 0x4bb20%Z I : word) = Some W_4bb18.
Proof. vm_refl. Qed.
Lemma D_4bb18 : decode_any W_4bb18 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb1c : bv 32 := @BV 32 0xf8010113%Z I.

Lemma D_4bb1c : decode_any W_4bb1c = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 3968%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb20 : bv 32 := @BV 32 0x06113c23%Z I.

Lemma D_4bb20 : decode_any W_4bb20 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 120%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb24 : bv 32 := @BV 32 0x06813823%Z I.

Lemma D_4bb24 : decode_any W_4bb24 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 112%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb28 : bv 32 := @BV 32 0x06913423%Z I.

Lemma D_4bb28 : decode_any W_4bb28 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 104%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb2c : bv 32 := @BV 32 0x07213023%Z I.

Lemma D_4bb2c : decode_any W_4bb2c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 96%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb30 : bv 32 := @BV 32 0x05313c23%Z I.

Lemma D_4bb30 : decode_any W_4bb30 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 19%Z I) (@BV 12 88%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb34 : bv 32 := @BV 32 0x05413823%Z I.

Lemma D_4bb34 : decode_any W_4bb34 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 20%Z I) (@BV 12 80%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb38 : bv 32 := @BV 32 0x05513423%Z I.

Lemma D_4bb38 : decode_any W_4bb38 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 21%Z I) (@BV 12 72%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb3c : bv 32 := @BV 32 0x05613023%Z I.

Lemma D_4bb3c : decode_any W_4bb3c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 22%Z I) (@BV 12 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb40 : bv 32 := @BV 32 0x03713c23%Z I.

Lemma D_4bb40 : decode_any W_4bb40 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 23%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb44 : bv 32 := @BV 32 0x03813823%Z I.

Lemma D_4bb44 : decode_any W_4bb44 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 24%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb48 : bv 32 := @BV 32 0x03913423%Z I.

Lemma D_4bb48 : decode_any W_4bb48 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 25%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb4c : bv 32 := @BV 32 0x03a13023%Z I.

Lemma D_4bb4c : decode_any W_4bb4c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 26%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb50 : bv 32 := @BV 32 0x01b13c23%Z I.

Lemma D_4bb50 : decode_any W_4bb50 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 27%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb54 : bv 32 := @BV 32 0x00078493%Z I.

Lemma D_4bb54 : decode_any W_4bb54 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 15%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb58 : bv 32 := @BV 32 0x00070d93%Z I.

Lemma D_4bb58 : decode_any W_4bb58 = Some (OpImm ALU_ADD (@BV 5 27%Z I) (@BV 5 14%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb5c : bv 32 := @BV 32 0x00068b93%Z I.

Lemma D_4bb5c : decode_any W_4bb5c = Some (OpImm ALU_ADD (@BV 5 23%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb60 : bv 32 := @BV 32 0x00060913%Z I.

Lemma D_4bb60 : decode_any W_4bb60 = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb64 : bv 32 := @BV 32 0x00058a93%Z I.

Lemma D_4bb64 : decode_any W_4bb64 = Some (OpImm ALU_ADD (@BV 5 21%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb68 : bv 32 := @BV 32 0x00050b13%Z I.

Lemma D_4bb68 : decode_any W_4bb68 = Some (OpImm ALU_ADD (@BV 5 22%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb6c : bv 32 := @BV 32 0x138290ef%Z I.

Lemma D_4bb6c : decode_any W_4bb6c = Some (Jal (@BV 5 1%Z I) (@BV 21 168248%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb70 : bv 32 := @BV 32 0x7e050463%Z I.

Lemma D_4bb70 : decode_any W_4bb70 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 2024%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb74 : bv 32 := @BV 32 0x5f92e0ef%Z I.

Lemma D_4bb74 : decode_any W_4bb74 = Some (Jal (@BV 5 1%Z I) (@BV 21 191992%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb78 : bv 32 := @BV 32 0x7e051663%Z I.

Lemma D_4bb78 : decode_any W_4bb78 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 2028%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb7c : bv 32 := @BV 32 0x080b86e3%Z I.

Lemma D_4bb7c : decode_any W_4bb7c = Some (Branch BC_EQ (@BV 5 23%Z I) (@BV 5 0%Z I) (@BV 13 2188%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb80 : bv 32 := @BV 32 0x00800513%Z I.

Lemma D_4bb80 : decode_any W_4bb80 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb84 : bv 32 := @BV 32 0x02a97e63%Z I.

Lemma D_4bb84 : decode_any W_4bb84 = Some (Branch BC_GEU (@BV 5 18%Z I) (@BV 5 10%Z I) (@BV 13 60%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb88 : bv 32 := @BV 32 0x00000593%Z I.



(* [comment removed for export] *)
Definition W_4bb8c : bv 32 := @BV 32 0x00090413%Z I.



(* [comment removed for export] *)
Definition W_4bb90 : bv 32 := @BV 32 0x01256463%Z I.



(* [comment removed for export] *)
Definition W_4bb94 : bv 32 := @BV 32 0x00800413%Z I.

Lemma D_4bb94 : decode_any W_4bb94 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 0%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb98 : bv 32 := @BV 32 0xfff40c93%Z I.

Lemma D_4bb98 : decode_any W_4bb98 = Some (OpImm ALU_ADD (@BV 5 25%Z I) (@BV 5 8%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bb9c : bv 32 := @BV 32 0x01947533%Z I.

Lemma D_4bb9c : decode_any W_4bb9c = Some (Op ALU_AND (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 5 25%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bba0 : bv 32 := @BV 32 0x7c051a63%Z I.

Lemma D_4bba0 : decode_any W_4bba0 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 2004%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bba4 : bv 32 := @BV 32 0x03100513%Z I.

Lemma D_4bba4 : decode_any W_4bba4 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 49%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bba8 : bv 32 := @BV 32 0x7ffb0d13%Z I.

Lemma D_4bba8 : decode_any W_4bba8 = Some (OpImm ALU_ADD (@BV 5 26%Z I) (@BV 5 22%Z I) (@BV 12 2047%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bbac : bv 32 := @BV 32 0x00913423%Z I.

Lemma D_4bbac : decode_any W_4bbac = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bbb0 : bv 32 := @BV 32 0x00b13823%Z I.

Lemma D_4bbb0 : decode_any W_4bbb0 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 11%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bbb4 : bv 32 := @BV 32 0x06aaf463%Z I.

Lemma D_4bbb4 : decode_any W_4bbb4 = Some (Branch BC_GEU (@BV 5 21%Z I) (@BV 5 10%Z I) (@BV 13 104%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bbb8 : bv 32 := @BV 32 0x00000993%Z I.

Lemma D_4bbb8 : decode_any W_4bbb8 = Some (OpImm ALU_ADD (@BV 5 19%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bbbc : bv 32 := @BV 32 0x0cc0006f%Z I.

Lemma D_4bbbc : decode_any W_4bbbc = Some (Jal (@BV 5 0%Z I) (@BV 21 204%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bbc0 : bv 32 := @BV 32 0x20000613%Z I.

Lemma D_4bbc0 : decode_any W_4bbc0 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 512%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bbc4 : bv 32 := @BV 32 0x00090593%Z I.

Lemma D_4bbc4 : decode_any W_4bbc4 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bbc8 : bv 32 := @BV 32 0x00c96463%Z I.

Lemma D_4bbc8 : decode_any W_4bbc8 = Some (Branch BC_LTU (@BV 5 18%Z I) (@BV 5 12%Z I) (@BV 13 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bbcc : bv 32 := @BV 32 0x20000593%Z I.



(* [comment removed for export] *)
Definition W_4bbd0 : bv 32 := @BV 32 0xfff58613%Z I.

Lemma D_4bbd0 : decode_any W_4bbd0 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bbd4 : bv 32 := @BV 32 0x00c5f633%Z I.

Lemma D_4bbd4 : decode_any W_4bbd4 = Some (Op ALU_AND (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bbd8 : bv 32 := @BV 32 0x040618e3%Z I.

Lemma D_4bbd8 : decode_any W_4bbd8 = Some (Branch BC_NE (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 13 2128%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bbdc : bv 32 := @BV 32 0xfffc5617%Z I.
Lemma F_4bbdc : fetch_word Asan.M.loaded_segments (@BV 64 0x4bbe4%Z I : word) = Some W_4bbdc.
Proof. vm_refl. Qed.
Lemma D_4bbdc : decode_any W_4bbdc = Some (Auipc (@BV 5 12%Z I) (@BV 20 1048517%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bbe0 : bv 32 := @BV 32 0x8ac63603%Z I.
Lemma F_4bbe0 : fetch_word Asan.M.loaded_segments (@BV 64 0x4bbe8%Z I : word) = Some W_4bbe0.
Proof. vm_refl. Qed.
Lemma D_4bbe0 : decode_any W_4bbe0 = Some (Load SZ8 true (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 2220%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bbe4 : bv 32 := @BV 32 0x40b006b3%Z I.

Lemma D_4bbe4 : decode_any W_4bbe4 = Some (Op ALU_SUB (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bbe8 : bv 32 := @BV 32 0x00d5f5b3%Z I.

Lemma D_4bbe8 : decode_any W_4bbe8 = Some (Op ALU_AND (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 13%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bbec : bv 32 := @BV 32 0x02c585b3%Z I.

Lemma D_4bbec : decode_any W_4bbec = Some (Mul M_MUL (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bbf0 : bv 32 := @BV 32 0xfffc5617%Z I.
Lemma F_4bbf0 : fetch_word Asan.M.loaded_segments (@BV 64 0x4bbf8%Z I : word) = Some W_4bbf0.
Proof. vm_refl. Qed.
Lemma D_4bbf0 : decode_any W_4bbf0 = Some (Auipc (@BV 5 12%Z I) (@BV 20 1048517%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bbf4 : bv 32 := @BV 32 0x03a5d593%Z I.

Lemma D_4bbf4 : decode_any W_4bbf4 = Some (ShiftImm ALU_SRL (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 6 58%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bbf8 : bv 32 := @BV 32 0x90860613%Z I.
Lemma F_4bbf8 : fetch_word Asan.M.loaded_segments (@BV 64 0x4bc00%Z I : word) = Some W_4bbf8.
Proof. vm_refl. Qed.
Lemma D_4bbf8 : decode_any W_4bbf8 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 2312%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bbfc : bv 32 := @BV 32 0x00b605b3%Z I.

Lemma D_4bbfc : decode_any W_4bbfc = Some (Op ALU_ADD (@BV 5 11%Z I) (@BV 5 12%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc00 : bv 32 := @BV 32 0x0005c583%Z I.

Lemma D_4bc00 : decode_any W_4bc00 = Some (Load SZ1 false (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc04 : bv 32 := @BV 32 0x00459593%Z I.

Lemma D_4bc04 : decode_any W_4bc04 = Some (ShiftImm ALU_SLL (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 6 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc08 : bv 32 := @BV 32 0x06058593%Z I.

Lemma D_4bc08 : decode_any W_4bc08 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 96%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc0c : bv 32 := @BV 32 0x0705f593%Z I.

Lemma D_4bc0c : decode_any W_4bc0c = Some (OpImm ALU_AND (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 112%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc10 : bv 32 := @BV 32 0x00090413%Z I.

Lemma D_4bc10 : decode_any W_4bc10 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc14 : bv 32 := @BV 32 0xf92570e3%Z I.

Lemma D_4bc14 : decode_any W_4bc14 = Some (Branch BC_GEU (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 13 8064%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc18 : bv 32 := @BV 32 0xf81ff06f%Z I.



(* [comment removed for export] *)
Definition W_4bc1c : bv 32 := @BV 32 0x06100513%Z I.

Lemma D_4bc1c : decode_any W_4bc1c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 97%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc20 : bv 32 := @BV 32 0x00aaf663%Z I.

Lemma D_4bc20 : decode_any W_4bc20 = Some (Branch BC_GEU (@BV 5 21%Z I) (@BV 5 10%Z I) (@BV 13 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc24 : bv 32 := @BV 32 0x00100993%Z I.

Lemma D_4bc24 : decode_any W_4bc24 = Some (OpImm ALU_ADD (@BV 5 19%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc28 : bv 32 := @BV 32 0x0600006f%Z I.

Lemma D_4bc28 : decode_any W_4bc28 = Some (Jal (@BV 5 0%Z I) (@BV 21 96%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc2c : bv 32 := @BV 32 0x1c100513%Z I.

Lemma D_4bc2c : decode_any W_4bc2c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 449%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc30 : bv 32 := @BV 32 0x00aaf663%Z I.

Lemma D_4bc30 : decode_any W_4bc30 = Some (Branch BC_GEU (@BV 5 21%Z I) (@BV 5 10%Z I) (@BV 13 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc34 : bv 32 := @BV 32 0x00200993%Z I.

Lemma D_4bc34 : decode_any W_4bc34 = Some (OpImm ALU_ADD (@BV 5 19%Z I) (@BV 5 0%Z I) (@BV 12 2%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc38 : bv 32 := @BV 32 0x0500006f%Z I.

Lemma D_4bc38 : decode_any W_4bc38 = Some (Jal (@BV 5 0%Z I) (@BV 21 80%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc3c : bv 32 := @BV 32 0x00001537%Z I.

Lemma D_4bc3c : decode_any W_4bc3c = Some (Lui (@BV 5 10%Z I) (@BV 20 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc40 : bv 32 := @BV 32 0xf815051b%Z I.

Lemma D_4bc40 : decode_any W_4bc40 = Some (OpImm32 (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 3969%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc44 : bv 32 := @BV 32 0x00aaf663%Z I.

Lemma D_4bc44 : decode_any W_4bc44 = Some (Branch BC_GEU (@BV 5 21%Z I) (@BV 5 10%Z I) (@BV 13 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc48 : bv 32 := @BV 32 0x00300993%Z I.

Lemma D_4bc48 : decode_any W_4bc48 = Some (OpImm ALU_ADD (@BV 5 19%Z I) (@BV 5 0%Z I) (@BV 12 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc4c : bv 32 := @BV 32 0x03c0006f%Z I.

Lemma D_4bc4c : decode_any W_4bc4c = Some (Jal (@BV 5 0%Z I) (@BV 21 60%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc50 : bv 32 := @BV 32 0x00004537%Z I.

Lemma D_4bc50 : decode_any W_4bc50 = Some (Lui (@BV 5 10%Z I) (@BV 20 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc54 : bv 32 := @BV 32 0xf015051b%Z I.

Lemma D_4bc54 : decode_any W_4bc54 = Some (OpImm32 (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 3841%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc58 : bv 32 := @BV 32 0x00aaf663%Z I.

Lemma D_4bc58 : decode_any W_4bc58 = Some (Branch BC_GEU (@BV 5 21%Z I) (@BV 5 10%Z I) (@BV 13 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc5c : bv 32 := @BV 32 0x00400993%Z I.

Lemma D_4bc5c : decode_any W_4bc5c = Some (OpImm ALU_ADD (@BV 5 19%Z I) (@BV 5 0%Z I) (@BV 12 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc60 : bv 32 := @BV 32 0x0280006f%Z I.

Lemma D_4bc60 : decode_any W_4bc60 = Some (Jal (@BV 5 0%Z I) (@BV 21 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc64 : bv 32 := @BV 32 0x00008537%Z I.

Lemma D_4bc64 : decode_any W_4bc64 = Some (Lui (@BV 5 10%Z I) (@BV 20 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc68 : bv 32 := @BV 32 0xe015051b%Z I.

Lemma D_4bc68 : decode_any W_4bc68 = Some (OpImm32 (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 3585%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc6c : bv 32 := @BV 32 0x00aaf663%Z I.

Lemma D_4bc6c : decode_any W_4bc6c = Some (Branch BC_GEU (@BV 5 21%Z I) (@BV 5 10%Z I) (@BV 13 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc70 : bv 32 := @BV 32 0x00500993%Z I.

Lemma D_4bc70 : decode_any W_4bc70 = Some (OpImm ALU_ADD (@BV 5 19%Z I) (@BV 5 0%Z I) (@BV 12 5%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc74 : bv 32 := @BV 32 0x0140006f%Z I.

Lemma D_4bc74 : decode_any W_4bc74 = Some (Jal (@BV 5 0%Z I) (@BV 21 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc78 : bv 32 := @BV 32 0x00010537%Z I.

Lemma D_4bc78 : decode_any W_4bc78 = Some (Lui (@BV 5 10%Z I) (@BV 20 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc7c : bv 32 := @BV 32 0xc015051b%Z I.

Lemma D_4bc7c : decode_any W_4bc7c = Some (OpImm32 (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 3073%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc80 : bv 32 := @BV 32 0x00aab533%Z I.

Lemma D_4bc80 : decode_any W_4bc80 = Some (Op ALU_SLTU (@BV 5 10%Z I) (@BV 5 21%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc84 : bv 32 := @BV 32 0x00754993%Z I.

Lemma D_4bc84 : decode_any W_4bc84 = Some (OpImm ALU_XOR (@BV 5 19%Z I) (@BV 5 10%Z I) (@BV 12 7%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc88 : bv 32 := @BV 32 0x629d1503%Z I.

Lemma D_4bc88 : decode_any W_4bc88 = Some (Load SZ2 true (@BV 5 10%Z I) (@BV 5 26%Z I) (@BV 12 1577%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc8c : bv 32 := @BV 32 0x0230000f%Z I.

Lemma D_4bc8c : decode_any W_4bc8c = Some (Fence (@BV 4 0%Z I) (@BV 4 2%Z I) (@BV 4 3%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc90 : bv 32 := @BV 32 0x00010a37%Z I.

Lemma D_4bc90 : decode_any W_4bc90 = Some (Lui (@BV 5 20%Z I) (@BV 20 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc94 : bv 32 := @BV 32 0xfffa0c1b%Z I.

Lemma D_4bc94 : decode_any W_4bc94 = Some (OpImm32 (@BV 5 24%Z I) (@BV 5 20%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc98 : bv 32 := @BV 32 0x01857533%Z I.

Lemma D_4bc98 : decode_any W_4bc98 = Some (Op ALU_AND (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 5 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bc9c : bv 32 := @BV 32 0x4a0050ef%Z I.

Lemma D_4bc9c : decode_any W_4bc9c = Some (Jal (@BV 5 1%Z I) (@BV 21 21664%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bca0 : bv 32 := @BV 32 0x00050493%Z I.

Lemma D_4bca0 : decode_any W_4bca0 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bca4 : bv 32 := @BV 32 0x62bd1503%Z I.

Lemma D_4bca4 : decode_any W_4bca4 = Some (Load SZ2 true (@BV 5 10%Z I) (@BV 5 26%Z I) (@BV 12 1579%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bca8 : bv 32 := @BV 32 0x0230000f%Z I.

Lemma D_4bca8 : decode_any W_4bca8 = Some (Fence (@BV 4 0%Z I) (@BV 4 2%Z I) (@BV 4 3%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bcac : bv 32 := @BV 32 0x01857533%Z I.

Lemma D_4bcac : decode_any W_4bcac = Some (Op ALU_AND (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 5 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bcb0 : bv 32 := @BV 32 0x48c050ef%Z I.

Lemma D_4bcb0 : decode_any W_4bcb0 = Some (Jal (@BV 5 1%Z I) (@BV 21 21644%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bcb4 : bv 32 := @BV 32 0x0b34e663%Z I.

Lemma D_4bcb4 : decode_any W_4bcb4 = Some (Branch BC_LTU (@BV 5 9%Z I) (@BV 5 19%Z I) (@BV 13 172%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bcb8 : bv 32 := @BV 32 0x00048993%Z I.

Lemma D_4bcb8 : decode_any W_4bcb8 = Some (OpImm ALU_ADD (@BV 5 19%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bcbc : bv 32 := @BV 32 0x0aa4f463%Z I.

Lemma D_4bcbc : decode_any W_4bcbc = Some (Branch BC_GEU (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 13 168%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bcc0 : bv 32 := @BV 32 0x00800593%Z I.

Lemma D_4bcc0 : decode_any W_4bcc0 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bcc4 : bv 32 := @BV 32 0x000a8513%Z I.

Lemma D_4bcc4 : decode_any W_4bcc4 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 21%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bcc8 : bv 32 := @BV 32 0x0155e463%Z I.

Lemma D_4bcc8 : decode_any W_4bcc8 = Some (Branch BC_LTU (@BV 5 11%Z I) (@BV 5 21%Z I) (@BV 13 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bccc : bv 32 := @BV 32 0x00800513%Z I.

Lemma D_4bccc : decode_any W_4bccc = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bcd0 : bv 32 := @BV 32 0x00850533%Z I.

Lemma D_4bcd0 : decode_any W_4bcd0 = Some (Op ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 5 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bcd4 : bv 32 := @BV 32 0x40800c33%Z I.

Lemma D_4bcd4 : decode_any W_4bcd4 = Some (Op ALU_SUB (@BV 5 24%Z I) (@BV 5 0%Z I) (@BV 5 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bcd8 : bv 32 := @BV 32 0x00993593%Z I.

Lemma D_4bcd8 : decode_any W_4bcd8 = Some (OpImm ALU_SLTU (@BV 5 11%Z I) (@BV 5 18%Z I) (@BV 12 9%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bcdc : bv 32 := @BV 32 0xfff50513%Z I.

Lemma D_4bcdc : decode_any W_4bcdc = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bce0 : bv 32 := @BV 32 0xfff58593%Z I.

Lemma D_4bce0 : decode_any W_4bce0 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bce4 : bv 32 := @BV 32 0x01857533%Z I.

Lemma D_4bce4 : decode_any W_4bce4 = Some (Op ALU_AND (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 5 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bce8 : bv 32 := @BV 32 0x0085f5b3%Z I.

Lemma D_4bce8 : decode_any W_4bce8 = Some (Op ALU_AND (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bcec : bv 32 := @BV 32 0x00b50533%Z I.

Lemma D_4bcec : decode_any W_4bcec = Some (Op ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bcf0 : bv 32 := @BV 32 0x00757593%Z I.

Lemma D_4bcf0 : decode_any W_4bcf0 = Some (OpImm ALU_AND (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 7%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bcf4 : bv 32 := @BV 32 0x6a059063%Z I.

Lemma D_4bcf4 : decode_any W_4bcf4 = Some (Branch BC_NE (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 1696%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bcf8 : bv 32 := @BV 32 0x01000593%Z I.

Lemma D_4bcf8 : decode_any W_4bcf8 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bcfc : bv 32 := @BV 32 0x001ab493%Z I.

Lemma D_4bcfc : decode_any W_4bcfc = Some (OpImm ALU_SLTU (@BV 5 9%Z I) (@BV 5 21%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bd00 : bv 32 := @BV 32 0x001a061b%Z I.

Lemma D_4bd00 : decode_any W_4bd00 = Some (OpImm32 (@BV 5 12%Z I) (@BV 5 20%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bd04 : bv 32 := @BV 32 0x01359a3b%Z I.

Lemma D_4bd04 : decode_any W_4bd04 = Some (Op32 ALU_SLL (@BV 5 20%Z I) (@BV 5 11%Z I) (@BV 5 19%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bd08 : bv 32 := @BV 32 0x00100593%Z I.

Lemma D_4bd08 : decode_any W_4bd08 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bd0c : bv 32 := @BV 32 0x009a84b3%Z I.

Lemma D_4bd0c : decode_any W_4bd0c = Some (Op ALU_ADD (@BV 5 9%Z I) (@BV 5 21%Z I) (@BV 5 9%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bd10 : bv 32 := @BV 32 0x00c936b3%Z I.

Lemma D_4bd10 : decode_any W_4bd10 = Some (Op ALU_SLTU (@BV 5 13%Z I) (@BV 5 18%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bd14 : bv 32 := @BV 32 0x014509b3%Z I.

Lemma D_4bd14 : decode_any W_4bd14 = Some (Op ALU_ADD (@BV 5 19%Z I) (@BV 5 10%Z I) (@BV 5 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bd18 : bv 32 := @BV 32 0x00c9b433%Z I.

Lemma D_4bd18 : decode_any W_4bd18 = Some (Op ALU_SLTU (@BV 5 8%Z I) (@BV 5 19%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bd1c : bv 32 := @BV 32 0x0086f433%Z I.

Lemma D_4bd1c : decode_any W_4bd1c = Some (Op ALU_AND (@BV 5 8%Z I) (@BV 5 13%Z I) (@BV 5 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bd20 : bv 32 := @BV 32 0xfff40513%Z I.

Lemma D_4bd20 : decode_any W_4bd20 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bd24 : bv 32 := @BV 32 0x01457633%Z I.

Lemma D_4bd24 : decode_any W_4bd24 = Some (Op ALU_AND (@BV 5 12%Z I) (@BV 5 10%Z I) (@BV 5 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bd28 : bv 32 := @BV 32 0x02859513%Z I.

Lemma D_4bd28 : decode_any W_4bd28 = Some (ShiftImm ALU_SLL (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 6 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bd2c : bv 32 := @BV 32 0x013609b3%Z I.

Lemma D_4bd2c : decode_any W_4bd2c = Some (Op ALU_ADD (@BV 5 19%Z I) (@BV 5 12%Z I) (@BV 5 19%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bd30 : bv 32 := @BV 32 0x01556863%Z I.

Lemma D_4bd30 : decode_any W_4bd30 = Some (Branch BC_LTU (@BV 5 10%Z I) (@BV 5 21%Z I) (@BV 13 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bd34 : bv 32 := @BV 32 0x01356663%Z I.

Lemma D_4bd34 : decode_any W_4bd34 = Some (Branch BC_LTU (@BV 5 10%Z I) (@BV 5 19%Z I) (@BV 13 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bd38 : bv 32 := @BV 32 0x621d3503%Z I.

Lemma D_4bd38 : decode_any W_4bd38 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 26%Z I) (@BV 12 1569%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bd3c : bv 32 := @BV 32 0x06957063%Z I.

Lemma D_4bd3c : decode_any W_4bd3c = Some (Branch BC_GEU (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 13 96%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bd40 : bv 32 := @BV 32 0x4052e0ef%Z I.



(* [comment removed for export] *)
Definition W_4bd44 : bv 32 := @BV 32 0x02050a63%Z I.



(* [comment removed for export] *)
Definition W_4bd50 : bv 32 := @BV 32 0x00048593%Z I.



(* [comment removed for export] *)
Definition W_4bd54 : bv 32 := @BV 32 0x604370ef%Z I.



(* [comment removed for export] *)
Definition W_4bd58 : bv 32 := @BV 32 0x00000a13%Z I.



(* [comment removed for export] *)
Definition W_4bd5c : bv 32 := @BV 32 0x4f40006f%Z I.



(* [comment removed for export] *)
Definition W_4bd60 : bv 32 := @BV 32 0xf6a9e0e3%Z I.

Lemma D_4bd60 : decode_any W_4bd60 = Some (Branch BC_LTU (@BV 5 19%Z I) (@BV 5 10%Z I) (@BV 13 8032%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bd64 : bv 32 := @BV 32 0x00050993%Z I.

Lemma D_4bd64 : decode_any W_4bd64 = Some (OpImm ALU_ADD (@BV 5 19%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bd68 : bv 32 := @BV 32 0x00800593%Z I.

Lemma D_4bd68 : decode_any W_4bd68 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bd6c : bv 32 := @BV 32 0x000a8513%Z I.

Lemma D_4bd6c : decode_any W_4bd6c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 21%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bd70 : bv 32 := @BV 32 0xf555fee3%Z I.

Lemma D_4bd70 : decode_any W_4bd70 = Some (Branch BC_GEU (@BV 5 11%Z I) (@BV 5 21%Z I) (@BV 13 8028%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bd74 : bv 32 := @BV 32 0xf5dff06f%Z I.

Lemma D_4bd74 : decode_any W_4bd74 = Some (Jal (@BV 5 0%Z I) (@BV 21 2096988%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bd78 : bv 32 := @BV 32 0x621d3603%Z I.



(* [comment removed for export] *)
Definition W_4bd7c : bv 32 := @BV 32 0x00100513%Z I.



(* [comment removed for export] *)
Definition W_4bd80 : bv 32 := @BV 32 0x02851513%Z I.



(* [comment removed for export] *)
Definition W_4bd84 : bv 32 := @BV 32 0x00a66463%Z I.



(* [comment removed for export] *)
Definition W_4bd88 : bv 32 := @BV 32 0x00050613%Z I.



(* [comment removed for export] *)
Definition W_4bd8c : bv 32 := @BV 32 0x00048513%Z I.



(* [comment removed for export] *)
Definition W_4bd90 : bv 32 := @BV 32 0x00098593%Z I.



(* [comment removed for export] *)
Definition W_4bd94 : bv 32 := @BV 32 0x000b8693%Z I.



(* [comment removed for export] *)
Definition W_4bd98 : bv 32 := @BV 32 0x541260ef%Z I.



(* [comment removed for export] *)
Definition W_4bd9c : bv 32 := @BV 32 0x6182c0ef%Z I.

Lemma D_4bd9c : decode_any W_4bd9c = Some (Jal (@BV 5 1%Z I) (@BV 21 181784%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bda0 : bv 32 := @BV 32 0x00050d13%Z I.

Lemma D_4bda0 : decode_any W_4bda0 = Some (OpImm ALU_ADD (@BV 5 26%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bda4 : bv 32 := @BV 32 0x08050863%Z I.

Lemma D_4bda4 : decode_any W_4bda4 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 144%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bda8 : bv 32 := @BV 32 0x0d0d0593%Z I.

Lemma D_4bda8 : decode_any W_4bda8 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 26%Z I) (@BV 12 208%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bdac : bv 32 := @BV 32 0x00800693%Z I.

Lemma D_4bdac : decode_any W_4bdac = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bdb0 : bv 32 := @BV 32 0x000b0513%Z I.

Lemma D_4bdb0 : decode_any W_4bdb0 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 22%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bdb4 : bv 32 := @BV 32 0x00098613%Z I.

Lemma D_4bdb4 : decode_any W_4bdb4 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bdb8 : bv 32 := @BV 32 0x4bc040ef%Z I.

Lemma D_4bdb8 : decode_any W_4bdb8 = Some (Jal (@BV 5 1%Z I) (@BV 21 17596%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bdbc : bv 32 := @BV 32 0x00050913%Z I.
Lemma F_4bdbc : fetch_word Asan.M.loaded_segments (@BV 64 0x4bdc4%Z I : word) = Some W_4bdbc.
Proof. vm_refl. Qed.
Lemma D_4bdbc : decode_any W_4bdbc = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bdc0 : bv 32 := @BV 32 0x0c050663%Z I.
Lemma F_4bdc0 : fetch_word Asan.M.loaded_segments (@BV 64 0x4bdc8%Z I : word) = Some W_4bdc0.
Proof. vm_refl. Qed.
Lemma D_4bdc0 : decode_any W_4bdc0 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 204%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bdc4 : bv 32 := @BV 32 0x01490a33%Z I.

Lemma D_4bdc4 : decode_any W_4bdc4 = Some (Op ALU_ADD (@BV 5 20%Z I) (@BV 5 18%Z I) (@BV 5 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bdc8 : bv 32 := @BV 32 0x019a7533%Z I.

Lemma D_4bdc8 : decode_any W_4bdc8 = Some (Op ALU_AND (@BV 5 10%Z I) (@BV 5 20%Z I) (@BV 5 25%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bdcc : bv 32 := @BV 32 0x01298733%Z I.

Lemma D_4bdcc : decode_any W_4bdcc = Some (Op ALU_ADD (@BV 5 14%Z I) (@BV 5 19%Z I) (@BV 5 18%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bdd0 : bv 32 := @BV 32 0x00050663%Z I.

Lemma D_4bdd0 : decode_any W_4bdd0 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bdd4 : bv 32 := @BV 32 0x014c8a33%Z I.



(* [comment removed for export] *)
Definition W_4bdd8 : bv 32 := @BV 32 0x018a7a33%Z I.



(* [comment removed for export] *)
Definition W_4bddc : bv 32 := @BV 32 0x009a0cb3%Z I.

Lemma D_4bddc : decode_any W_4bddc = Some (Op ALU_ADD (@BV 5 25%Z I) (@BV 5 20%Z I) (@BV 5 9%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bde0 : bv 32 := @BV 32 0x5d976a63%Z I.

Lemma D_4bde0 : decode_any W_4bde0 = Some (Branch BC_LTU (@BV 5 14%Z I) (@BV 5 25%Z I) (@BV 13 1492%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bde4 : bv 32 := @BV 32 0xff1a4503%Z I.

Lemma D_4bde4 : decode_any W_4bde4 = Some (Load SZ1 false (@BV 5 10%Z I) (@BV 5 20%Z I) (@BV 12 4081%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bde8 : bv 32 := @BV 32 0x003df593%Z I.

Lemma D_4bde8 : decode_any W_4bde8 = Some (OpImm ALU_AND (@BV 5 11%Z I) (@BV 5 27%Z I) (@BV 12 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bdec : bv 32 := @BV 32 0xffc57513%Z I.

Lemma D_4bdec : decode_any W_4bdec = Some (OpImm ALU_AND (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 4092%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bdf0 : bv 32 := @BV 32 0x00b56533%Z I.

Lemma D_4bdf0 : decode_any W_4bdf0 = Some (Op ALU_OR (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bdf4 : bv 32 := @BV 32 0x0204d593%Z I.

Lemma D_4bdf4 : decode_any W_4bdf4 = Some (ShiftImm ALU_SRL (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bdf8 : bv 32 := @BV 32 0x030ad613%Z I.

Lemma D_4bdf8 : decode_any W_4bdf8 = Some (ShiftImm ALU_SRL (@BV 5 12%Z I) (@BV 5 21%Z I) (@BV 6 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bdfc : bv 32 := @BV 32 0xfeaa08a3%Z I.

Lemma D_4bdfc : decode_any W_4bdfc = Some (Store SZ1 (@BV 5 20%Z I) (@BV 5 10%Z I) (@BV 12 4081%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4be00 : bv 32 := @BV 32 0xfeba1923%Z I.

Lemma D_4be00 : decode_any W_4be00 = Some (Store SZ2 (@BV 5 20%Z I) (@BV 5 11%Z I) (@BV 12 4082%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4be04 : bv 32 := @BV 32 0xfe9a2a23%Z I.

Lemma D_4be04 : decode_any W_4be04 = Some (Store SZ4 (@BV 5 20%Z I) (@BV 5 9%Z I) (@BV 12 4084%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4be08 : bv 32 := @BV 32 0x5c061463%Z I.

Lemma D_4be08 : decode_any W_4be08 = Some (Branch BC_NE (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 13 1480%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4be0c : bv 32 := @BV 32 0xff0a0a93%Z I.

Lemma D_4be0c : decode_any W_4be0c = Some (OpImm ALU_ADD (@BV 5 21%Z I) (@BV 5 20%Z I) (@BV 12 4080%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4be10 : bv 32 := @BV 32 0x08f57513%Z I.

Lemma D_4be10 : decode_any W_4be10 = Some (OpImm ALU_AND (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 143%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4be14 : bv 32 := @BV 32 0x01013583%Z I.

Lemma D_4be14 : decode_any W_4be14 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4be18 : bv 32 := @BV 32 0x00b56533%Z I.

Lemma D_4be18 : decode_any W_4be18 = Some (Op ALU_OR (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4be1c : bv 32 := @BV 32 0x00aa80a3%Z I.

Lemma D_4be1c : decode_any W_4be1c = Some (Store SZ1 (@BV 5 21%Z I) (@BV 5 10%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4be20 : bv 32 := @BV 32 0x080d0c63%Z I.

Lemma D_4be20 : decode_any W_4be20 = Some (Branch BC_EQ (@BV 5 26%Z I) (@BV 5 0%Z I) (@BV 13 152%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4be24 : bv 32 := @BV 32 0x000d3503%Z I.

Lemma D_4be24 : decode_any W_4be24 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 26%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4be28 : bv 32 := @BV 32 0x00852c03%Z I.

Lemma D_4be28 : decode_any W_4be28 = Some (Load SZ4 true (@BV 5 24%Z I) (@BV 5 10%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4be2c : bv 32 := @BV 32 0x020c1c13%Z I.

Lemma D_4be2c : decode_any W_4be2c = Some (ShiftImm ALU_SLL (@BV 5 24%Z I) (@BV 5 24%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4be30 : bv 32 := @BV 32 0x08c0006f%Z I.

Lemma D_4be30 : decode_any W_4be30 = Some (Jal (@BV 5 0%Z I) (@BV 21 140%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4be34 : bv 32 := @BV 32 0x3d8b0513%Z I.



(* [comment removed for export] *)
Definition W_4be38 : bv 32 := @BV 32 0x0ff00593%Z I.



(* [comment removed for export] *)
Definition W_4be3c : bv 32 := @BV 32 0xffc57613%Z I.



(* [comment removed for export] *)
Definition W_4be40 : bv 32 := @BV 32 0x00100693%Z I.



(* [comment removed for export] *)
Definition W_4be44 : bv 32 := @BV 32 0x1406272f%Z I.



(* [comment removed for export] *)
Definition W_4be48 : bv 32 := @BV 32 0x00068793%Z I.



(* [comment removed for export] *)
Definition W_4be4c : bv 32 := @BV 32 0x00f747b3%Z I.



(* [comment removed for export] *)
Definition W_4be50 : bv 32 := @BV 32 0x00b7f7b3%Z I.



(* [comment removed for export] *)
Definition W_4be54 : bv 32 := @BV 32 0x00f747b3%Z I.



(* [comment removed for export] *)
Definition W_4be58 : bv 32 := @BV 32 0x18f627af%Z I.



(* [comment removed for export] *)
Definition W_4be5c : bv 32 := @BV 32 0xfe0794e3%Z I.



(* [comment removed for export] *)
Definition W_4be60 : bv 32 := @BV 32 0x0ff77593%Z I.



(* [comment removed for export] *)
Definition W_4be64 : bv 32 := @BV 32 0x60059063%Z I.



(* [comment removed for export] *)
Definition W_4be68 : bv 32 := @BV 32 0x3e0b0593%Z I.



(* [comment removed for export] *)
Definition W_4be6c : bv 32 := @BV 32 0x00800693%Z I.



(* [comment removed for export] *)
Definition W_4be70 : bv 32 := @BV 32 0x000b0513%Z I.



(* [comment removed for export] *)
Definition W_4be74 : bv 32 := @BV 32 0x00098613%Z I.



(* [comment removed for export] *)
Definition W_4be78 : bv 32 := @BV 32 0x3fc040ef%Z I.



(* [comment removed for export] *)
Definition W_4be7c : bv 32 := @BV 32 0x00050913%Z I.



(* [comment removed for export] *)
Definition W_4be80 : bv 32 := @BV 32 0x0310000f%Z I.



(* [comment removed for export] *)
Definition W_4be84 : bv 32 := @BV 32 0x3c0b0c23%Z I.



(* [comment removed for export] *)
Definition W_4be88 : bv 32 := @BV 32 0xf2051ee3%Z I.



(* [comment removed for export] *)
Definition W_4be8c : bv 32 := @BV 32 0x2a92e0ef%Z I.
Lemma F_4be8c : fetch_word Asan.M.loaded_segments (@BV 64 0x4be94%Z I : word) = Some W_4be8c.
Proof. vm_refl. Qed.
Lemma D_4be8c : decode_any W_4be8c = Some (Jal (@BV 5 1%Z I) (@BV 21 191144%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4be90 : bv 32 := @BV 32 0x2b52e0ef%Z I.
Lemma F_4be90 : fetch_word Asan.M.loaded_segments (@BV 64 0x4be98%Z I : word) = Some W_4be90.
Proof. vm_refl. Qed.
Lemma D_4be90 : decode_any W_4be90 = Some (Jal (@BV 5 1%Z I) (@BV 21 191156%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4be94 : bv 32 := @BV 32 0x4c051c63%Z I.
Lemma F_4be94 : fetch_word Asan.M.loaded_segments (@BV 64 0x4be9c%Z I : word) = Some W_4be94.
Proof. vm_refl. Qed.
Lemma D_4be94 : decode_any W_4be94 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 1240%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4be98 : bv 32 := @BV 32 0x00048513%Z I.



(* [comment removed for export] *)
Definition W_4be9c : bv 32 := @BV 32 0x000b8593%Z I.



(* [comment removed for export] *)
Definition W_4bea0 : bv 32 := @BV 32 0x0cc270ef%Z I.



(* [comment removed for export] *)
Definition W_4bea4 : bv 32 := @BV 32 0x01490a33%Z I.



(* [comment removed for export] *)
Definition W_4bea8 : bv 32 := @BV 32 0x019a7533%Z I.



(* [comment removed for export] *)
Definition W_4beac : bv 32 := @BV 32 0x01298733%Z I.



(* [comment removed for export] *)
Definition W_4beb0 : bv 32 := @BV 32 0xf20512e3%Z I.



(* [comment removed for export] *)
Definition W_4beb4 : bv 32 := @BV 32 0xf29ff06f%Z I.



(* [comment removed for export] *)
Definition W_4beb8 : bv 32 := @BV 32 0x00000c13%Z I.



(* [comment removed for export] *)
Definition W_4bebc : bv 32 := @BV 32 0x000bb503%Z I.

Lemma D_4bebc : decode_any W_4bebc = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 23%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bec0 : bv 32 := @BV 32 0x008bb583%Z I.

Lemma D_4bec0 : decode_any W_4bec0 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 23%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bec4 : bv 32 := @BV 32 0x3b5420ef%Z I.

Lemma D_4bec4 : decode_any W_4bec4 = Some (Jal (@BV 5 1%Z I) (@BV 21 273332%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bec8 : bv 32 := @BV 32 0x02051513%Z I.

Lemma D_4bec8 : decode_any W_4bec8 = Some (ShiftImm ALU_SLL (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4becc : bv 32 := @BV 32 0x02055513%Z I.

Lemma D_4becc : decode_any W_4becc = Some (ShiftImm ALU_SRL (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bed0 : bv 32 := @BV 32 0x00ac6533%Z I.

Lemma D_4bed0 : decode_any W_4bed0 = Some (Op ALU_OR (@BV 5 10%Z I) (@BV 5 24%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bed4 : bv 32 := @BV 32 0x00aab423%Z I.

Lemma D_4bed4 : decode_any W_4bed4 = Some (Store SZ8 (@BV 5 21%Z I) (@BV 5 10%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bed8 : bv 32 := @BV 32 0x02040063%Z I.

Lemma D_4bed8 : decode_any W_4bed8 = Some (Branch BC_EQ (@BV 5 8%Z I) (@BV 5 0%Z I) (@BV 13 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bedc : bv 32 := @BV 32 0x000b3517%Z I.
Lemma F_4bedc : fetch_word Asan.M.loaded_segments (@BV 64 0x4bee4%Z I : word) = Some W_4bedc.
Proof. vm_refl. Qed.
Lemma D_4bedc : decode_any W_4bedc = Some (Auipc (@BV 5 10%Z I) (@BV 20 179%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bee0 : bv 32 := @BV 32 0x38c53503%Z I.
Lemma F_4bee0 : fetch_word Asan.M.loaded_segments (@BV 64 0x4bee8%Z I : word) = Some W_4bee0.
Proof. vm_refl. Qed.
Lemma D_4bee0 : decode_any W_4bee0 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 908%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bee4 : bv 32 := @BV 32 0x00053503%Z I.

Lemma D_4bee4 : decode_any W_4bee4 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bee8 : bv 32 := @BV 32 0x00395593%Z I.

Lemma D_4bee8 : decode_any W_4bee8 = Some (ShiftImm ALU_SRL (@BV 5 11%Z I) (@BV 5 18%Z I) (@BV 6 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4beec : bv 32 := @BV 32 0x00b50533%Z I.

Lemma D_4beec : decode_any W_4beec = Some (Op ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bef0 : bv 32 := @BV 32 0x00054503%Z I.

Lemma D_4bef0 : decode_any W_4bef0 = Some (Load SZ1 false (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bef4 : bv 32 := @BV 32 0x0c051063%Z I.

Lemma D_4bef4 : decode_any W_4bef4 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 192%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bef8 : bv 32 := @BV 32 0x020b3503%Z I.

Lemma D_4bef8 : decode_any W_4bef8 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 22%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4befc : bv 32 := @BV 32 0x02a96c63%Z I.

Lemma D_4befc : decode_any W_4befc = Some (Branch BC_LTU (@BV 5 18%Z I) (@BV 5 10%Z I) (@BV 13 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bf00 : bv 32 := @BV 32 0x00100593%Z I.

Lemma D_4bf00 : decode_any W_4bf00 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bf04 : bv 32 := @BV 32 0x02559593%Z I.

Lemma D_4bf04 : decode_any W_4bf04 = Some (ShiftImm ALU_SLL (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 6 37%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bf08 : bv 32 := @BV 32 0x00b505b3%Z I.

Lemma D_4bf08 : decode_any W_4bf08 = Some (Op ALU_ADD (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bf0c : bv 32 := @BV 32 0x02b97463%Z I.

Lemma D_4bf0c : decode_any W_4bf0c = Some (Branch BC_GEU (@BV 5 18%Z I) (@BV 5 11%Z I) (@BV 13 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bf10 : bv 32 := @BV 32 0x40a90533%Z I.



(* [comment removed for export] *)
Definition W_4bf14 : bv 32 := @BV 32 0x02055513%Z I.



(* [comment removed for export] *)
Definition W_4bf18 : bv 32 := @BV 32 0x01f57413%Z I.



(* [comment removed for export] *)
Definition W_4bf1c : bv 32 := @BV 32 0x01f00593%Z I.



(* [comment removed for export] *)
Definition W_4bf20 : bv 32 := @BV 32 0x56b40663%Z I.



(* [comment removed for export] *)
Definition W_4bf24 : bv 32 := @BV 32 0x01000593%Z I.



(* [comment removed for export] *)
Definition W_4bf28 : bv 32 := @BV 32 0x0285ee63%Z I.



(* [comment removed for export] *)
Definition W_4bf2c : bv 32 := @BV 32 0x00541413%Z I.



(* [comment removed for export] *)
Definition W_4bf30 : bv 32 := @BV 32 0x0580006f%Z I.



(* [comment removed for export] *)
Definition W_4bf34 : bv 32 := @BV 32 0x040b3503%Z I.

Lemma D_4bf34 : decode_any W_4bf34 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 22%Z I) (@BV 12 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bf38 : bv 32 := @BV 32 0xfff50593%Z I.

Lemma D_4bf38 : decode_any W_4bf38 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bf3c : bv 32 := @BV 32 0x0125f633%Z I.

Lemma D_4bf3c : decode_any W_4bf3c = Some (Op ALU_AND (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 5 18%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bf40 : bv 32 := @BV 32 0x52061663%Z I.

Lemma D_4bf40 : decode_any W_4bf40 = Some (Branch BC_NE (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 13 1324%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bf44 : bv 32 := @BV 32 0x00b57633%Z I.

Lemma D_4bf44 : decode_any W_4bf44 = Some (Op ALU_AND (@BV 5 12%Z I) (@BV 5 10%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bf48 : bv 32 := @BV 32 0x54061663%Z I.

Lemma D_4bf48 : decode_any W_4bf48 = Some (Branch BC_NE (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 13 1356%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bf4c : bv 32 := @BV 32 0x40a90633%Z I.

Lemma D_4bf4c : decode_any W_4bf4c = Some (Op ALU_SUB (@BV 5 12%Z I) (@BV 5 18%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bf50 : bv 32 := @BV 32 0x01063603%Z I.

Lemma D_4bf50 : decode_any W_4bf50 = Some (Load SZ8 true (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bf54 : bv 32 := @BV 32 0x00b605b3%Z I.

Lemma D_4bf54 : decode_any W_4bf54 = Some (Op ALU_ADD (@BV 5 11%Z I) (@BV 5 12%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bf58 : bv 32 := @BV 32 0x40a00433%Z I.

Lemma D_4bf58 : decode_any W_4bf58 = Some (Op ALU_SUB (@BV 5 8%Z I) (@BV 5 0%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bf5c : bv 32 := @BV 32 0x0085f433%Z I.

Lemma D_4bf5c : decode_any W_4bf5c = Some (Op ALU_AND (@BV 5 8%Z I) (@BV 5 11%Z I) (@BV 5 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bf60 : bv 32 := @BV 32 0x0280006f%Z I.

Lemma D_4bf60 : decode_any W_4bf60 = Some (Jal (@BV 5 0%Z I) (@BV 21 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bf64 : bv 32 := @BV 32 0xff040413%Z I.



(* [comment removed for export] *)
Definition W_4bf68 : bv 32 := @BV 32 0x20000593%Z I.



(* [comment removed for export] *)
Definition W_4bf6c : bv 32 := @BV 32 0x03f51513%Z I.



(* [comment removed for export] *)
Definition W_4bf70 : bv 32 := @BV 32 0x00145413%Z I.



(* [comment removed for export] *)
Definition W_4bf74 : bv 32 := @BV 32 0x00859433%Z I.



(* [comment removed for export] *)
Definition W_4bf78 : bv 32 := @BV 32 0x00145593%Z I.



(* [comment removed for export] *)
Definition W_4bf7c : bv 32 := @BV 32 0x43f55513%Z I.



(* [comment removed for export] *)
Definition W_4bf80 : bv 32 := @BV 32 0x00b57533%Z I.



(* [comment removed for export] *)
Definition W_4bf84 : bv 32 := @BV 32 0x00850433%Z I.



(* [comment removed for export] *)
Definition W_4bf88 : bv 32 := @BV 32 0x007c8c93%Z I.

Lemma D_4bf88 : decode_any W_4bf88 = Some (OpImm ALU_ADD (@BV 5 25%Z I) (@BV 5 25%Z I) (@BV 12 7%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bf8c : bv 32 := @BV 32 0xff8cfb13%Z I.

Lemma D_4bf8c : decode_any W_4bf8c = Some (OpImm ALU_AND (@BV 5 22%Z I) (@BV 5 25%Z I) (@BV 12 4088%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bf90 : bv 32 := @BV 32 0x412a05b3%Z I.

Lemma D_4bf90 : decode_any W_4bf90 = Some (Op ALU_SUB (@BV 5 11%Z I) (@BV 5 20%Z I) (@BV 5 18%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bf94 : bv 32 := @BV 32 0x0fa00613%Z I.

Lemma D_4bf94 : decode_any W_4bf94 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 250%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bf98 : bv 32 := @BV 32 0x00090513%Z I.

Lemma D_4bf98 : decode_any W_4bf98 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bf9c : bv 32 := @BV 32 0x66c230ef%Z I.

Lemma D_4bf9c : decode_any W_4bf9c = Some (Jal (@BV 5 1%Z I) (@BV 21 145004%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bfa0 : bv 32 := @BV 32 0x416905b3%Z I.

Lemma D_4bfa0 : decode_any W_4bfa0 = Some (Op ALU_SUB (@BV 5 11%Z I) (@BV 5 18%Z I) (@BV 5 22%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bfa4 : bv 32 := @BV 32 0x008585b3%Z I.

Lemma D_4bfa4 : decode_any W_4bfa4 = Some (Op ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bfa8 : bv 32 := @BV 32 0x0fa00613%Z I.

Lemma D_4bfa8 : decode_any W_4bfa8 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 250%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bfac : bv 32 := @BV 32 0x000b0513%Z I.

Lemma D_4bfac : decode_any W_4bfac = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 22%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bfb0 : bv 32 := @BV 32 0x658230ef%Z I.

Lemma D_4bfb0 : decode_any W_4bfb0 = Some (Jal (@BV 5 1%Z I) (@BV 21 144984%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bfb4 : bv 32 := @BV 32 0xfff80537%Z I.

Lemma D_4bfb4 : decode_any W_4bfb4 = Some (Lui (@BV 5 10%Z I) (@BV 20 1048448%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bfb8 : bv 32 := @BV 32 0x01055513%Z I.

Lemma D_4bfb8 : decode_any W_4bfb8 = Some (ShiftImm ALU_SRL (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 6 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bfbc : bv 32 := @BV 32 0x00a4fb33%Z I.

Lemma D_4bfbc : decode_any W_4bfbc = Some (Op ALU_AND (@BV 5 22%Z I) (@BV 5 9%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bfc0 : bv 32 := @BV 32 0x000b0a63%Z I.

Lemma D_4bfc0 : decode_any W_4bfc0 = Some (Branch BC_EQ (@BV 5 22%Z I) (@BV 5 0%Z I) (@BV 13 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bfc4 : bv 32 := @BV 32 0x000a0513%Z I.

Lemma D_4bfc4 : decode_any W_4bfc4 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 20%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bfc8 : bv 32 := @BV 32 0x000b0593%Z I.

Lemma D_4bfc8 : decode_any W_4bfc8 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 22%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bfcc : bv 32 := @BV 32 0x00000613%Z I.

Lemma D_4bfcc : decode_any W_4bfcc = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bfd0 : bv 32 := @BV 32 0x638230ef%Z I.

Lemma D_4bfd0 : decode_any W_4bfd0 = Some (Jal (@BV 5 1%Z I) (@BV 21 144952%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bfd4 : bv 32 := @BV 32 0x09648a63%Z I.

Lemma D_4bfd4 : decode_any W_4bfd4 = Some (Branch BC_EQ (@BV 5 9%Z I) (@BV 5 22%Z I) (@BV 13 148%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bfd8 : bv 32 := @BV 32 0x61c230ef%Z I.

Lemma D_4bfd8 : decode_any W_4bfd8 = Some (Jal (@BV 5 1%Z I) (@BV 21 144924%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bfdc : bv 32 := @BV 32 0x08050663%Z I.

Lemma D_4bfdc : decode_any W_4bfdc = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 140%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bfe0 : bv 32 := @BV 32 0x000b3517%Z I.
Lemma F_4bfe0 : fetch_word Asan.M.loaded_segments (@BV 64 0x4bfe8%Z I : word) = Some W_4bfe0.
Proof. vm_refl. Qed.
Lemma D_4bfe0 : decode_any W_4bfe0 = Some (Auipc (@BV 5 10%Z I) (@BV 20 179%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bfe4 : bv 32 := @BV 32 0x28853503%Z I.
Lemma F_4bfe4 : fetch_word Asan.M.loaded_segments (@BV 64 0x4bfec%Z I : word) = Some W_4bfe4.
Proof. vm_refl. Qed.
Lemma D_4bfe4 : decode_any W_4bfe4 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 648%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bfe8 : bv 32 := @BV 32 0x00053503%Z I.

Lemma D_4bfe8 : decode_any W_4bfe8 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bfec : bv 32 := @BV 32 0x016a0b33%Z I.

Lemma D_4bfec : decode_any W_4bfec = Some (Op ALU_ADD (@BV 5 22%Z I) (@BV 5 20%Z I) (@BV 5 22%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bff0 : bv 32 := @BV 32 0xfff50593%Z I.

Lemma D_4bff0 : decode_any W_4bff0 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bff4 : bv 32 := @BV 32 0x00b53633%Z I.

Lemma D_4bff4 : decode_any W_4bff4 = Some (Op ALU_SLTU (@BV 5 12%Z I) (@BV 5 10%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bff8 : bv 32 := @BV 32 0xfff60613%Z I.

Lemma D_4bff8 : decode_any W_4bff8 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4bffc : bv 32 := @BV 32 0x00b67633%Z I.

Lemma D_4bffc : decode_any W_4bffc = Some (Op ALU_AND (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c000 : bv 32 := @BV 32 0x05667263%Z I.

Lemma D_4c000 : decode_any W_4c000 = Some (Branch BC_GEU (@BV 5 12%Z I) (@BV 5 22%Z I) (@BV 13 68%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c004 : bv 32 := @BV 32 0x000b3617%Z I.
Lemma F_4c004 : fetch_word Asan.M.loaded_segments (@BV 64 0x4c00c%Z I : word) = Some W_4c004.
Proof. vm_refl. Qed.
Lemma D_4c004 : decode_any W_4c004 = Some (Auipc (@BV 5 12%Z I) (@BV 20 179%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c008 : bv 32 := @BV 32 0x26c63603%Z I.
Lemma F_4c008 : fetch_word Asan.M.loaded_segments (@BV 64 0x4c010%Z I : word) = Some W_4c008.
Proof. vm_refl. Qed.
Lemma D_4c008 : decode_any W_4c008 = Some (Load SZ8 true (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 620%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c00c : bv 32 := @BV 32 0x000b3697%Z I.
Lemma F_4c00c : fetch_word Asan.M.loaded_segments (@BV 64 0x4c014%Z I : word) = Some W_4c00c.
Proof. vm_refl. Qed.
Lemma D_4c00c : decode_any W_4c00c = Some (Auipc (@BV 5 13%Z I) (@BV 20 179%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c010 : bv 32 := @BV 32 0x26c6b683%Z I.
Lemma F_4c010 : fetch_word Asan.M.loaded_segments (@BV 64 0x4c018%Z I : word) = Some W_4c010.
Proof. vm_refl. Qed.
Lemma D_4c010 : decode_any W_4c010 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 620%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c014 : bv 32 := @BV 32 0x00063783%Z I.

Lemma D_4c014 : decode_any W_4c014 = Some (Load SZ8 true (@BV 5 15%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c018 : bv 32 := @BV 32 0x0006b603%Z I.

Lemma D_4c018 : decode_any W_4c018 = Some (Load SZ8 true (@BV 5 12%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c01c : bv 32 := @BV 32 0xfff78713%Z I.

Lemma D_4c01c : decode_any W_4c01c = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 15%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c020 : bv 32 := @BV 32 0x01677463%Z I.

Lemma D_4c020 : decode_any W_4c020 = Some (Branch BC_GEU (@BV 5 14%Z I) (@BV 5 22%Z I) (@BV 13 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c024 : bv 32 := @BV 32 0x03667063%Z I.



(* [comment removed for export] *)
Definition W_4c028 : bv 32 := @BV 32 0x000b3697%Z I.
Lemma F_4c028 : fetch_word Asan.M.loaded_segments (@BV 64 0x4c030%Z I : word) = Some W_4c028.
Proof. vm_refl. Qed.
Lemma D_4c028 : decode_any W_4c028 = Some (Auipc (@BV 5 13%Z I) (@BV 20 179%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c02c : bv 32 := @BV 32 0x2586b683%Z I.
Lemma F_4c02c : fetch_word Asan.M.loaded_segments (@BV 64 0x4c034%Z I : word) = Some W_4c02c.
Proof. vm_refl. Qed.
Lemma D_4c02c : decode_any W_4c02c = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 600%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c030 : bv 32 := @BV 32 0x0006b883%Z I.

Lemma D_4c030 : decode_any W_4c030 = Some (Load SZ8 true (@BV 5 17%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c034 : bv 32 := @BV 32 0x0038d693%Z I.

Lemma D_4c034 : decode_any W_4c034 = Some (ShiftImm ALU_SRL (@BV 5 13%Z I) (@BV 5 17%Z I) (@BV 6 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c038 : bv 32 := @BV 32 0x00a68833%Z I.

Lemma D_4c038 : decode_any W_4c038 = Some (Op ALU_ADD (@BV 5 16%Z I) (@BV 5 13%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c03c : bv 32 := @BV 32 0x2568ea63%Z I.

Lemma D_4c03c : decode_any W_4c03c = Some (Branch BC_LTU (@BV 5 17%Z I) (@BV 5 22%Z I) (@BV 13 596%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c040 : bv 32 := @BV 32 0x25687863%Z I.

Lemma D_4c040 : decode_any W_4c040 = Some (Branch BC_GEU (@BV 5 16%Z I) (@BV 5 22%Z I) (@BV 13 592%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c044 : bv 32 := @BV 32 0x000b3597%Z I.
Lemma F_4c044 : fetch_word Asan.M.loaded_segments (@BV 64 0x4c04c%Z I : word) = Some W_4c044.
Proof. vm_refl. Qed.
Lemma D_4c044 : decode_any W_4c044 = Some (Auipc (@BV 5 11%Z I) (@BV 20 179%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c048 : bv 32 := @BV 32 0x21c5b583%Z I.
Lemma F_4c048 : fetch_word Asan.M.loaded_segments (@BV 64 0x4c050%Z I : word) = Some W_4c048.
Proof. vm_refl. Qed.
Lemma D_4c048 : decode_any W_4c048 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 540%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c04c : bv 32 := @BV 32 0x0555c583%Z I.

Lemma D_4c04c : decode_any W_4c04c = Some (Load SZ1 false (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 85%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c050 : bv 32 := @BV 32 0x003b5613%Z I.

Lemma D_4c050 : decode_any W_4c050 = Some (ShiftImm ALU_SRL (@BV 5 12%Z I) (@BV 5 22%Z I) (@BV 6 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c054 : bv 32 := @BV 32 0x00c50533%Z I.

Lemma D_4c054 : decode_any W_4c054 = Some (Op ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c058 : bv 32 := @BV 32 0x40b005bb%Z I.

Lemma D_4c058 : decode_any W_4c058 = Some (Op32 ALU_SUB (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c05c : bv 32 := @BV 32 0x00b4f5b3%Z I.

Lemma D_4c05c : decode_any W_4c05c = Some (Op ALU_AND (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c060 : bv 32 := @BV 32 0x0075f593%Z I.

Lemma D_4c060 : decode_any W_4c060 = Some (OpImm ALU_AND (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 7%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c064 : bv 32 := @BV 32 0x00b50023%Z I.

Lemma D_4c064 : decode_any W_4c064 = Some (Store SZ1 (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c068 : bv 32 := @BV 32 0x5182b0ef%Z I.
Lemma F_4c068 : fetch_word Asan.M.loaded_segments (@BV 64 0x4c070%Z I : word) = Some W_4c068.
Proof. vm_refl. Qed.
Lemma D_4c068 : decode_any W_4c068 = Some (Jal (@BV 5 1%Z I) (@BV 21 177432%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c06c : bv 32 := @BV 32 0x01053583%Z I.

Lemma D_4c06c : decode_any W_4c06c = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c070 : bv 32 := @BV 32 0x00053603%Z I.

Lemma D_4c070 : decode_any W_4c070 = Some (Load SZ8 true (@BV 5 12%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c074 : bv 32 := @BV 32 0x00853683%Z I.

Lemma D_4c074 : decode_any W_4c074 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 10%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c078 : bv 32 := @BV 32 0x40998733%Z I.

Lemma D_4c078 : decode_any W_4c078 = Some (Op ALU_SUB (@BV 5 14%Z I) (@BV 5 19%Z I) (@BV 5 9%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c07c : bv 32 := @BV 32 0x00b705b3%Z I.

Lemma D_4c07c : decode_any W_4c07c = Some (Op ALU_ADD (@BV 5 11%Z I) (@BV 5 14%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c080 : bv 32 := @BV 32 0x00010737%Z I.

Lemma D_4c080 : decode_any W_4c080 = Some (Lui (@BV 5 14%Z I) (@BV 20 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c084 : bv 32 := @BV 32 0x0017071b%Z I.

Lemma D_4c084 : decode_any W_4c084 = Some (OpImm32 (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c088 : bv 32 := @BV 32 0x00160613%Z I.

Lemma D_4c088 : decode_any W_4c088 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c08c : bv 32 := @BV 32 0x009686b3%Z I.

Lemma D_4c08c : decode_any W_4c08c = Some (Op ALU_ADD (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 5 9%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c090 : bv 32 := @BV 32 0x00c53023%Z I.

Lemma D_4c090 : decode_any W_4c090 = Some (Store SZ8 (@BV 5 10%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c094 : bv 32 := @BV 32 0x00d53423%Z I.

Lemma D_4c094 : decode_any W_4c094 = Some (Store SZ8 (@BV 5 10%Z I) (@BV 5 13%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c098 : bv 32 := @BV 32 0x00b53823%Z I.

Lemma D_4c098 : decode_any W_4c098 = Some (Store SZ8 (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c09c : bv 32 := @BV 32 0x00e9ee63%Z I.

Lemma D_4c09c : decode_any W_4c09c = Some (Branch BC_LTU (@BV 5 19%Z I) (@BV 5 14%Z I) (@BV 13 28%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c0a0 : bv 32 := @BV 32 0x06853583%Z I.

Lemma D_4c0a0 : decode_any W_4c0a0 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 104%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c0a4 : bv 32 := @BV 32 0x00158593%Z I.

Lemma D_4c0a4 : decode_any W_4c0a4 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c0a8 : bv 32 := @BV 32 0x06b53423%Z I.

Lemma D_4c0a8 : decode_any W_4c0a8 = Some (Store SZ8 (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 104%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c0ac : bv 32 := @BV 32 0x00813503%Z I.

Lemma D_4c0ac : decode_any W_4c0ac = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c0b0 : bv 32 := @BV 32 0x10051c63%Z I.

Lemma D_4c0b0 : decode_any W_4c0b0 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 280%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c0b4 : bv 32 := @BV 32 0x1480006f%Z I.



(* [comment removed for export] *)
Definition W_4c0b8 : bv 32 := @BV 32 0x20000593%Z I.

Lemma D_4c0b8 : decode_any W_4c0b8 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 512%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c0bc : bv 32 := @BV 32 0x07050513%Z I.

Lemma D_4c0bc : decode_any W_4c0bc = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 112%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c0c0 : bv 32 := @BV 32 0x0135e863%Z I.

Lemma D_4c0c0 : decode_any W_4c0c0 = Some (Branch BC_LTU (@BV 5 11%Z I) (@BV 5 19%Z I) (@BV 13 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c0c4 : bv 32 := @BV 32 0x01f98593%Z I.

Lemma D_4c0c4 : decode_any W_4c0c4 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 19%Z I) (@BV 12 31%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c0c8 : bv 32 := @BV 32 0x0055d593%Z I.

Lemma D_4c0c8 : decode_any W_4c0c8 = Some (ShiftImm ALU_SRL (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 6 5%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c0cc : bv 32 := @BV 32 0x0e00006f%Z I.

Lemma D_4c0cc : decode_any W_4c0cc = Some (Jal (@BV 5 0%Z I) (@BV 21 224%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c0d0 : bv 32 := @BV 32 0x0019d593%Z I.

Lemma D_4c0d0 : decode_any W_4c0d0 = Some (ShiftImm ALU_SRL (@BV 5 11%Z I) (@BV 5 19%Z I) (@BV 6 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c0d4 : bv 32 := @BV 32 0x55555637%Z I.

Lemma D_4c0d4 : decode_any W_4c0d4 = Some (Lui (@BV 5 12%Z I) (@BV 20 349525%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c0d8 : bv 32 := @BV 32 0x333336b7%Z I.

Lemma D_4c0d8 : decode_any W_4c0d8 = Some (Lui (@BV 5 13%Z I) (@BV 20 209715%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c0dc : bv 32 := @BV 32 0x0f0f1737%Z I.

Lemma D_4c0dc : decode_any W_4c0dc = Some (Lui (@BV 5 14%Z I) (@BV 20 61681%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c0e0 : bv 32 := @BV 32 0x010107b7%Z I.

Lemma D_4c0e0 : decode_any W_4c0e0 = Some (Lui (@BV 5 15%Z I) (@BV 20 4112%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c0e4 : bv 32 := @BV 32 0x00b9e5b3%Z I.

Lemma D_4c0e4 : decode_any W_4c0e4 = Some (Op ALU_OR (@BV 5 11%Z I) (@BV 5 19%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c0e8 : bv 32 := @BV 32 0x5556061b%Z I.

Lemma D_4c0e8 : decode_any W_4c0e8 = Some (OpImm32 (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 1365%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c0ec : bv 32 := @BV 32 0x3336869b%Z I.

Lemma D_4c0ec : decode_any W_4c0ec = Some (OpImm32 (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 819%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c0f0 : bv 32 := @BV 32 0xf0f7071b%Z I.

Lemma D_4c0f0 : decode_any W_4c0f0 = Some (OpImm32 (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 12 3855%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c0f4 : bv 32 := @BV 32 0x1017879b%Z I.

Lemma D_4c0f4 : decode_any W_4c0f4 = Some (OpImm32 (@BV 5 15%Z I) (@BV 5 15%Z I) (@BV 12 257%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c0f8 : bv 32 := @BV 32 0x0025d813%Z I.

Lemma D_4c0f8 : decode_any W_4c0f8 = Some (ShiftImm ALU_SRL (@BV 5 16%Z I) (@BV 5 11%Z I) (@BV 6 2%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c0fc : bv 32 := @BV 32 0x0105e5b3%Z I.

Lemma D_4c0fc : decode_any W_4c0fc = Some (Op ALU_OR (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c100 : bv 32 := @BV 32 0x02061813%Z I.

Lemma D_4c100 : decode_any W_4c100 = Some (ShiftImm ALU_SLL (@BV 5 16%Z I) (@BV 5 12%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c104 : bv 32 := @BV 32 0x01060633%Z I.

Lemma D_4c104 : decode_any W_4c104 = Some (Op ALU_ADD (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 5 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c108 : bv 32 := @BV 32 0x02069813%Z I.

Lemma D_4c108 : decode_any W_4c108 = Some (ShiftImm ALU_SLL (@BV 5 16%Z I) (@BV 5 13%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c10c : bv 32 := @BV 32 0x010686b3%Z I.

Lemma D_4c10c : decode_any W_4c10c = Some (Op ALU_ADD (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 5 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c110 : bv 32 := @BV 32 0x02071813%Z I.

Lemma D_4c110 : decode_any W_4c110 = Some (ShiftImm ALU_SLL (@BV 5 16%Z I) (@BV 5 14%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c114 : bv 32 := @BV 32 0x01070733%Z I.

Lemma D_4c114 : decode_any W_4c114 = Some (Op ALU_ADD (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 5 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c118 : bv 32 := @BV 32 0x02079813%Z I.

Lemma D_4c118 : decode_any W_4c118 = Some (ShiftImm ALU_SLL (@BV 5 16%Z I) (@BV 5 15%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c11c : bv 32 := @BV 32 0x010787b3%Z I.

Lemma D_4c11c : decode_any W_4c11c = Some (Op ALU_ADD (@BV 5 15%Z I) (@BV 5 15%Z I) (@BV 5 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c120 : bv 32 := @BV 32 0x0045d813%Z I.

Lemma D_4c120 : decode_any W_4c120 = Some (ShiftImm ALU_SRL (@BV 5 16%Z I) (@BV 5 11%Z I) (@BV 6 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c124 : bv 32 := @BV 32 0x0105e5b3%Z I.

Lemma D_4c124 : decode_any W_4c124 = Some (Op ALU_OR (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c128 : bv 32 := @BV 32 0x0085d813%Z I.

Lemma D_4c128 : decode_any W_4c128 = Some (ShiftImm ALU_SRL (@BV 5 16%Z I) (@BV 5 11%Z I) (@BV 6 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c12c : bv 32 := @BV 32 0x0105e5b3%Z I.

Lemma D_4c12c : decode_any W_4c12c = Some (Op ALU_OR (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c130 : bv 32 := @BV 32 0x0105d813%Z I.

Lemma D_4c130 : decode_any W_4c130 = Some (ShiftImm ALU_SRL (@BV 5 16%Z I) (@BV 5 11%Z I) (@BV 6 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c134 : bv 32 := @BV 32 0x0105e5b3%Z I.

Lemma D_4c134 : decode_any W_4c134 = Some (Op ALU_OR (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c138 : bv 32 := @BV 32 0x0205d813%Z I.

Lemma D_4c138 : decode_any W_4c138 = Some (ShiftImm ALU_SRL (@BV 5 16%Z I) (@BV 5 11%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c13c : bv 32 := @BV 32 0x0105e5b3%Z I.

Lemma D_4c13c : decode_any W_4c13c = Some (Op ALU_OR (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c140 : bv 32 := @BV 32 0xfff5c593%Z I.

Lemma D_4c140 : decode_any W_4c140 = Some (OpImm ALU_XOR (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c144 : bv 32 := @BV 32 0x0015d813%Z I.

Lemma D_4c144 : decode_any W_4c144 = Some (ShiftImm ALU_SRL (@BV 5 16%Z I) (@BV 5 11%Z I) (@BV 6 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c148 : bv 32 := @BV 32 0x00c87633%Z I.

Lemma D_4c148 : decode_any W_4c148 = Some (Op ALU_AND (@BV 5 12%Z I) (@BV 5 16%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c14c : bv 32 := @BV 32 0x40c585b3%Z I.

Lemma D_4c14c : decode_any W_4c14c = Some (Op ALU_SUB (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c150 : bv 32 := @BV 32 0x00d5f633%Z I.

Lemma D_4c150 : decode_any W_4c150 = Some (Op ALU_AND (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 5 13%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c154 : bv 32 := @BV 32 0x0025d593%Z I.

Lemma D_4c154 : decode_any W_4c154 = Some (ShiftImm ALU_SRL (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 6 2%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c158 : bv 32 := @BV 32 0x00d5f5b3%Z I.

Lemma D_4c158 : decode_any W_4c158 = Some (Op ALU_AND (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 13%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c15c : bv 32 := @BV 32 0x00b605b3%Z I.

Lemma D_4c15c : decode_any W_4c15c = Some (Op ALU_ADD (@BV 5 11%Z I) (@BV 5 12%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c160 : bv 32 := @BV 32 0x0045d613%Z I.

Lemma D_4c160 : decode_any W_4c160 = Some (ShiftImm ALU_SRL (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 6 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c164 : bv 32 := @BV 32 0x00c585b3%Z I.

Lemma D_4c164 : decode_any W_4c164 = Some (Op ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c168 : bv 32 := @BV 32 0x03e00613%Z I.

Lemma D_4c168 : decode_any W_4c168 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 62%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c16c : bv 32 := @BV 32 0x00e5f5b3%Z I.

Lemma D_4c16c : decode_any W_4c16c = Some (Op ALU_AND (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 14%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c170 : bv 32 := @BV 32 0xfff00693%Z I.

Lemma D_4c170 : decode_any W_4c170 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c174 : bv 32 := @BV 32 0x02f585b3%Z I.

Lemma D_4c174 : decode_any W_4c174 = Some (Mul M_MUL (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 15%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c178 : bv 32 := @BV 32 0x0385d593%Z I.

Lemma D_4c178 : decode_any W_4c178 = Some (ShiftImm ALU_SRL (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 6 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c17c : bv 32 := @BV 32 0x40b6063b%Z I.

Lemma D_4c17c : decode_any W_4c17c = Some (Op32 ALU_SUB (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c180 : bv 32 := @BV 32 0x00159593%Z I.

Lemma D_4c180 : decode_any W_4c180 = Some (ShiftImm ALU_SLL (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 6 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c184 : bv 32 := @BV 32 0x00c9d733%Z I.

Lemma D_4c184 : decode_any W_4c184 = Some (Op ALU_SRL (@BV 5 14%Z I) (@BV 5 19%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c188 : bv 32 := @BV 32 0x00c6963b%Z I.

Lemma D_4c188 : decode_any W_4c188 = Some (Op32 ALU_SLL (@BV 5 12%Z I) (@BV 5 13%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c18c : bv 32 := @BV 32 0x07e5c593%Z I.

Lemma D_4c18c : decode_any W_4c18c = Some (OpImm ALU_XOR (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 126%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c190 : bv 32 := @BV 32 0x00177713%Z I.

Lemma D_4c190 : decode_any W_4c190 = Some (OpImm ALU_AND (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c194 : bv 32 := @BV 32 0xfff64613%Z I.

Lemma D_4c194 : decode_any W_4c194 = Some (OpImm ALU_XOR (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c198 : bv 32 := @BV 32 0x00c9f633%Z I.

Lemma D_4c198 : decode_any W_4c198 = Some (Op ALU_AND (@BV 5 12%Z I) (@BV 5 19%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c19c : bv 32 := @BV 32 0x00e5e5b3%Z I.

Lemma D_4c19c : decode_any W_4c19c = Some (Op ALU_OR (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 14%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c1a0 : bv 32 := @BV 32 0x00c03633%Z I.

Lemma D_4c1a0 : decode_any W_4c1a0 = Some (Op ALU_SLTU (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c1a4 : bv 32 := @BV 32 0x00c585b3%Z I.

Lemma D_4c1a4 : decode_any W_4c1a4 = Some (Op ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c1a8 : bv 32 := @BV 32 0xffe58593%Z I.

Lemma D_4c1a8 : decode_any W_4c1a8 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 4094%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c1ac : bv 32 := @BV 32 0x00359593%Z I.

Lemma D_4c1ac : decode_any W_4c1ac = Some (ShiftImm ALU_SLL (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 6 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c1b0 : bv 32 := @BV 32 0x00b50533%Z I.

Lemma D_4c1b0 : decode_any W_4c1b0 = Some (Op ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c1b4 : bv 32 := @BV 32 0x00053583%Z I.

Lemma D_4c1b4 : decode_any W_4c1b4 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c1b8 : bv 32 := @BV 32 0x00158593%Z I.

Lemma D_4c1b8 : decode_any W_4c1b8 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c1bc : bv 32 := @BV 32 0x00b53023%Z I.

Lemma D_4c1bc : decode_any W_4c1bc = Some (Store SZ8 (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c1c0 : bv 32 := @BV 32 0x00813503%Z I.

Lemma D_4c1c0 : decode_any W_4c1c0 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c1c4 : bv 32 := @BV 32 0x02050c63%Z I.

Lemma D_4c1c4 : decode_any W_4c1c4 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c1c8 : bv 32 := @BV 32 0x000b3517%Z I.
Lemma F_4c1c8 : fetch_word Asan.M.loaded_segments (@BV 64 0x4c1d0%Z I : word) = Some W_4c1c8.
Proof. vm_refl. Qed.
Lemma D_4c1c8 : decode_any W_4c1c8 = Some (Auipc (@BV 5 10%Z I) (@BV 20 179%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c1cc : bv 32 := @BV 32 0x09853503%Z I.
Lemma F_4c1cc : fetch_word Asan.M.loaded_segments (@BV 64 0x4c1d4%Z I : word) = Some W_4c1cc.
Proof. vm_refl. Qed.
Lemma D_4c1cc : decode_any W_4c1cc = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 152%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c1d0 : bv 32 := @BV 32 0x02c52583%Z I.

Lemma D_4c1d0 : decode_any W_4c1d0 = Some (Load SZ4 true (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 44%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c1d4 : bv 32 := @BV 32 0x02058463%Z I.

Lemma D_4c1d4 : decode_any W_4c1d4 = Some (Branch BC_EQ (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c1d8 : bv 32 := @BV 32 0x00048613%Z I.

Lemma D_4c1d8 : decode_any W_4c1d8 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c1dc : bv 32 := @BV 32 0x00b4e463%Z I.

Lemma D_4c1dc : decode_any W_4c1dc = Some (Branch BC_LTU (@BV 5 9%Z I) (@BV 5 11%Z I) (@BV 13 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c1e0 : bv 32 := @BV 32 0x00058613%Z I.

Lemma D_4c1e0 : decode_any W_4c1e0 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c1e4 : bv 32 := @BV 32 0x000b3597%Z I.
Lemma F_4c1e4 : fetch_word Asan.M.loaded_segments (@BV 64 0x4c1ec%Z I : word) = Some W_4c1e4.
Proof. vm_refl. Qed.
Lemma D_4c1e4 : decode_any W_4c1e4 = Some (Auipc (@BV 5 11%Z I) (@BV 20 179%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c1e8 : bv 32 := @BV 32 0x0a45b583%Z I.
Lemma F_4c1e8 : fetch_word Asan.M.loaded_segments (@BV 64 0x4c1f0%Z I : word) = Some W_4c1e8.
Proof. vm_refl. Qed.
Lemma D_4c1e8 : decode_any W_4c1e8 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 164%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c1ec : bv 32 := @BV 32 0x0005b683%Z I.

Lemma D_4c1ec : decode_any W_4c1ec = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c1f0 : bv 32 := @BV 32 0x03452583%Z I.

Lemma D_4c1f0 : decode_any W_4c1f0 = Some (Load SZ4 true (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 52%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c1f4 : bv 32 := @BV 32 0x000a0513%Z I.

Lemma D_4c1f4 : decode_any W_4c1f4 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 20%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c1f8 : bv 32 := @BV 32 0x000680e7%Z I.

Lemma D_4c1f8 : decode_any W_4c1f8 = Some (Jalr (@BV 5 1%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c1fc : bv 32 := @BV 32 0x57d4f0ef%Z I.

Lemma D_4c1fc : decode_any W_4c1fc = Some (Jal (@BV 5 1%Z I) (@BV 21 327036%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c200 : bv 32 := @BV 32 0x001ac583%Z I.

Lemma D_4c200 : decode_any W_4c200 = Some (Load SZ1 false (@BV 5 11%Z I) (@BV 5 21%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c204 : bv 32 := @BV 32 0x40a0053b%Z I.

Lemma D_4c204 : decode_any W_4c204 = Some (Op32 ALU_SUB (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c208 : bv 32 := @BV 32 0x00c57513%Z I.

Lemma D_4c208 : decode_any W_4c208 = Some (OpImm ALU_AND (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c20c : bv 32 := @BV 32 0x0f35f593%Z I.

Lemma D_4c20c : decode_any W_4c20c = Some (OpImm ALU_AND (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 243%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c210 : bv 32 := @BV 32 0x00a5e533%Z I.

Lemma D_4c210 : decode_any W_4c210 = Some (Op ALU_OR (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c214 : bv 32 := @BV 32 0x00200593%Z I.

Lemma D_4c214 : decode_any W_4c214 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 2%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c218 : bv 32 := @BV 32 0x00aa80a3%Z I.

Lemma D_4c218 : decode_any W_4c218 = Some (Store SZ1 (@BV 5 21%Z I) (@BV 5 10%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c21c : bv 32 := @BV 32 0x0310000f%Z I.

Lemma D_4c21c : decode_any W_4c21c = Some (Fence (@BV 4 0%Z I) (@BV 4 3%Z I) (@BV 4 1%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c220 : bv 32 := @BV 32 0x00ba8023%Z I.

Lemma D_4c220 : decode_any W_4c220 = Some (Store SZ1 (@BV 5 21%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c224 : bv 32 := @BV 32 0x032a8063%Z I.

Lemma D_4c224 : decode_any W_4c224 = Some (Branch BC_EQ (@BV 5 21%Z I) (@BV 5 18%Z I) (@BV 13 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c228 : bv 32 := @BV 32 0x01090693%Z I.

Lemma D_4c228 : decode_any W_4c228 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 18%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c22c : bv 32 := @BV 32 0x20daee63%Z I.

Lemma D_4c22c : decode_any W_4c22c = Some (Branch BC_LTU (@BV 5 21%Z I) (@BV 5 13%Z I) (@BV 13 540%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c230 : bv 32 := @BV 32 0xfffc4517%Z I.
Lemma F_4c230 : fetch_word Asan.M.loaded_segments (@BV 64 0x4c238%Z I : word) = Some W_4c230.
Proof. vm_refl. Qed.
Lemma D_4c230 : decode_any W_4c230 = Some (Auipc (@BV 5 10%Z I) (@BV 20 1048516%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c234 : bv 32 := @BV 32 0x18053503%Z I.
Lemma F_4c234 : fetch_word Asan.M.loaded_segments (@BV 64 0x4c23c%Z I : word) = Some W_4c234.
Proof. vm_refl. Qed.
Lemma D_4c234 : decode_any W_4c234 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 384%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c238 : bv 32 := @BV 32 0x01593423%Z I.

Lemma D_4c238 : decode_any W_4c238 = Some (Store SZ8 (@BV 5 18%Z I) (@BV 5 21%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c23c : bv 32 := @BV 32 0x0310000f%Z I.

Lemma D_4c23c : decode_any W_4c23c = Some (Fence (@BV 4 0%Z I) (@BV 4 3%Z I) (@BV 4 1%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c240 : bv 32 := @BV 32 0x00a93023%Z I.

Lemma D_4c240 : decode_any W_4c240 = Some (Store SZ8 (@BV 5 18%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c244 : bv 32 := @BV 32 0x000a0513%Z I.

Lemma D_4c244 : decode_any W_4c244 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 20%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c248 : bv 32 := @BV 32 0x00048593%Z I.

Lemma D_4c248 : decode_any W_4c248 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c24c : bv 32 := @BV 32 0x13d300ef%Z I.

Lemma D_4c24c : decode_any W_4c24c = Some (Jal (@BV 5 1%Z I) (@BV 21 198972%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c250 : bv 32 := @BV 32 0x000a0513%Z I.
Lemma F_4c250 : fetch_word Asan.M.loaded_segments (@BV 64 0x4c258%Z I : word) = Some W_4c250.
Proof. vm_refl. Qed.
Lemma D_4c250 : decode_any W_4c250 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 20%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c254 : bv 32 := @BV 32 0x07813083%Z I.
Lemma F_4c254 : fetch_word Asan.M.loaded_segments (@BV 64 0x4c25c%Z I : word) = Some W_4c254.
Proof. vm_refl. Qed.
Lemma D_4c254 : decode_any W_4c254 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 120%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c258 : bv 32 := @BV 32 0x07013403%Z I.
Lemma F_4c258 : fetch_word Asan.M.loaded_segments (@BV 64 0x4c260%Z I : word) = Some W_4c258.
Proof. vm_refl. Qed.
Lemma D_4c258 : decode_any W_4c258 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 112%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c25c : bv 32 := @BV 32 0x06813483%Z I.
Lemma F_4c25c : fetch_word Asan.M.loaded_segments (@BV 64 0x4c264%Z I : word) = Some W_4c25c.
Proof. vm_refl. Qed.
Lemma D_4c25c : decode_any W_4c25c = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 104%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c260 : bv 32 := @BV 32 0x06013903%Z I.
Lemma F_4c260 : fetch_word Asan.M.loaded_segments (@BV 64 0x4c268%Z I : word) = Some W_4c260.
Proof. vm_refl. Qed.
Lemma D_4c260 : decode_any W_4c260 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 96%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c264 : bv 32 := @BV 32 0x05813983%Z I.
Lemma F_4c264 : fetch_word Asan.M.loaded_segments (@BV 64 0x4c26c%Z I : word) = Some W_4c264.
Proof. vm_refl. Qed.
Lemma D_4c264 : decode_any W_4c264 = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 2%Z I) (@BV 12 88%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c268 : bv 32 := @BV 32 0x05013a03%Z I.
Lemma F_4c268 : fetch_word Asan.M.loaded_segments (@BV 64 0x4c270%Z I : word) = Some W_4c268.
Proof. vm_refl. Qed.
Lemma D_4c268 : decode_any W_4c268 = Some (Load SZ8 true (@BV 5 20%Z I) (@BV 5 2%Z I) (@BV 12 80%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c26c : bv 32 := @BV 32 0x04813a83%Z I.
Lemma F_4c26c : fetch_word Asan.M.loaded_segments (@BV 64 0x4c274%Z I : word) = Some W_4c26c.
Proof. vm_refl. Qed.
Lemma D_4c26c : decode_any W_4c26c = Some (Load SZ8 true (@BV 5 21%Z I) (@BV 5 2%Z I) (@BV 12 72%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c270 : bv 32 := @BV 32 0x04013b03%Z I.
Lemma F_4c270 : fetch_word Asan.M.loaded_segments (@BV 64 0x4c278%Z I : word) = Some W_4c270.
Proof. vm_refl. Qed.
Lemma D_4c270 : decode_any W_4c270 = Some (Load SZ8 true (@BV 5 22%Z I) (@BV 5 2%Z I) (@BV 12 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c274 : bv 32 := @BV 32 0x03813b83%Z I.
Lemma F_4c274 : fetch_word Asan.M.loaded_segments (@BV 64 0x4c27c%Z I : word) = Some W_4c274.
Proof. vm_refl. Qed.
Lemma D_4c274 : decode_any W_4c274 = Some (Load SZ8 true (@BV 5 23%Z I) (@BV 5 2%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c278 : bv 32 := @BV 32 0x03013c03%Z I.
Lemma F_4c278 : fetch_word Asan.M.loaded_segments (@BV 64 0x4c280%Z I : word) = Some W_4c278.
Proof. vm_refl. Qed.
Lemma D_4c278 : decode_any W_4c278 = Some (Load SZ8 true (@BV 5 24%Z I) (@BV 5 2%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c27c : bv 32 := @BV 32 0x02813c83%Z I.
Lemma F_4c27c : fetch_word Asan.M.loaded_segments (@BV 64 0x4c284%Z I : word) = Some W_4c27c.
Proof. vm_refl. Qed.
Lemma D_4c27c : decode_any W_4c27c = Some (Load SZ8 true (@BV 5 25%Z I) (@BV 5 2%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c280 : bv 32 := @BV 32 0x02013d03%Z I.
Lemma F_4c280 : fetch_word Asan.M.loaded_segments (@BV 64 0x4c288%Z I : word) = Some W_4c280.
Proof. vm_refl. Qed.
Lemma D_4c280 : decode_any W_4c280 = Some (Load SZ8 true (@BV 5 26%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c284 : bv 32 := @BV 32 0x01813d83%Z I.
Lemma F_4c284 : fetch_word Asan.M.loaded_segments (@BV 64 0x4c28c%Z I : word) = Some W_4c284.
Proof. vm_refl. Qed.
Lemma D_4c284 : decode_any W_4c284 = Some (Load SZ8 true (@BV 5 27%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c288 : bv 32 := @BV 32 0x08010113%Z I.
Lemma F_4c288 : fetch_word Asan.M.loaded_segments (@BV 64 0x4c290%Z I : word) = Some W_4c288.
Proof. vm_refl. Qed.
Lemma D_4c288 : decode_any W_4c288 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 128%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c28c : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_4c28c : fetch_word Asan.M.loaded_segments (@BV 64 0x4c294%Z I : word) = Some W_4c28c.
Proof. vm_refl. Qed.
Lemma D_4c28c : decode_any W_4c28c = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.


























































































































































(* [comment removed for export] *)
Definition W_4c36c : bv 32 := @BV 32 0x00000a13%Z I.
Lemma F_4c36c : fetch_word Asan.M.loaded_segments (@BV 64 0x4c374%Z I : word) = Some W_4c36c.
Proof. vm_refl. Qed.
Lemma D_4c36c : decode_any W_4c36c = Some (OpImm ALU_ADD (@BV 5 20%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4c370 : bv 32 := @BV 32 0xee1ff06f%Z I.
Lemma F_4c370 : fetch_word Asan.M.loaded_segments (@BV 64 0x4c378%Z I : word) = Some W_4c370.
Proof. vm_refl. Qed.
Lemma D_4c370 : decode_any W_4c370 = Some (Jal (@BV 5 0%Z I) (@BV 21 2096864%Z I), 4%Z).
Proof. vm_refl. Qed.













































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































End AsCodeM0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Create HintDb asfr.

(* [comment removed for export] *)
Abbreviation AIMGLO := 0x10000%Z.
Abbreviation AIMGHI := 0x65d000%Z.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hideW (P : Prop) : Prop := P.
Ltac hidehypW H := lazymatch type of H with ?T => change T with (hideW T) in H end.
(* [comment removed for export] *)
Ltac hlia := repeat match goal with |- _ /\ _ => split end;
             first [ assumption
                   | lazymatch goal with |- hideW _ => unfold hideW in *; tauto | |- _ => first [ lia | unfold hideW in *; lia ] end ].
Ltac hlia0 := unfold hideW in *; lia.
(* [comment removed for export] *)
Notation "'TSIDE' T" := (hideW (((T + 4096 <= AIMGLO)%Z \/ (AIMGHI <= T)%Z) /\ ((T + 4096 <= 0x7fff7000)%Z \/ (0x10007fff8000 <= T)%Z))) (at level 10, T at level 9).
Notation "'PSIDE' p n" := (hideW ((p + n <= 0x7fff7000)%Z \/ (0x10007fff8000 + 16 <= p)%Z)) (at level 10, p at level 9, n at level 9).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPGen1.
Context {fx : FPState}.

Lemma v_and_m1_l : forall x : word, v_and (Z_to_bv 64 18446744073709551615) x = x.
Proof using.
  intros x. pose proof (u64_range x). (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end). apply bv_eq. rewrite (u_Z2bv 18446744073709551615) by lia.
  rewrite Z.land_comm. change 18446744073709551615%Z with (2 ^ 64 - 1)%Z.
  rewrite land_ones_mod by lia. rewrite u_Z2bv; rewrite ?Z.mod_small; lia.
Qed.

(* [comment removed for export] *)
Lemma v_andi_m4_aligned : forall x : word, (bv_unsigned x mod 4 = 0)%Z -> v_andi x (-4) = x.
Proof using.
  intros x Hx. pose proof (u64_range x) as R.
  rewrite <- (Z_to_bv_bv_unsigned 64 x) at 1. rewrite andi_m4 by lia. rewrite Hx, Z.sub_0_r.
  apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
Lemma v_sllw_mult32 : forall (c : Z) (y : word), (0 <= c < 2 ^ 31)%Z -> (bv_unsigned y mod 32 = 0)%Z ->
  v_sllw (Z_to_bv 64 c) y = Z_to_bv 64 c.
Proof using.
  intros c y Hc Hy. (lazymatch goal with |- ?G => let G' := eval unfold v_sllw in G in change_no_check G' end). rewrite Hy, Z.shiftl_0_r, u_Z2bv by lia. f_equal.
  apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31)%Z. lia.
Qed.


(* [comment removed for export] *)
Lemma rdn1_wbytes_in : forall segs m (a : word) bs (k : nat),
  (k < length bs)%nat -> (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  rdn segs (wbytes m a bs) (at_ a (Z.of_nat k)) 1 = Some [nth k bs (Z_to_bv 8 0)].
Proof using.
  intros segs m a bs k Hk Hnw. pose proof (u64_range a) as Ha. (lazymatch goal with |- ?G => let G' := eval cbn [rdn] in G in change_no_check G' end).
  rewrite (AsRtIMemmove.wbytes_get_g bs m a (at_ a (Z.of_nat k)) Hnw).
  rewrite at_u by lia.
  replace (inrng (bv_unsigned a) (Z.of_nat (length bs)) (bv_unsigned a + Z.of_nat k)) with true.
  2:{ symmetry. apply inrng_true. lia. }
  replace (Z.to_nat (bv_unsigned a + Z.of_nat k - bv_unsigned a)) with k by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Lemma shad_facts2 : forall p n8, (p + n8 <= 0x7fff7000 \/ 0x10007fff8000 <= p)%Z -> (0 <= p)%Z -> (p + n8 <= 2 ^ 47)%Z -> (8 <= n8)%Z ->
  (p mod 8 = 0)%Z -> (n8 mod 8 = 0)%Z ->
  (((p + n8 <= 0x7fff7000 /\ p / 8 + n8 / 8 <= 0xfffee00) \/ (0x10007fff8000 <= p /\ 0x2001000 <= p / 8))
   /\ p / 8 + n8 / 8 <= 2 ^ 44 /\ 1 <= n8 / 8 /\ p = 8 * (p / 8) /\ n8 = 8 * (n8 / 8)
   /\ (p + n8 + 7) / 8 = p / 8 + n8 / 8)%Z.
Proof using. intros p n8 H0 H1 H2 H3 H4 H5. repeat split; try lia. Qed.
Lemma p16_facts : forall x, (x mod 16 = 0)%Z -> (16 <= x)%Z ->
  ((x - 16) mod 4 = 0 /\ (x + -16) mod 4 = 0 /\ (8 * (x + -16)) mod 32 = 0 /\ x mod 8 = 0 /\ (x - 16) mod 16 = 0 /\ (x + -16) mod 8 = 0)%Z.
Proof using. intros x Hx H16. repeat split; lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma rdn_wbytes_sub : forall segs m (a : word) bs (k j : nat),
  (k + j <= length bs)%nat -> (bv_unsigned a + Z.of_nat (length bs) < 2 ^ 64)%Z ->
  rdn segs (wbytes m a bs) (at_ a (Z.of_nat k)) j = Some (firstn j (skipn k bs)).
Proof using.
  intros segs m a bs k j. revert k. induction j as [|j IH]; intros k Hkj Hnw.
  - (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). rewrite firstn_O. reflexivity.
  - rewrite AsAinvDefs3.rdn_S. rewrite (rdn1_wbytes_in segs m a bs k) by lia.
    pose proof (u64_range a) as Ha.
    replace (at_ a (Z.of_nat k) + 1)%bv with (at_ a (Z.of_nat (S k))).
    2:{ apply bv_eq. rewrite u_add1 by (rewrite at_u; lia). rewrite !at_u by lia. lia. }
    rewrite (IH (S k)) by lia.
    destruct (skipn k bs) as [|b r] eqn:E.
    + exfalso. apply (f_equal (@length byte)) in E. rewrite length_skipn in E. cbn in E. lia.
    + replace (skipn (S k) bs) with r.
      2:{ change r with (skipn 1 (b :: r)). rewrite <- E. rewrite skipn_skipn. f_equal; lia. }
      (lazymatch goal with |- ?G => let G' := eval cbn [firstn] in G in change_no_check G' end). f_equal. f_equal.
      change b with (nth 0 (b :: r) (Z_to_bv 8 0)). rewrite <- E. rewrite nth_skipn. f_equal; lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_skip : forall segs m (a : word) n bs (k : nat),
  rdn segs m a n = Some bs -> (k <= n)%nat -> (bv_unsigned a + Z.of_nat n < 2 ^ 64)%Z ->
  rdn segs m (at_ a (Z.of_nat k)) (n - k) = Some (skipn k bs).
Proof using.
  intros segs m a n bs k. revert a n bs. induction k as [|k IH]; intros a n bs Hr Hk Hnw.
  - (lazymatch goal with |- ?G => let G' := eval cbn [skipn Z.of_nat] in G in change_no_check G' end). rewrite at_0, Nat.sub_0_r. exact Hr.
  - destruct n as [|n]; [lia|]. rewrite AsAinvDefs3.rdn_S in Hr.
    destruct (rdn segs m a 1) as [[|b [|]]|] eqn:E1; try discriminate Hr.
    destruct (rdn segs m (a + 1)%bv n) as [r|] eqn:E2; [|discriminate Hr]. injection Hr as <-.
    pose proof (u64_range a) as Ha.
    replace (at_ a (Z.of_nat (S k))) with (at_ (a + 1)%bv (Z.of_nat k)).
    2:{ apply bv_eq. rewrite !at_u; rewrite ?u_add1 by lia; lia. }
    replace (S n - S k)%nat with (n - k)%nat by lia. (lazymatch goal with |- ?G => let G' := eval cbn [skipn] in G in change_no_check G' end).
    apply IH; [exact E2 | lia | rewrite u_add1 by lia; lia].
Qed.

(* [comment removed for export] *)
Lemma rdn_defined_ex : forall segs (m : word -> option byte) (a : word) (n : nat),
  (forall i, (bv_unsigned a <= i < bv_unsigned a + Z.of_nat n)%Z -> m (Z_to_bv 64 i) <> None) ->
  (bv_unsigned a + Z.of_nat n < 2 ^ 64)%Z ->
  exists bs, rdn segs m a n = Some bs /\ length bs = n.
Proof using.
  intros segs m a n. revert a. induction n as [|n IH]; intros a Hdef Hnw.
  - exists []. split; reflexivity.
  - pose proof (u64_range a) as Ha. (lazymatch goal with |- ?G => let G' := eval cbn [rdn] in G in change_no_check G' end).
    destruct (m a) as [b|] eqn:E.
    2:{ exfalso. apply (Hdef (bv_unsigned a)); [lia|]. rewrite Z_to_bv_bv_unsigned. exact E. }
    destruct (IH (a + 1)%bv) as [bs [Hr Hl]].
    + intros i Hi. apply Hdef. rewrite u_add1 in Hi by lia. lia.
    + rewrite u_add1 by lia. lia.
    + rewrite Hr. exists (b :: bs). split; [reflexivity | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
Qed.

(* [comment removed for export] *)
Lemma rdn_cat : forall segs m (a : word) (j k : nat) l1 l2,
  rdn segs m a j = Some l1 -> rdn segs m (at_ a (Z.of_nat j)) k = Some l2 -> (bv_unsigned a + Z.of_nat j + Z.of_nat k < 2 ^ 64)%Z ->
  rdn segs m a (j + k) = Some (l1 ++ l2).
Proof using.
  intros segs m a j. revert a. induction j as [|j IH]; intros a k l1 l2 H1 H2 Hnw.
  - cbn in H1. injection H1 as <-. cbn [Z.of_nat] in H2. rewrite at_0 in H2. exact H2.
  - rewrite AsAinvDefs3.rdn_S in H1. (lazymatch goal with |- ?G => let G' := eval cbn [Nat.add] in G in change_no_check G' end). rewrite AsAinvDefs3.rdn_S.
    destruct (rdn segs m a 1) as [[|b0 [|]]|] eqn:E1; try discriminate H1.
    destruct (rdn segs m (a + 1)%bv j) as [r|] eqn:E2; [|discriminate H1]. injection H1 as <-.
    pose proof (u64_range a) as Ha.
    rewrite (IH (a + 1)%bv k r l2 E2); [reflexivity | | rewrite u_add1 by lia; lia].
    replace (at_ (a + 1)%bv (Z.of_nat j)) with (at_ a (Z.of_nat (S j))); [exact H2|].
    apply bv_eq. rewrite !at_u; rewrite ?u_add1 by lia; lia.
Qed.

Lemma ret_ok_lit : forall z, (0 <= z < 2 ^ 64)%Z -> (z mod 2 = 0)%Z -> ret_ok (Z_to_bv 64 z).
Proof using. intros z Hz He. apply ret_ok_even. rewrite u_Z2bv by lia. exact He. Qed.
(* [comment removed for export] *)
Lemma wc_rdn_wbytes_out3 : forall segs bs m (addr a : word) n,
  ((bv_unsigned a + Z.of_nat n <= bv_unsigned addr \/ bv_unsigned addr + Z.of_nat (length bs) <= bv_unsigned a)
   /\ bv_unsigned a + Z.of_nat n <= 2^64 /\ bv_unsigned addr + Z.of_nat (length bs) <= 2^64)%Z ->
  rdn segs (wbytes m addr bs) a n = rdn segs m a n.
Proof. intros segs bs m addr a n (H1 & H2 & H3). apply rdn_wbytes_out; assumption. Qed.
(* [comment removed for export] *)
Lemma wd_store_ok_sub3 : forall segs m (lo a : word) (N n : nat),
  (bv_unsigned lo + Z.of_nat N <= 2 ^ 64 /\ bv_unsigned lo <= bv_unsigned a /\ bv_unsigned a + Z.of_nat n <= bv_unsigned lo + Z.of_nat N)%Z ->
  store_ok segs m lo N = true -> store_ok segs m a n = true.
Proof. intros segs m lo a N n (H1 & H2 & H3) H. exact (store_ok_sub segs m lo a N n H1 H H2 H3). Qed.
End FPGen1.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac valz :=
  apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_srli, v_slli, v_add, v_sub, v_addi, v_or, at_ in G in change_no_check G' end);
  rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia; unorm; first [reflexivity | lia].

(* [comment removed for export] *)
Ltac addr_as Hr :=
  lazymatch goal with |- rdn _ _ ?a _ = _ =>
    lazymatch type of Hr with rdn _ _ ?b _ = _ =>
      first [ constr_eq a b
            | lazymatch a with Z_to_bv 64 ?x => lazymatch b with Z_to_bv 64 ?y => replace x with y by lia end end
            | replace a with b by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia) ] end end.

(* [comment removed for export] *)
Ltac rd_peel :=
  autounfold with asfr;
  repeat (rewrite wc_rdn_wbytes_out3; [ | rd8_side ]).

(* [comment removed for export] *)
Ltac rd_addr Hr :=
  gres; rwH; imm_norm; rewrite ?at_addi; zlit_at;
  try ((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; fold_at_vars);
  rd_peel; addr_as Hr; exact Hr.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac wc_off_ne a b :=
  lazymatch a with at_ ?x ?k1 => lazymatch b with at_ ?y ?k2 =>
    constr_eq x y; is_Z_lit k1; is_Z_lit k2;
    lazymatch eval vm_compute in (Z.eqb k1 k2) with false => idtac end end end.
Ltac rd_hit8 :=
  lazymatch goal with |- rdn _ (wbytes _ ?a _) ?b 8%nat = _ =>
    first [ constr_eq a b
          | wc_off_ne a b; fail 1
          | replace b with a by (first [f_equal; lia | apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia]) ];
    apply rdn_wbytes_hit8; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia end.
(* [comment removed for export] *)
Ltac wd_hit8 :=
  lazymatch goal with |- rdn _ (wbytes _ ?a _) ?b 8%nat = _ => constr_eq a b; apply rdn_wbytes_hit8; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia end.
Ltac wd_rdstep side :=
  lazymatch goal with
  | |- rdn _ (wbytes _ ?a _) ?b 8%nat = _ =>
      tryif constr_eq a b then first [ wd_hit8 | rewrite wc_rdn_wbytes_out3; [ | side ] ]
      else tryif wc_off_ne a b then (rewrite wc_rdn_wbytes_out3; [ | side ])
      else first [ rewrite wc_rdn_wbytes_out3; [ | side ] | rd_hit8 ]
  | _ => first [ rd_hit8 | rewrite wc_rdn_wbytes_out3; [ | side ] ]
  end.
Ltac rd_own :=
  gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; autounfold with asfr;
  repeat (wd_rdstep rd8_side);
  idtac.

(* [comment removed for export] *)
Ltac sok_side_old := rewrite ?at_u by lia; unorm; rewrite ?Z2Nat.id by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat Pos.iter_op Nat.add Nat.mul] in G in change_no_check G' end); lia.
(* [comment removed for export] *)
Ltac sok_side := first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_z2n1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat Pos.iter_op Nat.add Nat.mul] in G in change_no_check G' end); wd_zofnat; lia ]
                       | sok_side_old ].
Ltac any_ok_old :=
  repeat (eapply store_ok_mono; [apply wbytes_grows|]);
  match goal with
  | H : store_ok ?sg ?m ?b ?N = true |- store_ok _ _ _ _ = true =>
      first [ exact H
            | eapply (store_ok_sub sg m b _ N); [ sok_side | exact H | sok_side | sok_side ] ]
  end.
(* [comment removed for export] *)
Ltac sok_fast := (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_z2n1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat Pos.iter_op Nat.add Nat.mul] in G in change_no_check G' end); wd_zofnat; lia.
Ltac any_ok :=
  first [ repeat (eapply store_ok_mono; [apply wbytes_grows|]);
          match goal with
          | H : store_ok ?sg ?m ?b ?N = true |- store_ok _ _ _ _ = true =>
              first [ exact H | apply (wd_store_ok_sub3 sg m b _ N); [ solve [sok_fast] | exact H ] ]
          end
        | any_ok_old ].
Ltac stk_ok := any_ok.
Ltac hyp_ok := any_ok.

(* [comment removed for export] *)
Ltac fsd F D aa :=
  chain_step; [reflexivity
    | eapply step_sd_at with (a := aa);
      [exact F | reflexivity | exact D
      | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; first [reflexivity | f_equal; lia | apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_addi, at_ in G in change_no_check G' end); wd_ulia]
      | gres; rwH; reflexivity
      | first [stk_ok | hyp_ok] ]
    | step_simpl]; vn.
(* [comment removed for export] *)
Ltac fsw F D aa :=
  chain_step; [reflexivity
    | eapply step_sw_at with (a := aa);
      [exact F | reflexivity | exact D
      | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; first [reflexivity | f_equal; lia | apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_addi, at_ in G in change_no_check G' end); wd_ulia]
      | gres; rwH; reflexivity
      | first [stk_ok | hyp_ok] ]
    | step_simpl]; vn.

(* [comment removed for export] *)
Ltac fld F D vv :=
  chain_step; [reflexivity
    | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
      [exact F | reflexivity | exact D | rd_own | apply bytes_le_to_Z_8]
    | step_simpl]; vn.

(* [comment removed for export] *)
Ltac cld F D bbs vv Hr Hv :=
  chain_step; [reflexivity
    | eapply step_ld with (bs := bbs) (v := vv);
      [exact F | reflexivity | exact D | rd_addr Hr | first [exact Hv | rewrite Hv; unorm; first [reflexivity | lia]] ]
    | step_simpl]; vn.
Ltac clw F D bbs vv Hr Hv :=
  chain_step; [reflexivity
    | eapply step_lw with (bs := bbs) (v := vv);
      [exact F | reflexivity | exact D | rd_addr Hr | first [exact Hv | rewrite Hv; unorm; first [reflexivity | lia]] ]
    | step_simpl]; vn.
Ltac clwu F D bbs vv Hr Hv :=
  chain_step; [reflexivity
    | eapply step_lwu with (bs := bbs) (v := vv);
      [exact F | reflexivity | exact D | rd_addr Hr | first [exact Hv | rewrite Hv; unorm; first [reflexivity | lia]] ]
    | step_simpl]; vn.
Ltac clhu F D bbs vv Hr Hv :=
  chain_step; [reflexivity
    | eapply step_lhu with (bs := bbs) (v := vv);
      [exact F | reflexivity | exact D | rd_addr Hr | first [exact Hv | rewrite Hv; unorm; first [reflexivity | lia]] ]
    | step_simpl]; vn.
Ltac clbu F D bb Hr :=
  chain_step; [reflexivity
    | eapply step_lbu with (b := bb);
      [exact F | reflexivity | exact D | rd_addr Hr ]
    | step_simpl]; vn.
Ltac clb F D bb Hr :=
  chain_step; [reflexivity
    | eapply step_lb with (b := bb);
      [exact F | reflexivity | exact D | rd_addr Hr ]
    | step_simpl]; vn.
(* [comment removed for export] *)
Ltac cld8 F D vv Hr := cld F D (word_to_le_bytes 8 vv) vv Hr (bytes_le_to_Z_8 vv).

(* [comment removed for export] *)
Ltac rt F D :=
  chain_step; [reflexivity | eapply step_jalr_x0; [exact F | reflexivity | exact D | gres; rwH; reflexivity] | step_simpl]; vn.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
