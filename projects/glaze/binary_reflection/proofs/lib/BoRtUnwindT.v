(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.InstrEnc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Bo_code_70b0c_71670.
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
Definition W_714ac : bv 32 := @BV 32 0x0009c517%Z I.
Lemma F_714ac : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x714ac%Z I : word) = Some W_714ac.
Proof. vm_refl. Qed.
Lemma D_714ac : decode_any W_714ac = Some (Auipc (@BV 5 10%Z I) (@BV 20 156%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_714b0 : bv 32 := @BV 32 0x57450513%Z I.
Lemma F_714b0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x714b0%Z I : word) = Some W_714b0.
Proof. vm_refl. Qed.
Lemma D_714b0 : decode_any W_714b0 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 1396%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_714b4 : bv 32 := @BV 32 0x00054583%Z I.

Lemma D_714b4 : decode_any W_714b4 = Some (Load SZ1 false (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_714b8 : bv 32 := @BV 32 0x00058663%Z I.

Lemma D_714b8 : decode_any W_714b8 = Some (Branch BC_EQ (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_714bc : bv 32 := @BV 32 0x00452503%Z I.

Lemma D_714bc : decode_any W_714bc = Some (Load SZ4 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_714c0 : bv 32 := @BV 32 0x0598c06f%Z I.
Lemma F_714c0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x714c0%Z I : word) = Some W_714c0.
Proof. vm_refl. Qed.
Lemma D_714c0 : decode_any W_714c0 = Some (Jal (@BV 5 0%Z I) (@BV 21 575576%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_70b0c_71670.
Module Bo_code_7571c_75734.
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
Definition W_7571c : bv 32 := @BV 32 0x00099517%Z I.
Lemma F_7571c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7571c%Z I : word) = Some W_7571c.
Proof. vm_refl. Qed.
Lemma D_7571c : decode_any W_7571c = Some (Auipc (@BV 5 10%Z I) (@BV 20 153%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75720 : bv 32 := @BV 32 0x77c50503%Z I.
Lemma F_75720 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x75720%Z I : word) = Some W_75720.
Proof. vm_refl. Qed.
Lemma D_75720 : decode_any W_75720 = Some (Load SZ1 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 1916%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75724 : bv 32 := @BV 32 0x0230000f%Z I.
Lemma F_75724 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x75724%Z I : word) = Some W_75724.
Proof. vm_refl. Qed.
Lemma D_75724 : decode_any W_75724 = Some (Fence (@BV 4 0%Z I) (@BV 4 2%Z I) (@BV 4 3%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75728 : bv 32 := @BV 32 0xfff50513%Z I.
Lemma F_75728 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x75728%Z I : word) = Some W_75728.
Proof. vm_refl. Qed.
Lemma D_75728 : decode_any W_75728 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7572c : bv 32 := @BV 32 0x00153513%Z I.
Lemma F_7572c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7572c%Z I : word) = Some W_7572c.
Proof. vm_refl. Qed.
Lemma D_7572c : decode_any W_7572c = Some (OpImm ALU_SLTU (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75730 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_75730 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x75730%Z I : word) = Some W_75730.
Proof. vm_refl. Qed.
Lemma D_75730 : decode_any W_75730 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_7571c_75734.
Module Bo_code_76b0c_77514.
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
Definition W_773b4 : bv 32 := @BV 32 0x00098517%Z I.
Lemma F_773b4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x773b4%Z I : word) = Some W_773b4.
Proof. vm_refl. Qed.
Lemma D_773b4 : decode_any W_773b4 = Some (Auipc (@BV 5 10%Z I) (@BV 20 152%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_773b8 : bv 32 := @BV 32 0xb0852503%Z I.
Lemma F_773b8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x773b8%Z I : word) = Some W_773b8.
Proof. vm_refl. Qed.
Lemma D_773b8 : decode_any W_773b8 = Some (Load SZ4 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 2824%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_773bc : bv 32 := @BV 32 0x0230000f%Z I.
Lemma F_773bc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x773bc%Z I : word) = Some W_773bc.
Proof. vm_refl. Qed.
Lemma D_773bc : decode_any W_773bc = Some (Fence (@BV 4 0%Z I) (@BV 4 2%Z I) (@BV 4 3%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_773c0 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_773c0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x773c0%Z I : word) = Some W_773c0.
Proof. vm_refl. Qed.
Lemma D_773c0 : decode_any W_773c0 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_773c4 : bv 32 := @BV 32 0xfb010113%Z I.

Lemma D_773c4 : decode_any W_773c4 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4016%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_773c8 : bv 32 := @BV 32 0x04113423%Z I.

Lemma D_773c8 : decode_any W_773c8 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 72%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_773cc : bv 32 := @BV 32 0x04813023%Z I.

Lemma D_773cc : decode_any W_773cc = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_773d0 : bv 32 := @BV 32 0x02913c23%Z I.

Lemma D_773d0 : decode_any W_773d0 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_773d4 : bv 32 := @BV 32 0x03213823%Z I.

Lemma D_773d4 : decode_any W_773d4 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_773d8 : bv 32 := @BV 32 0x03313423%Z I.

Lemma D_773d8 : decode_any W_773d8 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 19%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_773dc : bv 32 := @BV 32 0x03413023%Z I.

Lemma D_773dc : decode_any W_773dc = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 20%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_773e0 : bv 32 := @BV 32 0x01513c23%Z I.

Lemma D_773e0 : decode_any W_773e0 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 21%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_773e4 : bv 32 := @BV 32 0x01613823%Z I.

Lemma D_773e4 : decode_any W_773e4 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 22%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_773e8 : bv 32 := @BV 32 0x01713423%Z I.

Lemma D_773e8 : decode_any W_773e8 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 23%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_773ec : bv 32 := @BV 32 0x01813023%Z I.

Lemma D_773ec : decode_any W_773ec = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 24%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_773f0 : bv 32 := @BV 32 0x00078493%Z I.

Lemma D_773f0 : decode_any W_773f0 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 15%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_773f4 : bv 32 := @BV 32 0x00070a93%Z I.

Lemma D_773f4 : decode_any W_773f4 = Some (OpImm ALU_ADD (@BV 5 21%Z I) (@BV 5 14%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_773f8 : bv 32 := @BV 32 0x00068a13%Z I.

Lemma D_773f8 : decode_any W_773f8 = Some (OpImm ALU_ADD (@BV 5 20%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_773fc : bv 32 := @BV 32 0x00060413%Z I.

Lemma D_773fc : decode_any W_773fc = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77400 : bv 32 := @BV 32 0x00058913%Z I.

Lemma D_77400 : decode_any W_77400 = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77404 : bv 32 := @BV 32 0x00050993%Z I.

Lemma D_77404 : decode_any W_77404 = Some (OpImm ALU_ADD (@BV 5 19%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77408 : bv 32 := @BV 32 0x00052423%Z I.

Lemma D_77408 : decode_any W_77408 = Some (Store SZ4 (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7740c : bv 32 := @BV 32 0xb10fe0ef%Z I.

Lemma D_7740c : decode_any W_7740c = Some (Jal (@BV 5 1%Z I) (@BV 21 2089744%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77410 : bv 32 := @BV 32 0x0c050a63%Z I.

Lemma D_77410 : decode_any W_77410 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 212%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77414 : bv 32 := @BV 32 0x219010ef%Z I.

Lemma D_77414 : decode_any W_77414 = Some (Jal (@BV 5 1%Z I) (@BV 21 6680%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77418 : bv 32 := @BV 32 0x04050a63%Z I.

Lemma D_77418 : decode_any W_77418 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 84%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7741c : bv 32 := @BV 32 0x7ff50c13%Z I.

Lemma D_7741c : decode_any W_7741c = Some (OpImm ALU_ADD (@BV 5 24%Z I) (@BV 5 10%Z I) (@BV 12 2047%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77420 : bv 32 := @BV 32 0x461c4583%Z I.

Lemma D_77420 : decode_any W_77420 = Some (Load SZ1 false (@BV 5 11%Z I) (@BV 5 24%Z I) (@BV 12 1121%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77424 : bv 32 := @BV 32 0x00100613%Z I.

Lemma D_77424 : decode_any W_77424 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77428 : bv 32 := @BV 32 0x46cc00a3%Z I.

Lemma D_77428 : decode_any W_77428 = Some (Store SZ1 (@BV 5 24%Z I) (@BV 5 12%Z I) (@BV 12 1121%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7742c : bv 32 := @BV 32 0x0a059a63%Z I.

Lemma D_7742c : decode_any W_7742c = Some (Branch BC_NE (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 180%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77430 : bv 32 := @BV 32 0x00050b93%Z I.

Lemma D_77430 : decode_any W_77430 = Some (OpImm ALU_ADD (@BV 5 23%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77434 : bv 32 := @BV 32 0x3bd010ef%Z I.

Lemma D_77434 : decode_any W_77434 = Some (Jal (@BV 5 1%Z I) (@BV 21 7100%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77438 : bv 32 := @BV 32 0x00050b13%Z I.

Lemma D_77438 : decode_any W_77438 = Some (OpImm ALU_ADD (@BV 5 22%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7743c : bv 32 := @BV 32 0x000b8513%Z I.

Lemma D_7743c : decode_any W_7743c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 23%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77440 : bv 32 := @BV 32 0x409010ef%Z I.

Lemma D_77440 : decode_any W_77440 = Some (Jal (@BV 5 1%Z I) (@BV 21 7176%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77444 : bv 32 := @BV 32 0x00050813%Z I.

Lemma D_77444 : decode_any W_77444 = Some (OpImm ALU_ADD (@BV 5 16%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77448 : bv 32 := @BV 32 0x060a8c63%Z I.

Lemma D_77448 : decode_any W_77448 = Some (Branch BC_EQ (@BV 5 21%Z I) (@BV 5 0%Z I) (@BV 13 120%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7744c : bv 32 := @BV 32 0x00100893%Z I.

Lemma D_7744c : decode_any W_7744c = Some (OpImm ALU_ADD (@BV 5 17%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77450 : bv 32 := @BV 32 0x00098513%Z I.

Lemma D_77450 : decode_any W_77450 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77454 : bv 32 := @BV 32 0x00048593%Z I.

Lemma D_77454 : decode_any W_77454 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77458 : bv 32 := @BV 32 0x00090613%Z I.

Lemma D_77458 : decode_any W_77458 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7745c : bv 32 := @BV 32 0x00040693%Z I.

Lemma D_7745c : decode_any W_7745c = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77460 : bv 32 := @BV 32 0x00000713%Z I.

Lemma D_77460 : decode_any W_77460 = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77464 : bv 32 := @BV 32 0x000b0793%Z I.

Lemma D_77464 : decode_any W_77464 = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 22%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77468 : bv 32 := @BV 32 0x0740006f%Z I.

Lemma D_77468 : decode_any W_77468 = Some (Jal (@BV 5 0%Z I) (@BV 21 116%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7746c : bv 32 := @BV 32 0x060a9c63%Z I.



(* [comment removed for export] *)
Definition W_77470 : bv 32 := @BV 32 0x00098513%Z I.



(* [comment removed for export] *)
Definition W_77474 : bv 32 := @BV 32 0x00048593%Z I.



(* [comment removed for export] *)
Definition W_77478 : bv 32 := @BV 32 0x00090613%Z I.



(* [comment removed for export] *)
Definition W_7747c : bv 32 := @BV 32 0x00040693%Z I.



(* [comment removed for export] *)
Definition W_77480 : bv 32 := @BV 32 0x000a0713%Z I.



(* [comment removed for export] *)
Definition W_77484 : bv 32 := @BV 32 0x00000793%Z I.



(* [comment removed for export] *)
Definition W_77488 : bv 32 := @BV 32 0x00000813%Z I.



(* [comment removed for export] *)
Definition W_7748c : bv 32 := @BV 32 0x00000893%Z I.



(* [comment removed for export] *)
Definition W_77490 : bv 32 := @BV 32 0x04813083%Z I.



(* [comment removed for export] *)
Definition W_77494 : bv 32 := @BV 32 0x04013403%Z I.



(* [comment removed for export] *)
Definition W_77498 : bv 32 := @BV 32 0x03813483%Z I.



(* [comment removed for export] *)
Definition W_7749c : bv 32 := @BV 32 0x03013903%Z I.



(* [comment removed for export] *)
Definition W_774a0 : bv 32 := @BV 32 0x02813983%Z I.



(* [comment removed for export] *)
Definition W_774a4 : bv 32 := @BV 32 0x02013a03%Z I.



(* [comment removed for export] *)
Definition W_774a8 : bv 32 := @BV 32 0x01813a83%Z I.



(* [comment removed for export] *)
Definition W_774ac : bv 32 := @BV 32 0x01013b03%Z I.



(* [comment removed for export] *)
Definition W_774b0 : bv 32 := @BV 32 0x00813b83%Z I.



(* [comment removed for export] *)
Definition W_774b4 : bv 32 := @BV 32 0x00013c03%Z I.



(* [comment removed for export] *)
Definition W_774b8 : bv 32 := @BV 32 0x05010113%Z I.



(* [comment removed for export] *)
Definition W_774bc : bv 32 := @BV 32 0x01c1906f%Z I.



(* [comment removed for export] *)
Definition W_774c0 : bv 32 := @BV 32 0x00098513%Z I.



(* [comment removed for export] *)
Definition W_774c4 : bv 32 := @BV 32 0x00048593%Z I.



(* [comment removed for export] *)
Definition W_774c8 : bv 32 := @BV 32 0x00090613%Z I.



(* [comment removed for export] *)
Definition W_774cc : bv 32 := @BV 32 0x00040693%Z I.



(* [comment removed for export] *)
Definition W_774d0 : bv 32 := @BV 32 0x000a0713%Z I.



(* [comment removed for export] *)
Definition W_774d4 : bv 32 := @BV 32 0x000b0793%Z I.



(* [comment removed for export] *)
Definition W_774d8 : bv 32 := @BV 32 0x00000893%Z I.



(* [comment removed for export] *)
Definition W_774dc : bv 32 := @BV 32 0x7fd180ef%Z I.

Lemma D_774dc : decode_any W_774dc = Some (Jal (@BV 5 1%Z I) (@BV 21 102396%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_774e0 : bv 32 := @BV 32 0x460c00a3%Z I.

Lemma D_774e0 : decode_any W_774e0 = Some (Store SZ1 (@BV 5 24%Z I) (@BV 5 0%Z I) (@BV 12 1121%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_774e4 : bv 32 := @BV 32 0x04813083%Z I.

Lemma D_774e4 : decode_any W_774e4 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 72%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_774e8 : bv 32 := @BV 32 0x04013403%Z I.

Lemma D_774e8 : decode_any W_774e8 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_774ec : bv 32 := @BV 32 0x03813483%Z I.

Lemma D_774ec : decode_any W_774ec = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_774f0 : bv 32 := @BV 32 0x03013903%Z I.

Lemma D_774f0 : decode_any W_774f0 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_774f4 : bv 32 := @BV 32 0x02813983%Z I.

Lemma D_774f4 : decode_any W_774f4 = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 2%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_774f8 : bv 32 := @BV 32 0x02013a03%Z I.

Lemma D_774f8 : decode_any W_774f8 = Some (Load SZ8 true (@BV 5 20%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_774fc : bv 32 := @BV 32 0x01813a83%Z I.

Lemma D_774fc : decode_any W_774fc = Some (Load SZ8 true (@BV 5 21%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77500 : bv 32 := @BV 32 0x01013b03%Z I.

Lemma D_77500 : decode_any W_77500 = Some (Load SZ8 true (@BV 5 22%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77504 : bv 32 := @BV 32 0x00813b83%Z I.

Lemma D_77504 : decode_any W_77504 = Some (Load SZ8 true (@BV 5 23%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77508 : bv 32 := @BV 32 0x00013c03%Z I.

Lemma D_77508 : decode_any W_77508 = Some (Load SZ8 true (@BV 5 24%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7750c : bv 32 := @BV 32 0x05010113%Z I.

Lemma D_7750c : decode_any W_7750c = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 80%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77510 : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_77510 : decode_any W_77510 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_76b0c_77514.
Module Bo_code_78b0c_799f4.
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
Definition W_78e2c : bv 32 := @BV 32 0xff010113%Z I.

Lemma D_78e2c : decode_any W_78e2c = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4080%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e30 : bv 32 := @BV 32 0x00113423%Z I.

Lemma D_78e30 : decode_any W_78e30 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e34 : bv 32 := @BV 32 0xe78f80ef%Z I.

Lemma D_78e34 : decode_any W_78e34 = Some (Jal (@BV 5 1%Z I) (@BV 21 2066040%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e38 : bv 32 := @BV 32 0x00050463%Z I.

Lemma D_78e38 : decode_any W_78e38 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e3c : bv 32 := @BV 32 0x09853503%Z I.

Lemma D_78e3c : decode_any W_78e3c = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 152%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e40 : bv 32 := @BV 32 0x00813083%Z I.

Lemma D_78e40 : decode_any W_78e40 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e44 : bv 32 := @BV 32 0x01010113%Z I.

Lemma D_78e44 : decode_any W_78e44 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e48 : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_78e48 : decode_any W_78e48 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ff0 : bv 32 := @BV 32 0x02850583%Z I.

Lemma D_78ff0 : decode_any W_78ff0 = Some (Load SZ1 true (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ff4 : bv 32 := @BV 32 0x0230000f%Z I.

Lemma D_78ff4 : decode_any W_78ff4 = Some (Fence (@BV 4 0%Z I) (@BV 4 2%Z I) (@BV 4 3%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ff8 : bv 32 := @BV 32 0x02058c63%Z I.

Lemma D_78ff8 : decode_any W_78ff8 = Some (Branch BC_EQ (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79030 : bv 32 := @BV 32 0x00853583%Z I.

Lemma D_79030 : decode_any W_79030 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79034 : bv 32 := @BV 32 0x01053503%Z I.

Lemma D_79034 : decode_any W_79034 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79038 : bv 32 := @BV 32 0x00b53533%Z I.

Lemma D_79038 : decode_any W_79038 = Some (Op ALU_SLTU (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7903c : bv 32 := @BV 32 0x40a00533%Z I.

Lemma D_7903c : decode_any W_7903c = Some (Op ALU_SUB (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79040 : bv 32 := @BV 32 0x00b57533%Z I.

Lemma D_79040 : decode_any W_79040 = Some (Op ALU_AND (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79044 : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_79044 : decode_any W_79044 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79048 : bv 32 := @BV 32 0x02850583%Z I.

Lemma D_79048 : decode_any W_79048 = Some (Load SZ1 true (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7904c : bv 32 := @BV 32 0x0230000f%Z I.

Lemma D_7904c : decode_any W_7904c = Some (Fence (@BV 4 0%Z I) (@BV 4 2%Z I) (@BV 4 3%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79050 : bv 32 := @BV 32 0x02058c63%Z I.

Lemma D_79050 : decode_any W_79050 = Some (Branch BC_EQ (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79088 : bv 32 := @BV 32 0x00853583%Z I.

Lemma D_79088 : decode_any W_79088 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7908c : bv 32 := @BV 32 0x01053503%Z I.

Lemma D_7908c : decode_any W_7908c = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79090 : bv 32 := @BV 32 0x00b535b3%Z I.

Lemma D_79090 : decode_any W_79090 = Some (Op ALU_SLTU (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79094 : bv 32 := @BV 32 0x40b005b3%Z I.

Lemma D_79094 : decode_any W_79094 = Some (Op ALU_SUB (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79098 : bv 32 := @BV 32 0x00a5f533%Z I.

Lemma D_79098 : decode_any W_79098 = Some (Op ALU_AND (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7909c : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_7909c : decode_any W_7909c = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.
























End Bo_code_78b0c_799f4.
Module Bo_code_7ab0c_7b3f4.
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
Definition W_7aea8 : bv 32 := @BV 32 0xfd010113%Z I.
Lemma F_7aea8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7aea8%Z I : word) = Some W_7aea8.
Proof. vm_refl. Qed.
Lemma D_7aea8 : decode_any W_7aea8 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4048%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aeac : bv 32 := @BV 32 0x02113423%Z I.
Lemma F_7aeac : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7aeac%Z I : word) = Some W_7aeac.
Proof. vm_refl. Qed.
Lemma D_7aeac : decode_any W_7aeac = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aeb0 : bv 32 := @BV 32 0x02813023%Z I.
Lemma F_7aeb0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7aeb0%Z I : word) = Some W_7aeb0.
Proof. vm_refl. Qed.
Lemma D_7aeb0 : decode_any W_7aeb0 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aeb4 : bv 32 := @BV 32 0x00913c23%Z I.
Lemma F_7aeb4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7aeb4%Z I : word) = Some W_7aeb4.
Proof. vm_refl. Qed.
Lemma D_7aeb4 : decode_any W_7aeb4 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aeb8 : bv 32 := @BV 32 0x01213823%Z I.
Lemma F_7aeb8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7aeb8%Z I : word) = Some W_7aeb8.
Proof. vm_refl. Qed.
Lemma D_7aeb8 : decode_any W_7aeb8 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aebc : bv 32 := @BV 32 0x01313423%Z I.
Lemma F_7aebc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7aebc%Z I : word) = Some W_7aebc.
Proof. vm_refl. Qed.
Lemma D_7aebc : decode_any W_7aebc = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 19%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aec0 : bv 32 := @BV 32 0x00123517%Z I.
Lemma F_7aec0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7aec0%Z I : word) = Some W_7aec0.
Proof. vm_refl. Qed.
Lemma D_7aec0 : decode_any W_7aec0 = Some (Auipc (@BV 5 10%Z I) (@BV 20 291%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aec4 : bv 32 := @BV 32 0xd8850413%Z I.
Lemma F_7aec4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7aec4%Z I : word) = Some W_7aec4.
Proof. vm_refl. Qed.
Lemma D_7aec4 : decode_any W_7aec4 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 10%Z I) (@BV 12 3464%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aec8 : bv 32 := @BV 32 0x00040503%Z I.
Lemma F_7aec8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7aec8%Z I : word) = Some W_7aec8.
Proof. vm_refl. Qed.
Lemma D_7aec8 : decode_any W_7aec8 = Some (Load SZ1 true (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aecc : bv 32 := @BV 32 0x0230000f%Z I.
Lemma F_7aecc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7aecc%Z I : word) = Some W_7aecc.
Proof. vm_refl. Qed.
Lemma D_7aecc : decode_any W_7aecc = Some (Fence (@BV 4 0%Z I) (@BV 4 2%Z I) (@BV 4 3%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aed0 : bv 32 := @BV 32 0x0e051e63%Z I.
Lemma F_7aed0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7aed0%Z I : word) = Some W_7aed0.
Proof. vm_refl. Qed.
Lemma D_7aed0 : decode_any W_7aed0 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 252%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aed4 : bv 32 := @BV 32 0x00140513%Z I.
Lemma F_7aed4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7aed4%Z I : word) = Some W_7aed4.
Proof. vm_refl. Qed.
Lemma D_7aed4 : decode_any W_7aed4 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aed8 : bv 32 := @BV 32 0x0ff00593%Z I.
Lemma F_7aed8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7aed8%Z I : word) = Some W_7aed8.
Proof. vm_refl. Qed.
Lemma D_7aed8 : decode_any W_7aed8 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 255%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aedc : bv 32 := @BV 32 0x00100613%Z I.
Lemma F_7aedc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7aedc%Z I : word) = Some W_7aedc.
Proof. vm_refl. Qed.
Lemma D_7aedc : decode_any W_7aedc = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aee0 : bv 32 := @BV 32 0xffc57693%Z I.
Lemma F_7aee0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7aee0%Z I : word) = Some W_7aee0.
Proof. vm_refl. Qed.
Lemma D_7aee0 : decode_any W_7aee0 = Some (OpImm ALU_AND (@BV 5 13%Z I) (@BV 5 10%Z I) (@BV 12 4092%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aee4 : bv 32 := @BV 32 0x00357713%Z I.
Lemma F_7aee4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7aee4%Z I : word) = Some W_7aee4.
Proof. vm_refl. Qed.
Lemma D_7aee4 : decode_any W_7aee4 = Some (OpImm ALU_AND (@BV 5 14%Z I) (@BV 5 10%Z I) (@BV 12 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aee8 : bv 32 := @BV 32 0x00371713%Z I.
Lemma F_7aee8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7aee8%Z I : word) = Some W_7aee8.
Proof. vm_refl. Qed.
Lemma D_7aee8 : decode_any W_7aee8 = Some (ShiftImm ALU_SLL (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 6 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aeec : bv 32 := @BV 32 0x00e595bb%Z I.
Lemma F_7aeec : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7aeec%Z I : word) = Some W_7aeec.
Proof. vm_refl. Qed.
Lemma D_7aeec : decode_any W_7aeec = Some (Op32 ALU_SLL (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 14%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aef0 : bv 32 := @BV 32 0x00e6163b%Z I.
Lemma F_7aef0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7aef0%Z I : word) = Some W_7aef0.
Proof. vm_refl. Qed.
Lemma D_7aef0 : decode_any W_7aef0 = Some (Op32 ALU_SLL (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 5 14%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aef4 : bv 32 := @BV 32 0x1406a7af%Z I.
Lemma F_7aef4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7aef4%Z I : word) = Some W_7aef4.
Proof. vm_refl. Qed.
Lemma D_7aef4 : decode_any W_7aef4 = Some (Lr AW true false (@BV 5 15%Z I) (@BV 5 13%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aef8 : bv 32 := @BV 32 0x00060813%Z I.
Lemma F_7aef8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7aef8%Z I : word) = Some W_7aef8.
Proof. vm_refl. Qed.
Lemma D_7aef8 : decode_any W_7aef8 = Some (OpImm ALU_ADD (@BV 5 16%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aefc : bv 32 := @BV 32 0x0107c833%Z I.
Lemma F_7aefc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7aefc%Z I : word) = Some W_7aefc.
Proof. vm_refl. Qed.
Lemma D_7aefc : decode_any W_7aefc = Some (Op ALU_XOR (@BV 5 16%Z I) (@BV 5 15%Z I) (@BV 5 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af00 : bv 32 := @BV 32 0x00b87833%Z I.
Lemma F_7af00 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af00%Z I : word) = Some W_7af00.
Proof. vm_refl. Qed.
Lemma D_7af00 : decode_any W_7af00 = Some (Op ALU_AND (@BV 5 16%Z I) (@BV 5 16%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af04 : bv 32 := @BV 32 0x0107c833%Z I.
Lemma F_7af04 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af04%Z I : word) = Some W_7af04.
Proof. vm_refl. Qed.
Lemma D_7af04 : decode_any W_7af04 = Some (Op ALU_XOR (@BV 5 16%Z I) (@BV 5 15%Z I) (@BV 5 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af08 : bv 32 := @BV 32 0x1906a82f%Z I.
Lemma F_7af08 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af08%Z I : word) = Some W_7af08.
Proof. vm_refl. Qed.
Lemma D_7af08 : decode_any W_7af08 = Some (Sc AW false false (@BV 5 16%Z I) (@BV 5 13%Z I) (@BV 5 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af0c : bv 32 := @BV 32 0xfe0814e3%Z I.
Lemma F_7af0c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af0c%Z I : word) = Some W_7af0c.
Proof. vm_refl. Qed.
Lemma D_7af0c : decode_any W_7af0c = Some (Branch BC_NE (@BV 5 16%Z I) (@BV 5 0%Z I) (@BV 13 8168%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af10 : bv 32 := @BV 32 0x00e7d5bb%Z I.
Lemma F_7af10 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af10%Z I : word) = Some W_7af10.
Proof. vm_refl. Qed.
Lemma D_7af10 : decode_any W_7af10 = Some (Op32 ALU_SRL (@BV 5 11%Z I) (@BV 5 15%Z I) (@BV 5 14%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af14 : bv 32 := @BV 32 0x0ff5f593%Z I.
Lemma F_7af14 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af14%Z I : word) = Some W_7af14.
Proof. vm_refl. Qed.
Lemma D_7af14 : decode_any W_7af14 = Some (OpImm ALU_AND (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 255%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af18 : bv 32 := @BV 32 0x0c059c63%Z I.
Lemma F_7af18 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af18%Z I : word) = Some W_7af18.
Proof. vm_refl. Qed.
Lemma D_7af18 : decode_any W_7af18 = Some (Branch BC_NE (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 216%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af1c : bv 32 := @BV 32 0x00040503%Z I.
Lemma F_7af1c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af1c%Z I : word) = Some W_7af1c.
Proof. vm_refl. Qed.
Lemma D_7af1c : decode_any W_7af1c = Some (Load SZ1 true (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af20 : bv 32 := @BV 32 0x0a051263%Z I.
Lemma F_7af20 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af20%Z I : word) = Some W_7af20.
Proof. vm_refl. Qed.
Lemma D_7af20 : decode_any W_7af20 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 164%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af24 : bv 32 := @BV 32 0x00094517%Z I.
Lemma F_7af24 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af24%Z I : word) = Some W_7af24.
Proof. vm_refl. Qed.
Lemma D_7af24 : decode_any W_7af24 = Some (Auipc (@BV 5 10%Z I) (@BV 20 148%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af28 : bv 32 := @BV 32 0x000815b7%Z I.
Lemma F_7af28 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af28%Z I : word) = Some W_7af28.
Proof. vm_refl. Qed.
Lemma D_7af28 : decode_any W_7af28 = Some (Lui (@BV 5 11%Z I) (@BV 20 129%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af2c : bv 32 := @BV 32 0x49c50493%Z I.
Lemma F_7af2c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af2c%Z I : word) = Some W_7af2c.
Proof. vm_refl. Qed.
Lemma D_7af2c : decode_any W_7af2c = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 12 1180%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af30 : bv 32 := @BV 32 0x0085851b%Z I.
Lemma F_7af30 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af30%Z I : word) = Some W_7af30.
Proof. vm_refl. Qed.
Lemma D_7af30 : decode_any W_7af30 = Some (OpImm32 (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af34 : bv 32 := @BV 32 0x00a48533%Z I.
Lemma F_7af34 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af34%Z I : word) = Some W_7af34.
Proof. vm_refl. Qed.
Lemma D_7af34 : decode_any W_7af34 = Some (Op ALU_ADD (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af38 : bv 32 := @BV 32 0x02800613%Z I.
Lemma F_7af38 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af38%Z I : word) = Some W_7af38.
Proof. vm_refl. Qed.
Lemma D_7af38 : decode_any W_7af38 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af3c : bv 32 := @BV 32 0x00000593%Z I.
Lemma F_7af3c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af3c%Z I : word) = Some W_7af3c.
Proof. vm_refl. Qed.
Lemma D_7af3c : decode_any W_7af3c = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af40 : bv 32 := @BV 32 0x269050ef%Z I.
Lemma F_7af40 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af40%Z I : word) = Some W_7af40.
Proof. vm_refl. Qed.
Lemma D_7af40 : decode_any W_7af40 = Some (Jal (@BV 5 1%Z I) (@BV 21 23144%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af44 : bv 32 := @BV 32 0x00048023%Z I.
Lemma F_7af44 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af44%Z I : word) = Some W_7af44.
Proof. vm_refl. Qed.
Lemma D_7af44 : decode_any W_7af44 = Some (Store SZ1 (@BV 5 9%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af48 : bv 32 := @BV 32 0x00848513%Z I.
Lemma F_7af48 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af48%Z I : word) = Some W_7af48.
Proof. vm_refl. Qed.
Lemma D_7af48 : decode_any W_7af48 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af4c : bv 32 := @BV 32 0x00040637%Z I.
Lemma F_7af4c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af4c%Z I : word) = Some W_7af4c.
Proof. vm_refl. Qed.
Lemma D_7af4c : decode_any W_7af4c = Some (Lui (@BV 5 12%Z I) (@BV 20 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af50 : bv 32 := @BV 32 0x000409b7%Z I.
Lemma F_7af50 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af50%Z I : word) = Some W_7af50.
Proof. vm_refl. Qed.
Lemma D_7af50 : decode_any W_7af50 = Some (Lui (@BV 5 19%Z I) (@BV 20 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af54 : bv 32 := @BV 32 0x00000593%Z I.
Lemma F_7af54 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af54%Z I : word) = Some W_7af54.
Proof. vm_refl. Qed.
Lemma D_7af54 : decode_any W_7af54 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af58 : bv 32 := @BV 32 0x251050ef%Z I.
Lemma F_7af58 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af58%Z I : word) = Some W_7af58.
Proof. vm_refl. Qed.
Lemma D_7af58 : decode_any W_7af58 = Some (Jal (@BV 5 1%Z I) (@BV 21 23120%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af5c : bv 32 := @BV 32 0x0409851b%Z I.
Lemma F_7af5c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af5c%Z I : word) = Some W_7af5c.
Proof. vm_refl. Qed.
Lemma D_7af5c : decode_any W_7af5c = Some (OpImm32 (@BV 5 10%Z I) (@BV 5 19%Z I) (@BV 12 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af60 : bv 32 := @BV 32 0x00a48533%Z I.
Lemma F_7af60 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af60%Z I : word) = Some W_7af60.
Proof. vm_refl. Qed.
Lemma D_7af60 : decode_any W_7af60 = Some (Op ALU_ADD (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af64 : bv 32 := @BV 32 0x01b00613%Z I.
Lemma F_7af64 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af64%Z I : word) = Some W_7af64.
Proof. vm_refl. Qed.
Lemma D_7af64 : decode_any W_7af64 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 27%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af68 : bv 32 := @BV 32 0x00761613%Z I.
Lemma F_7af68 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af68%Z I : word) = Some W_7af68.
Proof. vm_refl. Qed.
Lemma D_7af68 : decode_any W_7af68 = Some (ShiftImm ALU_SLL (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 6 7%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af6c : bv 32 := @BV 32 0x00000593%Z I.
Lemma F_7af6c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af6c%Z I : word) = Some W_7af6c.
Proof. vm_refl. Qed.
Lemma D_7af6c : decode_any W_7af6c = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af70 : bv 32 := @BV 32 0x239050ef%Z I.
Lemma F_7af70 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af70%Z I : word) = Some W_7af70.
Proof. vm_refl. Qed.
Lemma D_7af70 : decode_any W_7af70 = Some (Jal (@BV 5 1%Z I) (@BV 21 23096%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af74 : bv 32 := @BV 32 0x00041937%Z I.
Lemma F_7af74 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af74%Z I : word) = Some W_7af74.
Proof. vm_refl. Qed.
Lemma D_7af74 : decode_any W_7af74 = Some (Lui (@BV 5 18%Z I) (@BV 20 65%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af78 : bv 32 := @BV 32 0xdc09051b%Z I.
Lemma F_7af78 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af78%Z I : word) = Some W_7af78.
Proof. vm_refl. Qed.
Lemma D_7af78 : decode_any W_7af78 = Some (OpImm32 (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 12 3520%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af7c : bv 32 := @BV 32 0x00a48533%Z I.
Lemma F_7af7c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af7c%Z I : word) = Some W_7af7c.
Proof. vm_refl. Qed.
Lemma D_7af7c : decode_any W_7af7c = Some (Op ALU_ADD (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af80 : bv 32 := @BV 32 0x2489861b%Z I.
Lemma F_7af80 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af80%Z I : word) = Some W_7af80.
Proof. vm_refl. Qed.
Lemma D_7af80 : decode_any W_7af80 = Some (OpImm32 (@BV 5 12%Z I) (@BV 5 19%Z I) (@BV 12 584%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af84 : bv 32 := @BV 32 0x00000593%Z I.
Lemma F_7af84 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af84%Z I : word) = Some W_7af84.
Proof. vm_refl. Qed.
Lemma D_7af84 : decode_any W_7af84 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af88 : bv 32 := @BV 32 0x221050ef%Z I.
Lemma F_7af88 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af88%Z I : word) = Some W_7af88.
Proof. vm_refl. Qed.
Lemma D_7af88 : decode_any W_7af88 = Some (Jal (@BV 5 1%Z I) (@BV 21 23072%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af8c : bv 32 := @BV 32 0x0008b517%Z I.
Lemma F_7af8c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af8c%Z I : word) = Some W_7af8c.
Proof. vm_refl. Qed.
Lemma D_7af8c : decode_any W_7af8c = Some (Auipc (@BV 5 10%Z I) (@BV 20 139%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af90 : bv 32 := @BV 32 0xf6c53983%Z I.
Lemma F_7af90 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af90%Z I : word) = Some W_7af90.
Proof. vm_refl. Qed.
Lemma D_7af90 : decode_any W_7af90 = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 10%Z I) (@BV 12 3948%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af94 : bv 32 := @BV 32 0x0009b503%Z I.
Lemma F_7af94 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af94%Z I : word) = Some W_7af94.
Proof. vm_refl. Qed.
Lemma D_7af94 : decode_any W_7af94 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7af98 : bv 32 := @BV 32 0x00051663%Z I.
Lemma F_7af98 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7af98%Z I : word) = Some W_7af98.
Proof. vm_refl. Qed.
Lemma D_7af98 : decode_any W_7af98 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7afa4 : bv 32 := @BV 32 0x012485b3%Z I.
Lemma F_7afa4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7afa4%Z I : word) = Some W_7afa4.
Proof. vm_refl. Qed.
Lemma D_7afa4 : decode_any W_7afa4 = Some (Op ALU_ADD (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 5 18%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7afa8 : bv 32 := @BV 32 0xdd09061b%Z I.
Lemma F_7afa8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7afa8%Z I : word) = Some W_7afa8.
Proof. vm_refl. Qed.
Lemma D_7afa8 : decode_any W_7afa8 = Some (OpImm32 (@BV 5 12%Z I) (@BV 5 18%Z I) (@BV 12 3536%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7afac : bv 32 := @BV 32 0x00c48633%Z I.
Lemma F_7afac : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7afac%Z I : word) = Some W_7afac.
Proof. vm_refl. Qed.
Lemma D_7afac : decode_any W_7afac = Some (Op ALU_ADD (@BV 5 12%Z I) (@BV 5 9%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7afb0 : bv 32 := @BV 32 0x00100693%Z I.
Lemma F_7afb0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7afb0%Z I : word) = Some W_7afb0.
Proof. vm_refl. Qed.
Lemma D_7afb0 : decode_any W_7afb0 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7afb4 : bv 32 := @BV 32 0xdca5b023%Z I.
Lemma F_7afb4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7afb4%Z I : word) = Some W_7afb4.
Proof. vm_refl. Qed.
Lemma D_7afb4 : decode_any W_7afb4 = Some (Store SZ8 (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 3520%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7afb8 : bv 32 := @BV 32 0xdcc5b423%Z I.
Lemma F_7afb8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7afb8%Z I : word) = Some W_7afb8.
Proof. vm_refl. Qed.
Lemma D_7afb8 : decode_any W_7afb8 = Some (Store SZ8 (@BV 5 11%Z I) (@BV 5 12%Z I) (@BV 12 3528%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7afbc : bv 32 := @BV 32 0x0310000f%Z I.
Lemma F_7afbc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7afbc%Z I : word) = Some W_7afbc.
Proof. vm_refl. Qed.
Lemma D_7afbc : decode_any W_7afbc = Some (Fence (@BV 4 0%Z I) (@BV 4 3%Z I) (@BV 4 1%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7afc0 : bv 32 := @BV 32 0x00d40023%Z I.
Lemma F_7afc0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7afc0%Z I : word) = Some W_7afc0.
Proof. vm_refl. Qed.
Lemma D_7afc0 : decode_any W_7afc0 = Some (Store SZ1 (@BV 5 8%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7afc4 : bv 32 := @BV 32 0x0310000f%Z I.
Lemma F_7afc4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7afc4%Z I : word) = Some W_7afc4.
Proof. vm_refl. Qed.
Lemma D_7afc4 : decode_any W_7afc4 = Some (Fence (@BV 4 0%Z I) (@BV 4 3%Z I) (@BV 4 1%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7afc8 : bv 32 := @BV 32 0x000400a3%Z I.
Lemma F_7afc8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7afc8%Z I : word) = Some W_7afc8.
Proof. vm_refl. Qed.
Lemma D_7afc8 : decode_any W_7afc8 = Some (Store SZ1 (@BV 5 8%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7afcc : bv 32 := @BV 32 0x00094517%Z I.
Lemma F_7afcc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7afcc%Z I : word) = Some W_7afcc.
Proof. vm_refl. Qed.
Lemma D_7afcc : decode_any W_7afcc = Some (Auipc (@BV 5 10%Z I) (@BV 20 148%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7afd0 : bv 32 := @BV 32 0x3f450513%Z I.
Lemma F_7afd0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7afd0%Z I : word) = Some W_7afd0.
Proof. vm_refl. Qed.
Lemma D_7afd0 : decode_any W_7afd0 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 1012%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7afd4 : bv 32 := @BV 32 0x02813083%Z I.
Lemma F_7afd4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7afd4%Z I : word) = Some W_7afd4.
Proof. vm_refl. Qed.
Lemma D_7afd4 : decode_any W_7afd4 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7afd8 : bv 32 := @BV 32 0x02013403%Z I.
Lemma F_7afd8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7afd8%Z I : word) = Some W_7afd8.
Proof. vm_refl. Qed.
Lemma D_7afd8 : decode_any W_7afd8 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7afdc : bv 32 := @BV 32 0x01813483%Z I.
Lemma F_7afdc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7afdc%Z I : word) = Some W_7afdc.
Proof. vm_refl. Qed.
Lemma D_7afdc : decode_any W_7afdc = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7afe0 : bv 32 := @BV 32 0x01013903%Z I.
Lemma F_7afe0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7afe0%Z I : word) = Some W_7afe0.
Proof. vm_refl. Qed.
Lemma D_7afe0 : decode_any W_7afe0 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7afe4 : bv 32 := @BV 32 0x00813983%Z I.
Lemma F_7afe4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7afe4%Z I : word) = Some W_7afe4.
Proof. vm_refl. Qed.
Lemma D_7afe4 : decode_any W_7afe4 = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7afe8 : bv 32 := @BV 32 0x03010113%Z I.
Lemma F_7afe8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7afe8%Z I : word) = Some W_7afe8.
Proof. vm_refl. Qed.
Lemma D_7afe8 : decode_any W_7afe8 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7afec : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_7afec : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7afec%Z I : word) = Some W_7afec.
Proof. vm_refl. Qed.
Lemma D_7afec : decode_any W_7afec = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b3ac : bv 32 := @BV 32 0x00115517%Z I.
Lemma F_7b3ac : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7b3ac%Z I : word) = Some W_7b3ac.
Proof. vm_refl. Qed.
Lemma D_7b3ac : decode_any W_7b3ac = Some (Auipc (@BV 5 10%Z I) (@BV 20 277%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b3b0 : bv 32 := @BV 32 0x00100593%Z I.
Lemma F_7b3b0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7b3b0%Z I : word) = Some W_7b3b0.
Proof. vm_refl. Qed.
Lemma D_7b3b0 : decode_any W_7b3b0 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b3b4 : bv 32 := @BV 32 0x06b50a23%Z I.
Lemma F_7b3b4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7b3b4%Z I : word) = Some W_7b3b4.
Proof. vm_refl. Qed.
Lemma D_7b3b4 : decode_any W_7b3b4 = Some (Store SZ1 (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 116%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b3b8 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_7b3b8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7b3b8%Z I : word) = Some W_7b3b8.
Proof. vm_refl. Qed.
Lemma D_7b3b8 : decode_any W_7b3b8 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b3bc : bv 32 := @BV 32 0x00115517%Z I.
Lemma F_7b3bc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7b3bc%Z I : word) = Some W_7b3bc.
Proof. vm_refl. Qed.
Lemma D_7b3bc : decode_any W_7b3bc = Some (Auipc (@BV 5 10%Z I) (@BV 20 277%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b3c0 : bv 32 := @BV 32 0x06550503%Z I.
Lemma F_7b3c0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7b3c0%Z I : word) = Some W_7b3c0.
Proof. vm_refl. Qed.
Lemma D_7b3c0 : decode_any W_7b3c0 = Some (Load SZ1 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 101%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b3c4 : bv 32 := @BV 32 0x00a03533%Z I.
Lemma F_7b3c4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7b3c4%Z I : word) = Some W_7b3c4.
Proof. vm_refl. Qed.
Lemma D_7b3c4 : decode_any W_7b3c4 = Some (Op ALU_SLTU (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b3c8 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_7b3c8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7b3c8%Z I : word) = Some W_7b3c8.
Proof. vm_refl. Qed.
Lemma D_7b3c8 : decode_any W_7b3c8 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b3e4 : bv 32 := @BV 32 0x00115517%Z I.
Lemma F_7b3e4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7b3e4%Z I : word) = Some W_7b3e4.
Proof. vm_refl. Qed.
Lemma D_7b3e4 : decode_any W_7b3e4 = Some (Auipc (@BV 5 10%Z I) (@BV 20 277%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b3e8 : bv 32 := @BV 32 0x03e50503%Z I.
Lemma F_7b3e8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7b3e8%Z I : word) = Some W_7b3e8.
Proof. vm_refl. Qed.
Lemma D_7b3e8 : decode_any W_7b3e8 = Some (Load SZ1 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 62%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b3ec : bv 32 := @BV 32 0x00a03533%Z I.

Lemma D_7b3ec : decode_any W_7b3ec = Some (Op ALU_SLTU (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b3f0 : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_7b3f0 : decode_any W_7b3f0 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_7ab0c_7b3f4.
Module Bo_code_8fc84_905f0.
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
Definition W_8fc84 : bv 32 := @BV 32 0xfd010113%Z I.
Lemma F_8fc84 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fc84%Z I : word) = Some W_8fc84.
Proof. vm_refl. Qed.
Lemma D_8fc84 : decode_any W_8fc84 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4048%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc88 : bv 32 := @BV 32 0x02113423%Z I.
Lemma F_8fc88 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fc88%Z I : word) = Some W_8fc88.
Proof. vm_refl. Qed.
Lemma D_8fc88 : decode_any W_8fc88 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc8c : bv 32 := @BV 32 0x02813023%Z I.
Lemma F_8fc8c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fc8c%Z I : word) = Some W_8fc8c.
Proof. vm_refl. Qed.
Lemma D_8fc8c : decode_any W_8fc8c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc90 : bv 32 := @BV 32 0x00913c23%Z I.
Lemma F_8fc90 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fc90%Z I : word) = Some W_8fc90.
Proof. vm_refl. Qed.
Lemma D_8fc90 : decode_any W_8fc90 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc94 : bv 32 := @BV 32 0x01213823%Z I.
Lemma F_8fc94 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fc94%Z I : word) = Some W_8fc94.
Proof. vm_refl. Qed.
Lemma D_8fc94 : decode_any W_8fc94 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc98 : bv 32 := @BV 32 0x01313423%Z I.
Lemma F_8fc98 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fc98%Z I : word) = Some W_8fc98.
Proof. vm_refl. Qed.
Lemma D_8fc98 : decode_any W_8fc98 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 19%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fc9c : bv 32 := @BV 32 0x00050413%Z I.
Lemma F_8fc9c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fc9c%Z I : word) = Some W_8fc9c.
Proof. vm_refl. Qed.
Lemma D_8fc9c : decode_any W_8fc9c = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fca0 : bv 32 := @BV 32 0x00000593%Z I.
Lemma F_8fca0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fca0%Z I : word) = Some W_8fca0.
Proof. vm_refl. Qed.
Lemma D_8fca0 : decode_any W_8fca0 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fca4 : bv 32 := @BV 32 0x800004b7%Z I.
Lemma F_8fca4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fca4%Z I : word) = Some W_8fca4.
Proof. vm_refl. Qed.
Lemma D_8fca4 : decode_any W_8fca4 = Some (Lui (@BV 5 9%Z I) (@BV 20 524288%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fca8 : bv 32 := @BV 32 0x00900913%Z I.
Lemma F_8fca8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fca8%Z I : word) = Some W_8fca8.
Proof. vm_refl. Qed.
Lemma D_8fca8 : decode_any W_8fca8 = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 0%Z I) (@BV 12 9%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fcac : bv 32 := @BV 32 0x00052503%Z I.
Lemma F_8fcac : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fcac%Z I : word) = Some W_8fcac.
Proof. vm_refl. Qed.
Lemma D_8fcac : decode_any W_8fcac = Some (Load SZ4 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fcb0 : bv 32 := @BV 32 0x00055a63%Z I.
Lemma F_8fcb0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fcb0%Z I : word) = Some W_8fcb0.
Proof. vm_refl. Qed.
Lemma D_8fcb0 : decode_any W_8fcb0 = Some (Branch BC_GE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fcc4 : bv 32 := @BV 32 0x00956633%Z I.
Lemma F_8fcc4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fcc4%Z I : word) = Some W_8fcc4.
Proof. vm_refl. Qed.
Lemma D_8fcc4 : decode_any W_8fcc4 = Some (Op ALU_OR (@BV 5 12%Z I) (@BV 5 10%Z I) (@BV 5 9%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fcc8 : bv 32 := @BV 32 0x160426af%Z I.
Lemma F_8fcc8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fcc8%Z I : word) = Some W_8fcc8.
Proof. vm_refl. Qed.
Lemma D_8fcc8 : decode_any W_8fcc8 = Some (Lr AW true true (@BV 5 13%Z I) (@BV 5 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fccc : bv 32 := @BV 32 0x00a69663%Z I.
Lemma F_8fccc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fccc%Z I : word) = Some W_8fccc.
Proof. vm_refl. Qed.
Lemma D_8fccc : decode_any W_8fccc = Some (Branch BC_NE (@BV 5 13%Z I) (@BV 5 10%Z I) (@BV 13 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fcd0 : bv 32 := @BV 32 0x1ac4272f%Z I.
Lemma F_8fcd0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fcd0%Z I : word) = Some W_8fcd0.
Proof. vm_refl. Qed.
Lemma D_8fcd0 : decode_any W_8fcd0 = Some (Sc AW false true (@BV 5 14%Z I) (@BV 5 8%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fcd4 : bv 32 := @BV 32 0xfe071ae3%Z I.
Lemma F_8fcd4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fcd4%Z I : word) = Some W_8fcd4.
Proof. vm_refl. Qed.
Lemma D_8fcd4 : decode_any W_8fcd4 = Some (Branch BC_NE (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 13 8180%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fcd8 : bv 32 := @BV 32 0x02a68063%Z I.
Lemma F_8fcd8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fcd8%Z I : word) = Some W_8fcd8.
Proof. vm_refl. Qed.
Lemma D_8fcd8 : decode_any W_8fcd8 = Some (Branch BC_EQ (@BV 5 13%Z I) (@BV 5 10%Z I) (@BV 13 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fcf8 : bv 32 := @BV 32 0x02813083%Z I.
Lemma F_8fcf8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fcf8%Z I : word) = Some W_8fcf8.
Proof. vm_refl. Qed.
Lemma D_8fcf8 : decode_any W_8fcf8 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fcfc : bv 32 := @BV 32 0x02013403%Z I.
Lemma F_8fcfc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fcfc%Z I : word) = Some W_8fcfc.
Proof. vm_refl. Qed.
Lemma D_8fcfc : decode_any W_8fcfc = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd00 : bv 32 := @BV 32 0x01813483%Z I.
Lemma F_8fd00 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd00%Z I : word) = Some W_8fd00.
Proof. vm_refl. Qed.
Lemma D_8fd00 : decode_any W_8fd00 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd04 : bv 32 := @BV 32 0x01013903%Z I.
Lemma F_8fd04 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd04%Z I : word) = Some W_8fd04.
Proof. vm_refl. Qed.
Lemma D_8fd04 : decode_any W_8fd04 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd08 : bv 32 := @BV 32 0x00813983%Z I.
Lemma F_8fd08 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd08%Z I : word) = Some W_8fd08.
Proof. vm_refl. Qed.
Lemma D_8fd08 : decode_any W_8fd08 = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd0c : bv 32 := @BV 32 0x03010113%Z I.
Lemma F_8fd0c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd0c%Z I : word) = Some W_8fd0c.
Proof. vm_refl. Qed.
Lemma D_8fd0c : decode_any W_8fd0c = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd10 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_8fd10 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd10%Z I : word) = Some W_8fd10.
Proof. vm_refl. Qed.
Lemma D_8fd10 : decode_any W_8fd10 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd14 : bv 32 := @BV 32 0xfe010113%Z I.
Lemma F_8fd14 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd14%Z I : word) = Some W_8fd14.
Proof. vm_refl. Qed.
Lemma D_8fd14 : decode_any W_8fd14 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4064%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd18 : bv 32 := @BV 32 0x00113c23%Z I.
Lemma F_8fd18 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd18%Z I : word) = Some W_8fd18.
Proof. vm_refl. Qed.
Lemma D_8fd18 : decode_any W_8fd18 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd1c : bv 32 := @BV 32 0x00813823%Z I.
Lemma F_8fd1c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd1c%Z I : word) = Some W_8fd1c.
Proof. vm_refl. Qed.
Lemma D_8fd1c : decode_any W_8fd1c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd20 : bv 32 := @BV 32 0x00913423%Z I.
Lemma F_8fd20 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd20%Z I : word) = Some W_8fd20.
Proof. vm_refl. Qed.
Lemma D_8fd20 : decode_any W_8fd20 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd24 : bv 32 := @BV 32 0x01213023%Z I.
Lemma F_8fd24 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd24%Z I : word) = Some W_8fd24.
Proof. vm_refl. Qed.
Lemma D_8fd24 : decode_any W_8fd24 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd28 : bv 32 := @BV 32 0x00050413%Z I.
Lemma F_8fd28 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd28%Z I : word) = Some W_8fd28.
Proof. vm_refl. Qed.
Lemma D_8fd28 : decode_any W_8fd28 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd2c : bv 32 := @BV 32 0xffc57513%Z I.
Lemma F_8fd2c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd2c%Z I : word) = Some W_8fd2c.
Proof. vm_refl. Qed.
Lemma D_8fd2c : decode_any W_8fd2c = Some (OpImm ALU_AND (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 4092%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd30 : bv 32 := @BV 32 0x0ff00613%Z I.
Lemma F_8fd30 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd30%Z I : word) = Some W_8fd30.
Proof. vm_refl. Qed.
Lemma D_8fd30 : decode_any W_8fd30 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 255%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd34 : bv 32 := @BV 32 0x00100693%Z I.
Lemma F_8fd34 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd34%Z I : word) = Some W_8fd34.
Proof. vm_refl. Qed.
Lemma D_8fd34 : decode_any W_8fd34 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd38 : bv 32 := @BV 32 0x1405272f%Z I.
Lemma F_8fd38 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd38%Z I : word) = Some W_8fd38.
Proof. vm_refl. Qed.
Lemma D_8fd38 : decode_any W_8fd38 = Some (Lr AW true false (@BV 5 14%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd3c : bv 32 := @BV 32 0x00068793%Z I.
Lemma F_8fd3c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd3c%Z I : word) = Some W_8fd3c.
Proof. vm_refl. Qed.
Lemma D_8fd3c : decode_any W_8fd3c = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd40 : bv 32 := @BV 32 0x00f747b3%Z I.
Lemma F_8fd40 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd40%Z I : word) = Some W_8fd40.
Proof. vm_refl. Qed.
Lemma D_8fd40 : decode_any W_8fd40 = Some (Op ALU_XOR (@BV 5 15%Z I) (@BV 5 14%Z I) (@BV 5 15%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd44 : bv 32 := @BV 32 0x00c7f7b3%Z I.
Lemma F_8fd44 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd44%Z I : word) = Some W_8fd44.
Proof. vm_refl. Qed.
Lemma D_8fd44 : decode_any W_8fd44 = Some (Op ALU_AND (@BV 5 15%Z I) (@BV 5 15%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd48 : bv 32 := @BV 32 0x00f747b3%Z I.
Lemma F_8fd48 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd48%Z I : word) = Some W_8fd48.
Proof. vm_refl. Qed.
Lemma D_8fd48 : decode_any W_8fd48 = Some (Op ALU_XOR (@BV 5 15%Z I) (@BV 5 14%Z I) (@BV 5 15%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd4c : bv 32 := @BV 32 0x18f527af%Z I.
Lemma F_8fd4c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd4c%Z I : word) = Some W_8fd4c.
Proof. vm_refl. Qed.
Lemma D_8fd4c : decode_any W_8fd4c = Some (Sc AW false false (@BV 5 15%Z I) (@BV 5 10%Z I) (@BV 5 15%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd50 : bv 32 := @BV 32 0xfe0794e3%Z I.
Lemma F_8fd50 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd50%Z I : word) = Some W_8fd50.
Proof. vm_refl. Qed.
Lemma D_8fd50 : decode_any W_8fd50 = Some (Branch BC_NE (@BV 5 15%Z I) (@BV 5 0%Z I) (@BV 13 8168%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd54 : bv 32 := @BV 32 0x0ff77513%Z I.
Lemma F_8fd54 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd54%Z I : word) = Some W_8fd54.
Proof. vm_refl. Qed.
Lemma D_8fd54 : decode_any W_8fd54 = Some (OpImm ALU_AND (@BV 5 10%Z I) (@BV 5 14%Z I) (@BV 12 255%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd58 : bv 32 := @BV 32 0x08051463%Z I.
Lemma F_8fd58 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd58%Z I : word) = Some W_8fd58.
Proof. vm_refl. Qed.
Lemma D_8fd58 : decode_any W_8fd58 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 136%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd5c : bv 32 := @BV 32 0x00359593%Z I.
Lemma F_8fd5c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd5c%Z I : word) = Some W_8fd5c.
Proof. vm_refl. Qed.
Lemma D_8fd5c : decode_any W_8fd5c = Some (ShiftImm ALU_SLL (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 6 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd60 : bv 32 := @BV 32 0x00b404b3%Z I.
Lemma F_8fd60 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd60%Z I : word) = Some W_8fd60.
Proof. vm_refl. Qed.
Lemma D_8fd60 : decode_any W_8fd60 = Some (Op ALU_ADD (@BV 5 9%Z I) (@BV 5 8%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd64 : bv 32 := @BV 32 0x0084b503%Z I.
Lemma F_8fd64 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd64%Z I : word) = Some W_8fd64.
Proof. vm_refl. Qed.
Lemma D_8fd64 : decode_any W_8fd64 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd68 : bv 32 := @BV 32 0x0230000f%Z I.
Lemma F_8fd68 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd68%Z I : word) = Some W_8fd68.
Proof. vm_refl. Qed.
Lemma D_8fd68 : decode_any W_8fd68 = Some (Fence (@BV 4 0%Z I) (@BV 4 2%Z I) (@BV 4 3%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd6c : bv 32 := @BV 32 0x04051a63%Z I.
Lemma F_8fd6c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd6c%Z I : word) = Some W_8fd6c.
Proof. vm_refl. Qed.
Lemma D_8fd6c : decode_any W_8fd6c = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 84%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd70 : bv 32 := @BV 32 0x00076517%Z I.
Lemma F_8fd70 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd70%Z I : word) = Some W_8fd70.
Proof. vm_refl. Qed.
Lemma D_8fd70 : decode_any W_8fd70 = Some (Auipc (@BV 5 10%Z I) (@BV 20 118%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd74 : bv 32 := @BV 32 0x18853903%Z I.
Lemma F_8fd74 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd74%Z I : word) = Some W_8fd74.
Proof. vm_refl. Qed.
Lemma D_8fd74 : decode_any W_8fd74 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 10%Z I) (@BV 12 392%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd78 : bv 32 := @BV 32 0x00093503%Z I.
Lemma F_8fd78 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd78%Z I : word) = Some W_8fd78.
Proof. vm_refl. Qed.
Lemma D_8fd78 : decode_any W_8fd78 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd7c : bv 32 := @BV 32 0x00051663%Z I.
Lemma F_8fd7c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd7c%Z I : word) = Some W_8fd7c.
Proof. vm_refl. Qed.
Lemma D_8fd7c : decode_any W_8fd7c = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd88 : bv 32 := @BV 32 0xfff50593%Z I.
Lemma F_8fd88 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd88%Z I : word) = Some W_8fd88.
Proof. vm_refl. Qed.
Lemma D_8fd88 : decode_any W_8fd88 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd8c : bv 32 := @BV 32 0x00b575b3%Z I.
Lemma F_8fd8c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd8c%Z I : word) = Some W_8fd8c.
Proof. vm_refl. Qed.
Lemma D_8fd8c : decode_any W_8fd8c = Some (Op ALU_AND (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd90 : bv 32 := @BV 32 0x06059a63%Z I.
Lemma F_8fd90 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd90%Z I : word) = Some W_8fd90.
Proof. vm_refl. Qed.
Lemma D_8fd90 : decode_any W_8fd90 = Some (Branch BC_NE (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 116%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd94 : bv 32 := @BV 32 0x001005b7%Z I.
Lemma F_8fd94 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd94%Z I : word) = Some W_8fd94.
Proof. vm_refl. Qed.
Lemma D_8fd94 : decode_any W_8fd94 = Some (Lui (@BV 5 11%Z I) (@BV 20 256%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd98 : bv 32 := @BV 32 0xfff5859b%Z I.
Lemma F_8fd98 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd98%Z I : word) = Some W_8fd98.
Proof. vm_refl. Qed.
Lemma D_8fd98 : decode_any W_8fd98 = Some (OpImm32 (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fd9c : bv 32 := @BV 32 0x00b505b3%Z I.
Lemma F_8fd9c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fd9c%Z I : word) = Some W_8fd9c.
Proof. vm_refl. Qed.
Lemma D_8fd9c : decode_any W_8fd9c = Some (Op ALU_ADD (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fda0 : bv 32 := @BV 32 0x40a00533%Z I.
Lemma F_8fda0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fda0%Z I : word) = Some W_8fda0.
Proof. vm_refl. Qed.
Lemma D_8fda0 : decode_any W_8fda0 = Some (Op ALU_SUB (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fda4 : bv 32 := @BV 32 0x00a5f533%Z I.
Lemma F_8fda4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fda4%Z I : word) = Some W_8fda4.
Proof. vm_refl. Qed.
Lemma D_8fda4 : decode_any W_8fda4 = Some (Op ALU_AND (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fda8 : bv 32 := @BV 32 0xfff92597%Z I.
Lemma F_8fda8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fda8%Z I : word) = Some W_8fda8.
Proof. vm_refl. Qed.
Lemma D_8fda8 : decode_any W_8fda8 = Some (Auipc (@BV 5 11%Z I) (@BV 20 1048466%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fdac : bv 32 := @BV 32 0xfdb58593%Z I.
Lemma F_8fdac : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fdac%Z I : word) = Some W_8fdac.
Proof. vm_refl. Qed.
Lemma D_8fdac : decode_any W_8fdac = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 4059%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fdb0 : bv 32 := @BV 32 0x00000613%Z I.
Lemma F_8fdb0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fdb0%Z I : word) = Some W_8fdb0.
Proof. vm_refl. Qed.
Lemma D_8fdb0 : decode_any W_8fdb0 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fdb4 : bv 32 := @BV 32 0xac5f20ef%Z I.
Lemma F_8fdb4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fdb4%Z I : word) = Some W_8fdb4.
Proof. vm_refl. Qed.
Lemma D_8fdb4 : decode_any W_8fdb4 = Some (Jal (@BV 5 1%Z I) (@BV 21 2042564%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fdb8 : bv 32 := @BV 32 0x0310000f%Z I.
Lemma F_8fdb8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fdb8%Z I : word) = Some W_8fdb8.
Proof. vm_refl. Qed.
Lemma D_8fdb8 : decode_any W_8fdb8 = Some (Fence (@BV 4 0%Z I) (@BV 4 3%Z I) (@BV 4 1%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fdbc : bv 32 := @BV 32 0x00a4b423%Z I.
Lemma F_8fdbc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fdbc%Z I : word) = Some W_8fdbc.
Proof. vm_refl. Qed.
Lemma D_8fdbc : decode_any W_8fdbc = Some (Store SZ8 (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fdc0 : bv 32 := @BV 32 0x0310000f%Z I.
Lemma F_8fdc0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fdc0%Z I : word) = Some W_8fdc0.
Proof. vm_refl. Qed.
Lemma D_8fdc0 : decode_any W_8fdc0 = Some (Fence (@BV 4 0%Z I) (@BV 4 3%Z I) (@BV 4 1%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fdc4 : bv 32 := @BV 32 0x00040023%Z I.
Lemma F_8fdc4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fdc4%Z I : word) = Some W_8fdc4.
Proof. vm_refl. Qed.
Lemma D_8fdc4 : decode_any W_8fdc4 = Some (Store SZ1 (@BV 5 8%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fdc8 : bv 32 := @BV 32 0x01813083%Z I.
Lemma F_8fdc8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fdc8%Z I : word) = Some W_8fdc8.
Proof. vm_refl. Qed.
Lemma D_8fdc8 : decode_any W_8fdc8 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fdcc : bv 32 := @BV 32 0x01013403%Z I.
Lemma F_8fdcc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fdcc%Z I : word) = Some W_8fdcc.
Proof. vm_refl. Qed.
Lemma D_8fdcc : decode_any W_8fdcc = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fdd0 : bv 32 := @BV 32 0x00813483%Z I.
Lemma F_8fdd0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fdd0%Z I : word) = Some W_8fdd0.
Proof. vm_refl. Qed.
Lemma D_8fdd0 : decode_any W_8fdd0 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fdd4 : bv 32 := @BV 32 0x00013903%Z I.
Lemma F_8fdd4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fdd4%Z I : word) = Some W_8fdd4.
Proof. vm_refl. Qed.
Lemma D_8fdd4 : decode_any W_8fdd4 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fdd8 : bv 32 := @BV 32 0x02010113%Z I.
Lemma F_8fdd8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fdd8%Z I : word) = Some W_8fdd8.
Proof. vm_refl. Qed.
Lemma D_8fdd8 : decode_any W_8fdd8 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fddc : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_8fddc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fddc%Z I : word) = Some W_8fddc.
Proof. vm_refl. Qed.
Lemma D_8fddc : decode_any W_8fddc = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fe74 : bv 32 := @BV 32 0x00008513%Z I.
Lemma F_8fe74 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fe74%Z I : word) = Some W_8fe74.
Proof. vm_refl. Qed.
Lemma D_8fe74 : decode_any W_8fe74 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fe78 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_8fe78 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8fe78%Z I : word) = Some W_8fe78.
Proof. vm_refl. Qed.
Lemma D_8fe78 : decode_any W_8fe78 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fe7c : bv 32 := @BV 32 0xfc010113%Z I.

Lemma D_8fe7c : decode_any W_8fe7c = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4032%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fe80 : bv 32 := @BV 32 0x02113c23%Z I.

Lemma D_8fe80 : decode_any W_8fe80 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fe84 : bv 32 := @BV 32 0x02813823%Z I.

Lemma D_8fe84 : decode_any W_8fe84 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fe88 : bv 32 := @BV 32 0x02913423%Z I.

Lemma D_8fe88 : decode_any W_8fe88 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fe8c : bv 32 := @BV 32 0x03213023%Z I.

Lemma D_8fe8c : decode_any W_8fe8c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fe90 : bv 32 := @BV 32 0x01313c23%Z I.

Lemma D_8fe90 : decode_any W_8fe90 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 19%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fe94 : bv 32 := @BV 32 0x01413823%Z I.

Lemma D_8fe94 : decode_any W_8fe94 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 20%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fe98 : bv 32 := @BV 32 0x01513423%Z I.

Lemma D_8fe98 : decode_any W_8fe98 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 21%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fe9c : bv 32 := @BV 32 0x01613023%Z I.

Lemma D_8fe9c : decode_any W_8fe9c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 22%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fea0 : bv 32 := @BV 32 0x00068493%Z I.

Lemma D_8fea0 : decode_any W_8fea0 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fea4 : bv 32 := @BV 32 0x02079413%Z I.

Lemma D_8fea4 : decode_any W_8fea4 = Some (ShiftImm ALU_SLL (@BV 5 8%Z I) (@BV 5 15%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fea8 : bv 32 := @BV 32 0x00100693%Z I.

Lemma D_8fea8 : decode_any W_8fea8 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8feac : bv 32 := @BV 32 0x02045413%Z I.

Lemma D_8feac : decode_any W_8feac = Some (ShiftImm ALU_SRL (@BV 5 8%Z I) (@BV 5 8%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8feb0 : bv 32 := @BV 32 0x0ef6f863%Z I.

Lemma D_8feb0 : decode_any W_8feb0 = Some (Branch BC_GEU (@BV 5 13%Z I) (@BV 5 15%Z I) (@BV 13 240%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8feb4 : bv 32 := @BV 32 0x00076697%Z I.
Lemma F_8feb4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8feb4%Z I : word) = Some W_8feb4.
Proof. vm_refl. Qed.
Lemma D_8feb4 : decode_any W_8feb4 = Some (Auipc (@BV 5 13%Z I) (@BV 20 118%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8feb8 : bv 32 := @BV 32 0x0446b903%Z I.
Lemma F_8feb8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8feb8%Z I : word) = Some W_8feb8.
Proof. vm_refl. Qed.
Lemma D_8feb8 : decode_any W_8feb8 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 13%Z I) (@BV 12 68%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8febc : bv 32 := @BV 32 0x00093683%Z I.

Lemma D_8febc : decode_any W_8febc = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fec0 : bv 32 := @BV 32 0x00068e63%Z I.

Lemma D_8fec0 : decode_any W_8fec0 = Some (Branch BC_EQ (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 13 28%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fec4 : bv 32 := @BV 32 0x00100793%Z I.

Lemma D_8fec4 : decode_any W_8fec4 = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fec8 : bv 32 := @BV 32 0x00c4d813%Z I.

Lemma D_8fec8 : decode_any W_8fec8 = Some (ShiftImm ALU_SRL (@BV 5 16%Z I) (@BV 5 9%Z I) (@BV 6 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fecc : bv 32 := @BV 32 0x00f52423%Z I.

Lemma D_8fecc : decode_any W_8fecc = Some (Store SZ4 (@BV 5 10%Z I) (@BV 5 15%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fed0 : bv 32 := @BV 32 0x00b53823%Z I.

Lemma D_8fed0 : decode_any W_8fed0 = Some (Store SZ8 (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fed4 : bv 32 := @BV 32 0x04081463%Z I.

Lemma D_8fed4 : decode_any W_8fed4 = Some (Branch BC_NE (@BV 5 16%Z I) (@BV 5 0%Z I) (@BV 13 72%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8fed8 : bv 32 := @BV 32 0x0a00006f%Z I.



(* [comment removed for export] *)
Definition W_8fedc : bv 32 := @BV 32 0x00058a13%Z I.



(* [comment removed for export] *)
Definition W_8fee0 : bv 32 := @BV 32 0x00050993%Z I.



(* [comment removed for export] *)
Definition W_8fee4 : bv 32 := @BV 32 0x00060a93%Z I.



(* [comment removed for export] *)
Definition W_8fee8 : bv 32 := @BV 32 0x00070b13%Z I.



(* [comment removed for export] *)
Definition W_8feec : bv 32 := @BV 32 0x9e8f20ef%Z I.



(* [comment removed for export] *)
Definition W_8fef0 : bv 32 := @BV 32 0x000b0713%Z I.



(* [comment removed for export] *)
Definition W_8fef4 : bv 32 := @BV 32 0x000a8613%Z I.



(* [comment removed for export] *)
Definition W_8fef8 : bv 32 := @BV 32 0x000a0593%Z I.



(* [comment removed for export] *)
Definition W_8fefc : bv 32 := @BV 32 0x00050693%Z I.



(* [comment removed for export] *)
Definition W_8ff00 : bv 32 := @BV 32 0x00098513%Z I.



(* [comment removed for export] *)
Definition W_8ff04 : bv 32 := @BV 32 0x00d93023%Z I.



(* [comment removed for export] *)
Definition W_8ff08 : bv 32 := @BV 32 0x00100793%Z I.



(* [comment removed for export] *)
Definition W_8ff0c : bv 32 := @BV 32 0x00c4d813%Z I.



(* [comment removed for export] *)
Definition W_8ff10 : bv 32 := @BV 32 0x00f9a423%Z I.



(* [comment removed for export] *)
Definition W_8ff14 : bv 32 := @BV 32 0x0149b823%Z I.



(* [comment removed for export] *)
Definition W_8ff18 : bv 32 := @BV 32 0x06080063%Z I.



(* [comment removed for export] *)
Definition W_8ff1c : bv 32 := @BV 32 0x0a977263%Z I.

Lemma D_8ff1c : decode_any W_8ff1c = Some (Branch BC_GEU (@BV 5 14%Z I) (@BV 5 9%Z I) (@BV 13 164%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff20 : bv 32 := @BV 32 0x04c77c63%Z I.

Lemma D_8ff20 : decode_any W_8ff20 = Some (Branch BC_GEU (@BV 5 14%Z I) (@BV 5 12%Z I) (@BV 13 88%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff24 : bv 32 := @BV 32 0xff048493%Z I.

Lemma D_8ff24 : decode_any W_8ff24 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 9%Z I) (@BV 12 4080%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff28 : bv 32 := @BV 32 0x04967863%Z I.

Lemma D_8ff28 : decode_any W_8ff28 = Some (Branch BC_GEU (@BV 5 12%Z I) (@BV 5 9%Z I) (@BV 13 80%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff2c : bv 32 := @BV 32 0x00767713%Z I.

Lemma D_8ff2c : decode_any W_8ff2c = Some (OpImm ALU_AND (@BV 5 14%Z I) (@BV 5 12%Z I) (@BV 12 7%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff30 : bv 32 := @BV 32 0x04071463%Z I.

Lemma D_8ff30 : decode_any W_8ff30 = Some (Branch BC_NE (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 13 72%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff34 : bv 32 := @BV 32 0x01050713%Z I.

Lemma D_8ff34 : decode_any W_8ff34 = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 10%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff38 : bv 32 := @BV 32 0x00100793%Z I.

Lemma D_8ff38 : decode_any W_8ff38 = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff3c : bv 32 := @BV 32 0x0287fe63%Z I.

Lemma D_8ff3c : decode_any W_8ff3c = Some (Branch BC_GEU (@BV 5 15%Z I) (@BV 5 8%Z I) (@BV 13 60%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff40 : bv 32 := @BV 32 0xff863803%Z I.

Lemma D_8ff40 : decode_any W_8ff40 = Some (Load SZ8 true (@BV 5 16%Z I) (@BV 5 12%Z I) (@BV 12 4088%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff44 : bv 32 := @BV 32 0x02d86a63%Z I.

Lemma D_8ff44 : decode_any W_8ff44 = Some (Branch BC_LTU (@BV 5 16%Z I) (@BV 5 13%Z I) (@BV 13 52%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff48 : bv 32 := @BV 32 0x00b80c63%Z I.

Lemma D_8ff48 : decode_any W_8ff48 = Some (Branch BC_EQ (@BV 5 16%Z I) (@BV 5 11%Z I) (@BV 13 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff4c : bv 32 := @BV 32 0x00379893%Z I.

Lemma D_8ff4c : decode_any W_8ff4c = Some (ShiftImm ALU_SLL (@BV 5 17%Z I) (@BV 5 15%Z I) (@BV 6 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff50 : bv 32 := @BV 32 0x00178793%Z I.

Lemma D_8ff50 : decode_any W_8ff50 = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 15%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff54 : bv 32 := @BV 32 0x011708b3%Z I.

Lemma D_8ff54 : decode_any W_8ff54 = Some (Op ALU_ADD (@BV 5 17%Z I) (@BV 5 14%Z I) (@BV 5 17%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff58 : bv 32 := @BV 32 0x00f52423%Z I.

Lemma D_8ff58 : decode_any W_8ff58 = Some (Store SZ4 (@BV 5 10%Z I) (@BV 5 15%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff5c : bv 32 := @BV 32 0x0108b023%Z I.

Lemma D_8ff5c : decode_any W_8ff5c = Some (Store SZ8 (@BV 5 17%Z I) (@BV 5 16%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff60 : bv 32 := @BV 32 0xff063803%Z I.

Lemma D_8ff60 : decode_any W_8ff60 = Some (Load SZ8 true (@BV 5 16%Z I) (@BV 5 12%Z I) (@BV 12 4080%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff64 : bv 32 := @BV 32 0x01067a63%Z I.

Lemma D_8ff64 : decode_any W_8ff64 = Some (Branch BC_GEU (@BV 5 12%Z I) (@BV 5 16%Z I) (@BV 13 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff68 : bv 32 := @BV 32 0x00987863%Z I.

Lemma D_8ff68 : decode_any W_8ff68 = Some (Branch BC_GEU (@BV 5 16%Z I) (@BV 5 9%Z I) (@BV 13 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff6c : bv 32 := @BV 32 0x00787893%Z I.

Lemma D_8ff6c : decode_any W_8ff6c = Some (OpImm ALU_AND (@BV 5 17%Z I) (@BV 5 16%Z I) (@BV 12 7%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff70 : bv 32 := @BV 32 0x00080613%Z I.

Lemma D_8ff70 : decode_any W_8ff70 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 16%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff74 : bv 32 := @BV 32 0xfc0884e3%Z I.

Lemma D_8ff74 : decode_any W_8ff74 = Some (Branch BC_EQ (@BV 5 17%Z I) (@BV 5 0%Z I) (@BV 13 8136%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff78 : bv 32 := @BV 32 0x03813083%Z I.

Lemma D_8ff78 : decode_any W_8ff78 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff7c : bv 32 := @BV 32 0x03013403%Z I.

Lemma D_8ff7c : decode_any W_8ff7c = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff80 : bv 32 := @BV 32 0x02813483%Z I.

Lemma D_8ff80 : decode_any W_8ff80 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff84 : bv 32 := @BV 32 0x02013903%Z I.

Lemma D_8ff84 : decode_any W_8ff84 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff88 : bv 32 := @BV 32 0x01813983%Z I.

Lemma D_8ff88 : decode_any W_8ff88 = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff8c : bv 32 := @BV 32 0x01013a03%Z I.

Lemma D_8ff8c : decode_any W_8ff8c = Some (Load SZ8 true (@BV 5 20%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff90 : bv 32 := @BV 32 0x00813a83%Z I.

Lemma D_8ff90 : decode_any W_8ff90 = Some (Load SZ8 true (@BV 5 21%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff94 : bv 32 := @BV 32 0x00013b03%Z I.

Lemma D_8ff94 : decode_any W_8ff94 = Some (Load SZ8 true (@BV 5 22%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff98 : bv 32 := @BV 32 0x04010113%Z I.

Lemma D_8ff98 : decode_any W_8ff98 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ff9c : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_8ff9c : decode_any W_8ff9c = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_904d8 : bv 32 := @BV 32 0xfc010113%Z I.

Lemma D_904d8 : decode_any W_904d8 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4032%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_904dc : bv 32 := @BV 32 0x02113c23%Z I.

Lemma D_904dc : decode_any W_904dc = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_904e0 : bv 32 := @BV 32 0x02813823%Z I.

Lemma D_904e0 : decode_any W_904e0 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_904e4 : bv 32 := @BV 32 0x02913423%Z I.

Lemma D_904e4 : decode_any W_904e4 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_904e8 : bv 32 := @BV 32 0x03213023%Z I.

Lemma D_904e8 : decode_any W_904e8 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_904ec : bv 32 := @BV 32 0x01313c23%Z I.

Lemma D_904ec : decode_any W_904ec = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 19%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_904f0 : bv 32 := @BV 32 0x01413823%Z I.

Lemma D_904f0 : decode_any W_904f0 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 20%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_904f4 : bv 32 := @BV 32 0x01513423%Z I.

Lemma D_904f4 : decode_any W_904f4 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 21%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_904f8 : bv 32 := @BV 32 0x00058413%Z I.

Lemma D_904f8 : decode_any W_904f8 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_904fc : bv 32 := @BV 32 0x0015b593%Z I.

Lemma D_904fc : decode_any W_904fc = Some (OpImm ALU_SLTU (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90500 : bv 32 := @BV 32 0x7ff50293%Z I.

Lemma D_90500 : decode_any W_90500 = Some (OpImm ALU_ADD (@BV 5 5%Z I) (@BV 5 10%Z I) (@BV 12 2047%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90504 : bv 32 := @BV 32 0xfff58593%Z I.

Lemma D_90504 : decode_any W_90504 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90508 : bv 32 := @BV 32 0x00d5f333%Z I.

Lemma D_90508 : decode_any W_90508 = Some (Op ALU_AND (@BV 5 6%Z I) (@BV 5 11%Z I) (@BV 5 13%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9050c : bv 32 := @BV 32 0x00100593%Z I.

Lemma D_9050c : decode_any W_9050c = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90510 : bv 32 := @BV 32 0x0062b4a3%Z I.

Lemma D_90510 : decode_any W_90510 = Some (Store SZ8 (@BV 5 5%Z I) (@BV 5 6%Z I) (@BV 12 9%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90514 : bv 32 := @BV 32 0x00b40863%Z I.

Lemma D_90514 : decode_any W_90514 = Some (Branch BC_EQ (@BV 5 8%Z I) (@BV 5 11%Z I) (@BV 13 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90518 : bv 32 := @BV 32 0x02041c63%Z I.

Lemma D_90518 : decode_any W_90518 = Some (Branch BC_NE (@BV 5 8%Z I) (@BV 5 0%Z I) (@BV 13 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9051c : bv 32 := @BV 32 0x00052423%Z I.



(* [comment removed for export] *)
Definition W_90520 : bv 32 := @BV 32 0x00c0006f%Z I.



(* [comment removed for export] *)
Definition W_90524 : bv 32 := @BV 32 0x00b52423%Z I.



(* [comment removed for export] *)
Definition W_90528 : bv 32 := @BV 32 0x00c53823%Z I.



(* [comment removed for export] *)
Definition W_9052c : bv 32 := @BV 32 0x03813083%Z I.



(* [comment removed for export] *)
Definition W_90530 : bv 32 := @BV 32 0x03013403%Z I.



(* [comment removed for export] *)
Definition W_90534 : bv 32 := @BV 32 0x02813483%Z I.



(* [comment removed for export] *)
Definition W_90538 : bv 32 := @BV 32 0x02013903%Z I.



(* [comment removed for export] *)
Definition W_9053c : bv 32 := @BV 32 0x01813983%Z I.



(* [comment removed for export] *)
Definition W_90540 : bv 32 := @BV 32 0x01013a03%Z I.



(* [comment removed for export] *)
Definition W_90544 : bv 32 := @BV 32 0x00813a83%Z I.



(* [comment removed for export] *)
Definition W_90548 : bv 32 := @BV 32 0x04010113%Z I.



(* [comment removed for export] *)
Definition W_9054c : bv 32 := @BV 32 0x00008067%Z I.



(* [comment removed for export] *)
Definition W_90550 : bv 32 := @BV 32 0x06089463%Z I.

Lemma D_90550 : decode_any W_90550 = Some (Branch BC_NE (@BV 5 17%Z I) (@BV 5 0%Z I) (@BV 13 104%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90554 : bv 32 := @BV 32 0x00068493%Z I.



(* [comment removed for export] *)
Definition W_90558 : bv 32 := @BV 32 0x00078913%Z I.



(* [comment removed for export] *)
Definition W_9055c : bv 32 := @BV 32 0x00080993%Z I.



(* [comment removed for export] *)
Definition W_90560 : bv 32 := @BV 32 0x00050a93%Z I.



(* [comment removed for export] *)
Definition W_90564 : bv 32 := @BV 32 0x00060a13%Z I.



(* [comment removed for export] *)
Definition W_90568 : bv 32 := @BV 32 0x00060593%Z I.



(* [comment removed for export] *)
Definition W_9056c : bv 32 := @BV 32 0x02070063%Z I.



(* [comment removed for export] *)
Definition W_90570 : bv 32 := @BV 32 0x00070613%Z I.



(* [comment removed for export] *)
Definition W_90574 : bv 32 := @BV 32 0x00040693%Z I.



(* [comment removed for export] *)
Definition W_90578 : bv 32 := @BV 32 0x45c060ef%Z I.



(* [comment removed for export] *)
Definition W_9057c : bv 32 := @BV 32 0x008aa583%Z I.



(* [comment removed for export] *)
Definition W_90580 : bv 32 := @BV 32 0x00200713%Z I.



(* [comment removed for export] *)
Definition W_90584 : bv 32 := @BV 32 0x00b77e63%Z I.



(* [comment removed for export] *)
Definition W_90588 : bv 32 := @BV 32 0xfa5ff06f%Z I.



(* [comment removed for export] *)
Definition W_9058c : bv 32 := @BV 32 0x00040613%Z I.



(* [comment removed for export] *)
Definition W_90590 : bv 32 := @BV 32 0x2b0060ef%Z I.



(* [comment removed for export] *)
Definition W_90594 : bv 32 := @BV 32 0x008aa583%Z I.



(* [comment removed for export] *)
Definition W_90598 : bv 32 := @BV 32 0x00200713%Z I.



(* [comment removed for export] *)
Definition W_9059c : bv 32 := @BV 32 0xf8b768e3%Z I.



(* [comment removed for export] *)
Definition W_905a0 : bv 32 := @BV 32 0x000a8513%Z I.



(* [comment removed for export] *)
Definition W_905a4 : bv 32 := @BV 32 0x00098813%Z I.



(* [comment removed for export] *)
Definition W_905a8 : bv 32 := @BV 32 0x00090793%Z I.



(* [comment removed for export] *)
Definition W_905ac : bv 32 := @BV 32 0x000a0613%Z I.



(* [comment removed for export] *)
Definition W_905b0 : bv 32 := @BV 32 0x00048693%Z I.



(* [comment removed for export] *)
Definition W_905b4 : bv 32 := @BV 32 0xf685fce3%Z I.



(* [comment removed for export] *)
Definition W_905b8 : bv 32 := @BV 32 0x00060593%Z I.

Lemma D_905b8 : decode_any W_905b8 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_905bc : bv 32 := @BV 32 0x00068613%Z I.

Lemma D_905bc : decode_any W_905bc = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_905c0 : bv 32 := @BV 32 0x00078693%Z I.

Lemma D_905c0 : decode_any W_905c0 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 15%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_905c4 : bv 32 := @BV 32 0x00080713%Z I.

Lemma D_905c4 : decode_any W_905c4 = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 16%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_905c8 : bv 32 := @BV 32 0x00040793%Z I.

Lemma D_905c8 : decode_any W_905c8 = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_905cc : bv 32 := @BV 32 0x03813083%Z I.

Lemma D_905cc : decode_any W_905cc = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_905d0 : bv 32 := @BV 32 0x03013403%Z I.

Lemma D_905d0 : decode_any W_905d0 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_905d4 : bv 32 := @BV 32 0x02813483%Z I.

Lemma D_905d4 : decode_any W_905d4 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_905d8 : bv 32 := @BV 32 0x02013903%Z I.

Lemma D_905d8 : decode_any W_905d8 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_905dc : bv 32 := @BV 32 0x01813983%Z I.

Lemma D_905dc : decode_any W_905dc = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_905e0 : bv 32 := @BV 32 0x01013a03%Z I.

Lemma D_905e0 : decode_any W_905e0 = Some (Load SZ8 true (@BV 5 20%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_905e4 : bv 32 := @BV 32 0x00813a83%Z I.

Lemma D_905e4 : decode_any W_905e4 = Some (Load SZ8 true (@BV 5 21%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_905e8 : bv 32 := @BV 32 0x04010113%Z I.

Lemma D_905e8 : decode_any W_905e8 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_905ec : bv 32 := @BV 32 0x891ff06f%Z I.

Lemma D_905ec : decode_any W_905ec = Some (Jal (@BV 5 0%Z I) (@BV 21 2095248%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_8fc84_905f0.
Module Bo_code_fc94c_fce54.
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
End Bo_code_fc94c_fce54.
Module Bo_code_fdbac_fdd40.
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
Definition W_fdd24 : bv 32 := @BV 32 0x00020593%Z I.

Lemma D_fdd24 : decode_any W_fdd24 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 4%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fdd28 : bv 32 := @BV 32 0xfa85b583%Z I.

Lemma D_fdd28 : decode_any W_fdd28 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 4008%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fdd2c : bv 32 := @BV 32 0x02051513%Z I.

Lemma D_fdd2c : decode_any W_fdd2c = Some (ShiftImm ALU_SLL (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fdd30 : bv 32 := @BV 32 0x01d55513%Z I.

Lemma D_fdd30 : decode_any W_fdd30 = Some (ShiftImm ALU_SRL (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 6 29%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fdd34 : bv 32 := @BV 32 0x00a58533%Z I.

Lemma D_fdd34 : decode_any W_fdd34 = Some (Op ALU_ADD (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fdd38 : bv 32 := @BV 32 0x00053503%Z I.

Lemma D_fdd38 : decode_any W_fdd38 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fdd3c : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_fdd3c : decode_any W_fdd3c = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_fdbac_fdd40.
Module Bo_code_fde90_fe69c.
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
End Bo_code_fde90_fe69c.
Module Bo_code_fe6a4_fe6b0.
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
End Bo_code_fe6a4_fe6b0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab Bo_code_70b0c_71670 Bo_code_7571c_75734 Bo_code_76b0c_77514 Bo_code_78b0c_799f4 Bo_code_8fc84_905f0 Bo_code_fc94c_fce54 Bo_code_fdbac_fdd40 Bo_code_fde90_fe69c Bo_code_fe6a4_fe6b0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

Definition uf_words : list (option (bv 32)) :=
  [
   Some W_8fe7c; Some W_8fe80; Some W_8fe84; Some W_8fe88; Some W_8fe8c; Some W_8fe90; Some W_8fe94;
   Some W_8fe98; Some W_8fe9c; Some W_8fea0; Some W_8fea4; Some W_8fea8; Some W_8feac; Some W_8feb0;
   None; None; Some W_8febc; Some W_8fec0; Some W_8fec4; Some W_8fec8; Some W_8fecc; Some W_8fed0;
   Some W_8fed4; Some W_8fed8; Some W_8fedc; Some W_8fee0; Some W_8fee4; Some W_8fee8; Some W_8feec;
   Some W_8fef0; Some W_8fef4; Some W_8fef8; Some W_8fefc; Some W_8ff00; Some W_8ff04; Some W_8ff08;
   Some W_8ff0c; Some W_8ff10; Some W_8ff14; Some W_8ff18; Some W_8ff1c; Some W_8ff20; Some W_8ff24;
   Some W_8ff28; Some W_8ff2c; Some W_8ff30; Some W_8ff34; Some W_8ff38; Some W_8ff3c; Some W_8ff40;
   Some W_8ff44; Some W_8ff48; Some W_8ff4c; Some W_8ff50; Some W_8ff54; Some W_8ff58; Some W_8ff5c;
   Some W_8ff60; Some W_8ff64; Some W_8ff68; Some W_8ff6c; Some W_8ff70; Some W_8ff74; Some W_8ff78;
   Some W_8ff7c; Some W_8ff80; Some W_8ff84; Some W_8ff88; Some W_8ff8c; Some W_8ff90; Some W_8ff94;
   Some W_8ff98; Some W_8ff9c
  ]%list.

(* [comment removed for export] *)
Definition uf_clob : list reg := [12; 13; 14; 15; 16; 17].
(* [comment removed for export] *)
Definition uf_clobx : list reg := [2; 8; 9; 18; 19; 20; 21; 22; 12; 13; 14; 15; 16; 17].

(* [comment removed for export] *)
Record uf_tab := UFT { uf_base : word; uf_g_pgsz : Z }.
Record uf_tab_ok (segs : list Segment) (t : uf_tab) : Prop := UFTOK {
  ufo_code : code_ato segs (uf_base t) 0 uf_words;
  ufo_g56 : gload2 segs (uf_base t) 56 13 18 (uf_g_pgsz t) }.

Section UF.
  Variable segs : list Segment.
  Variable base : word.
  Variable g_pgsz : Z.
  Hypothesis HCODE : code_ato segs base 0 uf_words.
  Hypothesis G56 : gload2 segs base 56 13 18 g_pgsz.

  Lemma Fo0 : fetch_word segs (at_ base 0) = Some W_8fe7c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 0 _ HCODE eq_refl). Qed.
  Lemma Fo4 : fetch_word segs (at_ base 4) = Some W_8fe80.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 1 _ HCODE eq_refl). Qed.
  Lemma Fo8 : fetch_word segs (at_ base 8) = Some W_8fe84.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 2 _ HCODE eq_refl). Qed.
  Lemma Fo12 : fetch_word segs (at_ base 12) = Some W_8fe88.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 3 _ HCODE eq_refl). Qed.
  Lemma Fo16 : fetch_word segs (at_ base 16) = Some W_8fe8c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 4 _ HCODE eq_refl). Qed.
  Lemma Fo20 : fetch_word segs (at_ base 20) = Some W_8fe90.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 5 _ HCODE eq_refl). Qed.
  Lemma Fo24 : fetch_word segs (at_ base 24) = Some W_8fe94.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 6 _ HCODE eq_refl). Qed.
  Lemma Fo28 : fetch_word segs (at_ base 28) = Some W_8fe98.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 7 _ HCODE eq_refl). Qed.
  Lemma Fo32 : fetch_word segs (at_ base 32) = Some W_8fe9c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 8 _ HCODE eq_refl). Qed.
  Lemma Fo36 : fetch_word segs (at_ base 36) = Some W_8fea0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 9 _ HCODE eq_refl). Qed.
  Lemma Fo40 : fetch_word segs (at_ base 40) = Some W_8fea4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 10 _ HCODE eq_refl). Qed.
  Lemma Fo44 : fetch_word segs (at_ base 44) = Some W_8fea8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 11 _ HCODE eq_refl). Qed.
  Lemma Fo48 : fetch_word segs (at_ base 48) = Some W_8feac.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 12 _ HCODE eq_refl). Qed.
  Lemma Fo52 : fetch_word segs (at_ base 52) = Some W_8feb0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 13 _ HCODE eq_refl). Qed.
  Lemma Fo64 : fetch_word segs (at_ base 64) = Some W_8febc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 16 _ HCODE eq_refl). Qed.
  Lemma Fo68 : fetch_word segs (at_ base 68) = Some W_8fec0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 17 _ HCODE eq_refl). Qed.
  Lemma Fo72 : fetch_word segs (at_ base 72) = Some W_8fec4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 18 _ HCODE eq_refl). Qed.
  Lemma Fo76 : fetch_word segs (at_ base 76) = Some W_8fec8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 19 _ HCODE eq_refl). Qed.
  Lemma Fo80 : fetch_word segs (at_ base 80) = Some W_8fecc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 20 _ HCODE eq_refl). Qed.
  Lemma Fo84 : fetch_word segs (at_ base 84) = Some W_8fed0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 21 _ HCODE eq_refl). Qed.
  Lemma Fo88 : fetch_word segs (at_ base 88) = Some W_8fed4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 22 _ HCODE eq_refl). Qed.
  Lemma Fo160 : fetch_word segs (at_ base 160) = Some W_8ff1c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 40 _ HCODE eq_refl). Qed.
  Lemma Fo164 : fetch_word segs (at_ base 164) = Some W_8ff20.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 41 _ HCODE eq_refl). Qed.
  Lemma Fo168 : fetch_word segs (at_ base 168) = Some W_8ff24.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 42 _ HCODE eq_refl). Qed.
  Lemma Fo172 : fetch_word segs (at_ base 172) = Some W_8ff28.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 43 _ HCODE eq_refl). Qed.
  Lemma Fo176 : fetch_word segs (at_ base 176) = Some W_8ff2c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 44 _ HCODE eq_refl). Qed.
  Lemma Fo180 : fetch_word segs (at_ base 180) = Some W_8ff30.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 45 _ HCODE eq_refl). Qed.
  Lemma Fo184 : fetch_word segs (at_ base 184) = Some W_8ff34.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 46 _ HCODE eq_refl). Qed.
  Lemma Fo188 : fetch_word segs (at_ base 188) = Some W_8ff38.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 47 _ HCODE eq_refl). Qed.
  Lemma Fo192 : fetch_word segs (at_ base 192) = Some W_8ff3c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 48 _ HCODE eq_refl). Qed.
  Lemma Fo196 : fetch_word segs (at_ base 196) = Some W_8ff40.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 49 _ HCODE eq_refl). Qed.
  Lemma Fo200 : fetch_word segs (at_ base 200) = Some W_8ff44.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 50 _ HCODE eq_refl). Qed.
  Lemma Fo204 : fetch_word segs (at_ base 204) = Some W_8ff48.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 51 _ HCODE eq_refl). Qed.
  Lemma Fo208 : fetch_word segs (at_ base 208) = Some W_8ff4c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 52 _ HCODE eq_refl). Qed.
  Lemma Fo212 : fetch_word segs (at_ base 212) = Some W_8ff50.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 53 _ HCODE eq_refl). Qed.
  Lemma Fo216 : fetch_word segs (at_ base 216) = Some W_8ff54.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 54 _ HCODE eq_refl). Qed.
  Lemma Fo220 : fetch_word segs (at_ base 220) = Some W_8ff58.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 55 _ HCODE eq_refl). Qed.
  Lemma Fo224 : fetch_word segs (at_ base 224) = Some W_8ff5c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 56 _ HCODE eq_refl). Qed.
  Lemma Fo228 : fetch_word segs (at_ base 228) = Some W_8ff60.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 57 _ HCODE eq_refl). Qed.
  Lemma Fo232 : fetch_word segs (at_ base 232) = Some W_8ff64.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 58 _ HCODE eq_refl). Qed.
  Lemma Fo236 : fetch_word segs (at_ base 236) = Some W_8ff68.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 59 _ HCODE eq_refl). Qed.
  Lemma Fo240 : fetch_word segs (at_ base 240) = Some W_8ff6c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 60 _ HCODE eq_refl). Qed.
  Lemma Fo244 : fetch_word segs (at_ base 244) = Some W_8ff70.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 61 _ HCODE eq_refl). Qed.
  Lemma Fo248 : fetch_word segs (at_ base 248) = Some W_8ff74.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 62 _ HCODE eq_refl). Qed.
  Lemma Fo252 : fetch_word segs (at_ base 252) = Some W_8ff78.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 63 _ HCODE eq_refl). Qed.
  Lemma Fo256 : fetch_word segs (at_ base 256) = Some W_8ff7c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 64 _ HCODE eq_refl). Qed.
  Lemma Fo260 : fetch_word segs (at_ base 260) = Some W_8ff80.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 65 _ HCODE eq_refl). Qed.
  Lemma Fo264 : fetch_word segs (at_ base 264) = Some W_8ff84.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 66 _ HCODE eq_refl). Qed.
  Lemma Fo268 : fetch_word segs (at_ base 268) = Some W_8ff88.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 67 _ HCODE eq_refl). Qed.
  Lemma Fo272 : fetch_word segs (at_ base 272) = Some W_8ff8c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 68 _ HCODE eq_refl). Qed.
  Lemma Fo276 : fetch_word segs (at_ base 276) = Some W_8ff90.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 69 _ HCODE eq_refl). Qed.
  Lemma Fo280 : fetch_word segs (at_ base 280) = Some W_8ff94.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 70 _ HCODE eq_refl). Qed.
  Lemma Fo284 : fetch_word segs (at_ base 284) = Some W_8ff98.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 71 _ HCODE eq_refl). Qed.
  Lemma Fo288 : fetch_word segs (at_ base 288) = Some W_8ff9c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 uf_words 72 _ HCODE eq_refl). Qed.

  (* [comment removed for export] *)
  Variables (regs : bvmap 5 word) (rom : word -> option byte).
  Variables (ra sp this pc0 bp top bot : word).
  Hypothesis Hret : ret_ok ra.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = this.
  Hypothesis H11 : getr regs 11 = pc0.
  Hypothesis H12 : getr regs 12 = bp.
  Hypothesis H13 : getr regs 13 = top.
  Hypothesis H14 : getr regs 14 = bot.
  Hypothesis H15 : getr regs 15 = Z_to_bv 64 30.
  (* [comment removed for export] *)
  Hypothesis Gsp : (2 ^ 32 + 64 <= U sp)%Z.
  Hypothesis Gframe : (U sp <= U this)%Z.
  Hypothesis Gobj : (U this + 256 <= U bp - 16)%Z.
  Hypothesis GS : (U bp + 16 <= 2 ^ 47)%Z.
  Hypothesis GS8 : (U bp mod 16 = 0)%Z.
  Hypothesis Gtop : (4096 <= U top <= 2 ^ 47)%Z.
  Hypothesis Gbot : (U bot < U top)%Z.

  #[local] Abbreviation CL := (fun r => In r uf_clob).
  #[local] Abbreviation CLX := (fun r => In r uf_clobx).

  (* [comment removed for export] *)
  Lemma uf_epi : forall (M : word -> option byte) r0,
    getr r0 2 = at_ sp (-64) -> getr r0 10 = this -> getr r0 11 = pc0 ->
    (forall (k : Z) (v : word),
       In (k, v) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19);
                  (-48, getr regs 20); (-56, getr regs 21); (-64, getr regs 22)]%Z ->
       rdn segs M (at_ sp k) 8 = Some (LE8 v)) ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 252) M rom) (mkst r ra M rom)
      /\ getr r 10 = this /\ getr r 11 = pc0
      /\ regs_agree CL regs r.
  Proof using H15 H14 H13 H12 H2 H1 Hret bot top bp HCODE.
    intros M r0 R2 R10 R11 RD AG0. pose proof (u64_range sp) as Hspr.
    Ltac fldM F D vv RD :=
      chain_step; [reflexivity
        | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
          [exact F | reflexivity | exact D
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; apply RD; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto
          | apply bytes_le_to_Z_8]
        | step_simpl]; vn.
    wd_eexists. split; [|split; [|split]].
    - fldM Fo252 D_8ff78 ra RD.
      fldM Fo256 D_8ff7c (getr regs 8) RD.
      fldM Fo260 D_8ff80 (getr regs 9) RD.
      fldM Fo264 D_8ff84 (getr regs 18) RD.
      fldM Fo268 D_8ff88 (getr regs 19) RD.
      fldM Fo272 D_8ff8c (getr regs 20) RD.
      fldM Fo276 D_8ff90 (getr regs 21) RD.
      fldM Fo280 D_8ff94 (getr regs 22) RD.
      an Fo284 D_8ff98.                                  (* [comment removed for export] *)
      aret Fo288 D_8ff9c ra.                             (* [comment removed for export] *)
      wd_refl.
    - gres. exact R10.
    - gres. exact R11.
    - apply (regs_agree_strengthen uf_clob uf_clobx regs).
      + (lazymatch goal with |- ?G => let G' := eval unfold uf_clobx in G in change_no_check G' end). ra_solve.
      + intros i Hi Hni. cbn [uf_clobx In] in Hi.
        repeat (destruct Hi as [<-|Hi]; [gres; rwH; rewrite ?at_addi, ?at_0; first [reflexivity | symmetry; assumption | f_equal; lia | exfalso; apply Hni; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto] |]).
        destruct Hi.
  Qed.

  (* [comment removed for export] *)
  Definition uf_frame (mem : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
      (at_ sp (-8)) (LE8 ra)) (at_ sp (-16)) (LE8 (getr regs 8))) (at_ sp (-24)) (LE8 (getr regs 9)))
      (at_ sp (-32)) (LE8 (getr regs 18))) (at_ sp (-40)) (LE8 (getr regs 19))) (at_ sp (-48)) (LE8 (getr regs 20)))
      (at_ sp (-56)) (LE8 (getr regs 21))) (at_ sp (-64)) (LE8 (getr regs 22)).
  (* [comment removed for export] *)
  Definition uf_mem2 (mem : word -> option byte) : word -> option byte :=
    wbytes (wbytes (uf_frame mem) (at_ this 8) (LE4 1)) (at_ this 16) (LE8 pc0).

  Lemma uf_frame_outside : forall mem (x : word),
    (U x < U sp - 64 \/ U sp <= U x)%Z -> uf_frame mem x = mem x.
  Proof using Gsp bp.
    intros mem x Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold uf_frame in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; try reflexivity; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia.
  Qed.
  Lemma uf_mem2_outside : forall mem (x : word),
    (U x < U sp - 64)%Z \/ (U sp <= U x < U this + 8)%Z \/ (U this + 12 <= U x < U this + 16)%Z \/ (U this + 24 <= U x)%Z ->
    uf_mem2 mem x = mem x.
  Proof using GS Gobj Gframe Gsp bp.
    intros mem x Hx. pose proof (u64_range sp). pose proof (u64_range this). (lazymatch goal with |- ?G => let G' := eval unfold uf_mem2 in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia.
    apply uf_frame_outside. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma uf_mem2_slots : forall mem (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19);
               (-48, getr regs 20); (-56, getr regs 21); (-64, getr regs 22)]%Z ->
    rdn segs (uf_mem2 mem) (at_ sp k) 8 = Some (LE8 v).
  Proof using GS Gobj Gframe Gsp bp.
    intros mem k v Hin. pose proof (u64_range sp). pose proof (u64_range this). (lazymatch goal with |- ?G => let G' := eval unfold uf_mem2, uf_frame in G in change_no_check G' end).
    cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_same : forall (M mem : word -> option byte) (a : word) k bs0,
    (forall x : word, (U a <= U x < U a + Z.of_nat k)%Z -> M x = mem x) -> (U a + Z.of_nat k <= 2 ^ 64)%Z ->
    rdn segs mem a k = Some bs0 -> rdn segs M a k = Some bs0.
  Proof using. intros M mem a k bs0 HM Hnw Hr. rewrite <- Hr. apply rdn_ext; [exact Hnw | exact HM]. Qed.
  Lemma rd_sameZ : forall (M mem : word -> option byte) (c : Z) k bs0,
    (0 <= c < 2 ^ 64)%Z -> (c + Z.of_nat k <= 2 ^ 64)%Z ->
    (forall x : word, (c <= U x < c + Z.of_nat k)%Z -> M x = mem x) ->
    rdn segs mem (Z_to_bv 64 c) k = Some bs0 -> rdn segs M (Z_to_bv 64 c) k = Some bs0.
  Proof using bp.
    intros M mem c k bs0 Hc Hk HM Hr. apply (rd_same M mem); [| wd_ulia | exact Hr].
    intros x Hx. apply HM. revert Hx. unorm. intros Hx. exact Hx.
  Qed.

  Section Run.
    Variable mem : word -> option byte.
    Variables (P : word).
    (* [comment removed for export] *)
    Hypothesis Rg : rdn segs mem (Z_to_bv 64 g_pgsz) 8 = Some (LE8 P).
    Hypothesis RP : rdn segs mem P 8 = Some (LE8 (Z_to_bv 64 4096)).
    Hypothesis Gg : (0 <= g_pgsz /\ g_pgsz + 8 <= 2 ^ 32)%Z.
    Hypothesis GP : (U P + 8 <= 2 ^ 32)%Z.
    (* [comment removed for export] *)
    Hypothesis Hstk : store_ok segs mem (at_ sp (-64)) 64 = true.
    Hypothesis Hobj : store_ok segs mem (at_ this 8) 248 = true.

    Ltac sok8 Hs lo N :=
      repeat (eapply store_ok_mono; [apply wbytes_grows|]);
      eapply (store_ok_sub segs mem lo _ N); [rewrite at_u; lia | exact Hs | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia].
    (* [comment removed for export] *)
    Ltac sok8G GR Hs lo N :=
      repeat (eapply store_ok_mono; [apply wbytes_grows|]);
      eapply store_ok_mono; [exact GR|];
      eapply (store_ok_sub segs mem lo _ N); [rewrite at_u; lia | exact Hs | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia].
    Ltac fsd_g F D aa oktac :=
      chain_step; [reflexivity
        | eapply step_sd_at with (a := aa);
          [exact F | reflexivity | exact D
          | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
          | gres; rwH; reflexivity
          | oktac ]
        | step_simpl]; vn.
    Ltac fsw_g F D aa oktac :=
      chain_step; [reflexivity
        | eapply step_sw_at with (a := aa);
          [exact F | reflexivity | exact D
          | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
          | gres; rwH; reflexivity
          | oktac ]
        | step_simpl]; vn.
    Ltac fsd F D aa := fsd_g F D aa ltac:(first [sok8 Hstk (at_ sp (-64)) 64%nat | sok8 Hobj (at_ this 8) 248%nat]).
    Ltac fsw F D aa := fsw_g F D aa ltac:(first [sok8 Hstk (at_ sp (-64)) 64%nat | sok8 Hobj (at_ this 8) 248%nat]).
    Ltac cld F D vv Hr :=
      chain_step; [reflexivity
        | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
          [exact F | reflexivity | exact D | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi; zlit_at; Hr | apply bytes_le_to_Z_8]
        | step_simpl]; vn.

    (* [comment removed for export] *)
    Lemma uf_pro :
      exists r,
        msteps segs (mkst regs (at_ base 0) mem rom) (mkst r (at_ base 164) (uf_mem2 mem) rom)
        /\ getr r 2 = at_ sp (-64) /\ getr r 10 = this /\ getr r 11 = pc0 /\ getr r 12 = bp
        /\ getr r 13 = Z_to_bv 64 4096 /\ getr r 14 = bot /\ getr r 15 = Z_to_bv 64 1
        /\ getr r 8 = Z_to_bv 64 30 /\ getr r 9 = top
        /\ regs_agree CLX regs r.
    Proof using Hobj Hstk GP Gg RP Rg P Gbot Gtop GS Gobj Gframe Gsp H15 H14 H13 H12 H11 H10 H2 H1 G56 HCODE g_pgsz.
      pose proof (u64_range sp) as Hspr. pose proof (u64_range this) as Hth. pose proof (u64_range top) as Htop.
      destruct G56 as [gx G56'].
      wd_eexists. split.
      - an Fo0 D_8fe7c.                                   (* [comment removed for export] *)
        fsd Fo4 D_8fe80 (at_ sp (-8)).                    (* [comment removed for export] *)
        fsd Fo8 D_8fe84 (at_ sp (-16)).                   (* [comment removed for export] *)
        fsd Fo12 D_8fe88 (at_ sp (-24)).                  (* [comment removed for export] *)
        fsd Fo16 D_8fe8c (at_ sp (-32)).                  (* [comment removed for export] *)
        fsd Fo20 D_8fe90 (at_ sp (-40)).                  (* [comment removed for export] *)
        fsd Fo24 D_8fe94 (at_ sp (-48)).                  (* [comment removed for export] *)
        fsd Fo28 D_8fe98 (at_ sp (-56)).                  (* [comment removed for export] *)
        fsd Fo32 D_8fe9c (at_ sp (-64)).                  (* [comment removed for export] *)
        change (wbytes _ _ _) with (uf_frame mem).
        an Fo36 D_8fea0.                                  (* [comment removed for export] *)
        an Fo40 D_8fea4.                                  (* [comment removed for export] *)
        an Fo44 D_8fea8.                                  (* [comment removed for export] *)
        an Fo48 D_8feac.                                  (* [comment removed for export] *)
        ab_ft Fo52 D_8feb0 ltac:(condz).                 (* [comment removed for export] *)
        eapply msteps_trans; [ eapply G56'; apply (rd_sameZ _ mem); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x Hx; apply uf_frame_outside; cbn in Hx; lia | exact Rg] | ]; zlit_at.
        cld Fo64 D_8febc (Z_to_bv 64 4096) ltac:(apply (rd_same _ mem); [intros x Hx; apply uf_frame_outside; cbn in Hx; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact RP]).   (* [comment removed for export] *)
        ab_ft Fo68 D_8fec0 ltac:(condz).                 (* [comment removed for export] *)
        an Fo72 D_8fec4.                                  (* [comment removed for export] *)
        av Fo76 D_8fec8 (Z_to_bv 64 (U top / 4096)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; reflexivity).  (* [comment removed for export] *)
        fsw Fo80 D_8fecc (at_ this 8).                    (* [comment removed for export] *)
        fsd Fo84 D_8fed0 (at_ this 16).                   (* [comment removed for export] *)
        change (wbytes _ _ _) with (uf_mem2 mem).
        assert (Hd : (1 <= U top / 4096 /\ U top / 4096 < 2 ^ 62)%Z) by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]).
        ab_tk Fo88 D_8fed4 ltac:(condz).                 (* [comment removed for export] *)
        ab_ft Fo160 D_8ff1c ltac:(condz).                (* [comment removed for export] *)
        wd_refl.
      - post. (lazymatch goal with |- ?G => let G' := eval unfold uf_clobx in G in change_no_check G' end). ra_solve.
    Qed.

    (* [comment removed for export] *)
    Definition uf_upd (M : word -> option byte) (k : Z) (r : word) : word -> option byte :=
      wbytes (wbytes M (at_ this 8) (LE4 (k + 1))) (at_ this (16 + 8 * k)) (LE8 r).

    Lemma uf_upd_outside : forall M k r (x : word), (1 <= k < 30)%Z ->
      (U x < U this + 8 \/ (U this + 12 <= U x < U this + 16 + 8 * k) \/ U this + 24 + 8 * k <= U x)%Z ->
      uf_upd M k r x = M x.
    Proof using GS Gobj Gframe Gsp bp sp.
      intros M k r x Hk Hx. pose proof (u64_range this). (lazymatch goal with |- ?G => let G' := eval unfold uf_upd in G in change_no_check G' end).
      rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma rdn_some_of_defined : forall (M : word -> option byte) n (a : word),
      (forall i, (U a <= i < U a + Z.of_nat n)%Z -> M (Z_to_bv 64 i) <> None) -> (U a + Z.of_nat n <= 2 ^ 64)%Z ->
      exists bs, rdn segs M a n = Some bs /\ length bs = n.
    Proof using Gobj Gframe Gsp bp this sp.
      intros M n. induction n as [|n IH]; intros a HD Hnw.
      - exists []. split; reflexivity.
      - (lazymatch goal with |- ?G => let G' := eval cbn [rdn] in G in change_no_check G' end). pose proof (u64_range a) as Ha.
        assert (Hb : exists b, M a = Some b).
        { destruct (M a) as [b|] eqn:E; [exists b; reflexivity|]. exfalso. apply (HD (U a)); [lia|].
          rewrite Z_to_bv_bv_unsigned. exact E. }
        destruct Hb as [b ->].
        destruct n as [|n'].
        + exists [b]. split; reflexivity.
        + assert (Hu1 : U (a + 1) = (U a + 1)%Z) by (apply u_add1; lia).
          destruct (IH (a + 1)) as (bs & -> & L); [intros i Hi; apply HD; lia | lia |].
          exists (b :: bs). split; [reflexivity | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); rewrite L; reflexivity].
    Qed.

    (* [comment removed for export] *)
    Lemma rdn_of_m64 : forall (M : word -> option byte) (a : word) (w : Z),
      m64 M (U a) w -> (U a + 8 <= 2 ^ 64)%Z ->
      exists bs, rdn segs M a 8 = Some bs /\ length bs = 8%nat /\ bytes_le_to_Z bs = w.
    Proof using Gobj Gframe Gsp bp this sp.
      intros M a w (bs & B1 & B2 & B3) Hnw. exists bs. split; [| split; assumption].
      pose proof (u64_range a) as Ha.
      destruct bs as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|x t]]]]]]]]]; cbn in B2; try lia.
      assert (E : forall i : nat, (i < 8)%nat -> M (Z_to_bv 64 (U a + Z.of_nat i)) = Some (nth i [b0; b1; b2; b3; b4; b5; b6; b7] (Z_to_bv 8 0))) by exact B1.
      rewrite <- (rdn_wbytes_hit segs [b0; b1; b2; b3; b4; b5; b6; b7] M a) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia).
      apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. cbn [length] in Hx.
      rewrite wbytes_inside by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia). cbn [length Z.of_nat] in *.
      pose proof (u64_range x).
      assert (Ex : x = Z_to_bv 64 (U a + Z.of_nat (Z.to_nat (U x - U a)))) by (apply bv_eq; wd_ulia).
      rewrite Ex at 1. rewrite (E (Z.to_nat (U x - U a))) by lia. reflexivity.
    Qed.

    #[local] Abbreviation lez := bytes_le_to_Z.
    (* [comment removed for export] *)
    Definition uf_foot (x : word) : Prop := (U this + 8 <= U x < U this + 12)%Z \/ (U this + 24 <= U x < U this + 256)%Z.
    Definition uf_slots (M : word -> option byte) : Prop :=
      forall (c : Z) (x : word),
        In (c, x) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19);
                   (-48, getr regs 20); (-56, getr regs 21); (-64, getr regs 22)]%Z ->
        rdn segs M (at_ sp c) 8 = Some (LE8 x).

    Lemma uf_slots_keep : forall M M' : word -> option byte,
      uf_slots M -> (forall x : word, (U x < U sp)%Z -> M' x = M x) -> uf_slots M'.
    Proof using GS Gobj Gframe Gsp bp this.
      intros M M' RD HM c x Hin. pose proof (u64_range sp).
      assert (Hc : (-64 <= c <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E; intros; lia|]); destruct Hin).
      apply (rd_same M' M); [intros y Hy; apply HM; rewrite at_u in Hy; lia | rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (RD c x Hin)].
    Qed.

    Ltac cldb F D bs0 Hr :=
      chain_step; [reflexivity
        | eapply step_ld with (bs := bs0) (v := Z_to_bv 64 (bytes_le_to_Z bs0));
          [exact F | reflexivity | exact D | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi; zlit_at; Hr | unorm; reflexivity]
        | step_simpl]; vn.

    (* [comment removed for export] *)
    Lemma uf_exit : forall (M M1 : word -> option byte) r1 (k s : Z) (bnd : Z),
      getr r1 2 = at_ sp (-64) -> getr r1 10 = this -> getr r1 11 = pc0 -> regs_agree CLX regs r1 ->
      uf_slots M1 -> (k <= s <= 30)%Z -> (s <= k + 1)%Z -> (0 <= bnd)%Z -> rdn segs M1 (at_ this 8) 4 = Some (LE4 s) ->
      (forall x : word, M1 x <> M x -> uf_foot x) -> mem_grows M M1 ->
      exists r' M' (s' : Z),
        msteps segs (mkst r1 (at_ base 252) M1 rom) (mkst r' ra M' rom)
        /\ getr r' 10 = this /\ getr r' 11 = pc0 /\ regs_agree CL regs r'
        /\ (k <= s' <= 30)%Z /\ (s' <= k + 1 + bnd)%Z
        /\ rdn segs M' (at_ this 8) 4 = Some (LE4 s')
        /\ (forall x : word, M' x <> M x -> uf_foot x)
        /\ mem_grows M M'.
    Proof using Gobj Gframe Gsp H15 H14 H13 H12 H2 H1 Hret bot top bp HCODE.
      intros M M1 r1 k s bnd Q2 Q10 Q11 QAG QRD Hs1 Hs2 Hb QSZ QF QG.
      destruct (uf_epi M1 r1 Q2 Q10 Q11 QRD QAG) as (r' & RUN & P10 & P11 & PAG).
      exists r', M1, s. repeat (split; [first [exact RUN | exact P10 | exact P11 | exact PAG | exact QSZ | exact QF | lia] |]). exact QG.
    Qed.

    (* [comment removed for export] *)
    Definition uf_step (M : word -> option byte) (k k1 : Z) (r : word) : word -> option byte :=
      if Z.eqb k1 k then M else uf_upd M k r.

    Lemma uf_head : forall (M : word -> option byte) r0 (v : word) (k : Z) (bsr : list byte),
      getr r0 2 = at_ sp (-64) -> getr r0 10 = this -> getr r0 11 = pc0 -> getr r0 12 = v ->
      getr r0 13 = Z_to_bv 64 4096 -> getr r0 14 = at_ this 16 -> getr r0 15 = Z_to_bv 64 k ->
      getr r0 8 = Z_to_bv 64 30 -> getr r0 9 = at_ top (-16) -> regs_agree CLX regs r0 ->
      (1 <= k < 30)%Z -> (U bp <= U v)%Z -> (U v + 16 < 2 ^ 47)%Z ->
      rdn segs M (at_ v (-8)) 8 = Some bsr -> length bsr = 8%nat -> (4096 <= lez bsr)%Z ->
      mem_grows mem M ->
      exists r1 (k1 : Z),
        msteps segs (mkst r0 (at_ base 192) M rom) (mkst r1 (at_ base 228) (uf_step M k k1 (Z_to_bv 64 (lez bsr))) rom)
        /\ getr r1 2 = at_ sp (-64) /\ getr r1 10 = this /\ getr r1 11 = pc0 /\ getr r1 12 = v
        /\ getr r1 13 = Z_to_bv 64 4096 /\ getr r1 14 = at_ this 16 /\ getr r1 15 = Z_to_bv 64 k1
        /\ getr r1 8 = Z_to_bv 64 30 /\ getr r1 9 = at_ top (-16) /\ regs_agree CLX regs r1
        /\ (k1 = k \/ k1 = k + 1)%Z.
    Proof using Hobj Gobj Gframe Gsp HCODE.
      intros M r0 v k bsr R2 R10 R11 R12 R13 R14 R15 R8 R9 AG0 Hk HSv Hv Rr Lr Hr4 GR.
      pose proof (u64_range sp) as Hspr. pose proof (u64_range this) as Hth. pose proof (u64_range top) as Htop.
      pose proof (u64_range bp) as HS. pose proof (u64_range v) as Hvr. pose proof (u64_range pc0) as Hpc0.
      pose proof (bytes_le_to_Z_bound bsr) as Br. rewrite Lr in Br. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Br.
      pose proof (bytes_le_to_Z_nonneg bsr) as Br0.
      destruct (Z.eq_dec (lez bsr) (U pc0)) as [Epc|Npc].
      - (* [comment removed for export] *)
        eexists _, k. split.
        + ab_ft Fo192 D_8ff3c ltac:(condz).                (* [comment removed for export] *)
          cldb Fo196 D_8ff40 bsr ltac:(exact Rr).           (* [comment removed for export] *)
          ab_ft Fo200 D_8ff44 ltac:(condz).                (* [comment removed for export] *)
          ab_tk Fo204 D_8ff48 ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, bv_eqb in G in change_no_check G' end); unorm; apply Z.eqb_eq; exact Epc).   (* [comment removed for export] *)
          (lazymatch goal with |- ?G => let G' := eval unfold uf_step in G in change_no_check G' end). rewrite Z.eqb_refl. wd_refl.
        + post. (lazymatch goal with |- ?G => let G' := eval unfold uf_clobx in G in change_no_check G' end). ra_chain.
      - (* [comment removed for export] *)
        eexists _, (k + 1)%Z. split.
        + ab_ft Fo192 D_8ff3c ltac:(condz).
          cldb Fo196 D_8ff40 bsr ltac:(exact Rr).
          ab_ft Fo200 D_8ff44 ltac:(condz).
          ab_ft Fo204 D_8ff48 ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, bv_eqb in G in change_no_check G' end); unorm; apply Z.eqb_neq; exact Npc).   (* [comment removed for export] *)
          av Fo208 D_8ff4c (Z_to_bv 64 (8 * k)) ltac:(rewrite v_slli_mul by lia; unorm; f_equal; lia).   (* [comment removed for export] *)
          av Fo212 D_8ff50 (Z_to_bv 64 (k + 1)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; reflexivity).              (* [comment removed for export] *)
          av Fo216 D_8ff54 (at_ this (16 + 8 * k)) ltac:(rewrite v_add_at by lia; rewrite at_at; reflexivity).   (* [comment removed for export] *)
          fsw_g Fo220 D_8ff58 (at_ this 8) ltac:(sok8G GR Hobj (at_ this 8) 248%nat).                   (* [comment removed for export] *)
          fsd_g Fo224 D_8ff5c (at_ this (16 + 8 * k)) ltac:(sok8G GR Hobj (at_ this 8) 248%nat).        (* [comment removed for export] *)
          (lazymatch goal with |- ?G => let G' := eval unfold uf_step in G in change_no_check G' end). replace (Z.eqb (k + 1) k) with false by (symmetry; apply Z.eqb_neq; lia).
          (lazymatch goal with |- ?G => let G' := eval unfold uf_upd in G in change_no_check G' end). wd_refl.
        + post. (lazymatch goal with |- ?G => let G' := eval unfold uf_clobx in G in change_no_check G' end). ra_chain.
    Qed.

    (* [comment removed for export] *)
    Lemma uf_tail : forall (d : nat) (M1 : word -> option byte) r1 (v : word) (k1 : Z) (bsw : list byte),
      getr r1 2 = at_ sp (-64) -> getr r1 10 = this -> getr r1 11 = pc0 -> getr r1 12 = v ->
      getr r1 13 = Z_to_bv 64 4096 -> getr r1 14 = at_ this 16 -> getr r1 15 = Z_to_bv 64 k1 ->
      getr r1 8 = Z_to_bv 64 30 -> getr r1 9 = at_ top (-16) -> regs_agree CLX regs r1 ->
      (U bp <= U v)%Z -> (U v + 16 < 2 ^ 47)%Z ->
      rdn segs mem (at_ v (-16)) 8 = Some bsw -> length bsw = 8%nat ->
      fpc mem (lez bsw) (U v) d ->
      (forall x : word, (U bp - 16 <= U x)%Z -> M1 x = mem x) ->
      (exists r2, msteps segs (mkst r1 (at_ base 228) M1 rom) (mkst r2 (at_ base 252) M1 rom)
                  /\ getr r2 2 = at_ sp (-64) /\ getr r2 10 = this /\ getr r2 11 = pc0 /\ regs_agree CLX regs r2)
      \/ (exists r2 d' (bsr' bsw' : list byte), d = S d'
            /\ msteps segs (mkst r1 (at_ base 228) M1 rom) (mkst r2 (at_ base 192) M1 rom)
            /\ getr r2 2 = at_ sp (-64) /\ getr r2 10 = this /\ getr r2 11 = pc0 /\ getr r2 12 = Z_to_bv 64 (lez bsw)
            /\ getr r2 13 = Z_to_bv 64 4096 /\ getr r2 14 = at_ this 16 /\ getr r2 15 = Z_to_bv 64 k1
            /\ getr r2 8 = Z_to_bv 64 30 /\ getr r2 9 = at_ top (-16) /\ regs_agree CLX regs r2
            /\ (U bp <= lez bsw)%Z /\ (lez bsw + 16 < 2 ^ 47)%Z
            /\ rdn segs mem (at_ (Z_to_bv 64 (lez bsw)) (-8)) 8 = Some bsr' /\ length bsr' = 8%nat
            /\ rdn segs mem (at_ (Z_to_bv 64 (lez bsw)) (-16)) 8 = Some bsw' /\ length bsw' = 8%nat
            /\ fpc mem (lez bsw') (lez bsw) d').
    Proof using Gtop Gobj Gframe Gsp HCODE.
      intros d M1 r1 v k1 bsw R2 R10 R11 R12 R13 R14 R15 R8 R9 AG0 HSv Hv Rw Lw FPC HM1.
      pose proof (u64_range sp) as Hspr. pose proof (u64_range this) as Hth. pose proof (u64_range top) as Htop.
      pose proof (u64_range bp) as HS. pose proof (u64_range v) as Hvr.
      pose proof (bytes_le_to_Z_bound bsw) as Bw. rewrite Lw in Bw. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bw.
      pose proof (bytes_le_to_Z_nonneg bsw) as Bw0.
      assert (Rw1 : rdn segs M1 (at_ v (-16)) 8 = Some bsw).
      { apply (rd_same M1 mem); [intros x Hx; apply HM1; rewrite at_u in Hx by lia; lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Rw]. }
      destruct (Z.lt_ge_cases (U v) (lez bsw)) as [C1|C1].
      2:{ left. wd_eexists. split.
          - cldb Fo228 D_8ff60 bsw ltac:(exact Rw1).        (* [comment removed for export] *)
            ab_tk Fo232 D_8ff64 ltac:(condz).              (* [comment removed for export] *)
            wd_refl.
          - post. (lazymatch goal with |- ?G => let G' := eval unfold uf_clobx in G in change_no_check G' end). ra_chain. }
      destruct (Z.lt_ge_cases (lez bsw) (U top - 16)) as [C2|C2].
      2:{ left. wd_eexists. split.
          - cldb Fo228 D_8ff60 bsw ltac:(exact Rw1).
            ab_ft Fo232 D_8ff64 ltac:(condz).
            ab_tk Fo236 D_8ff68 ltac:(condz).              (* [comment removed for export] *)
            wd_refl.
          - post. (lazymatch goal with |- ?G => let G' := eval unfold uf_clobx in G in change_no_check G' end). ra_chain. }
      destruct (Z.eq_dec (lez bsw mod 8) 0) as [C3|C3].
      2:{ left. wd_eexists. split.
          - cldb Fo228 D_8ff60 bsw ltac:(exact Rw1).
            ab_ft Fo232 D_8ff64 ltac:(condz).
            ab_ft Fo236 D_8ff68 ltac:(condz).
            av Fo240 D_8ff6c (Z_to_bv 64 (lez bsw mod 8)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end); change (bv_wrap 64 7) with 7%Z; unorm; rewrite land_7 by lia; reflexivity).  (* [comment removed for export] *)
            an Fo244 D_8ff70.                                (* [comment removed for export] *)
            pose proof (Z.mod_pos_bound (lez bsw) 8 ltac:(lia)).
            ab_ft Fo248 D_8ff74 ltac:(condz).              (* [comment removed for export] *)
            wd_refl.
          - post. (lazymatch goal with |- ?G => let G' := eval unfold uf_clobx in G in change_no_check G' end). ra_chain. }
      (* [comment removed for export] *)
      right.
      inversion FPC as [v0 lo0 d0 ST E1 E2 E3 | v0 lo0 d' w2 H16 H8 HP DEF RD64 CH E1 E2 E3]; subst v0 lo0.
      { exfalso. unfold PTRHI in ST. lia. }
      subst d.
      assert (Uw : U (Z_to_bv 64 (lez bsw)) = lez bsw) by (unorm; reflexivity).
      destruct (rdn_of_m64 mem (at_ (Z_to_bv 64 (lez bsw)) (-16)) w2) as (bsw' & Rw' & Lw' & Ew').
      { rewrite at_u by (rewrite Uw; lia). rewrite Uw. exact RD64. }
      { rewrite at_u by (rewrite Uw; lia). rewrite Uw. lia. }
      destruct (rdn_some_of_defined mem 8 (at_ (Z_to_bv 64 (lez bsw)) (-8))) as (bsr' & Rr' & Lr').
      { intros i Hi. rewrite at_u in Hi by (rewrite Uw; lia). rewrite Uw in Hi. apply DEF. cbn in Hi. lia. }
      { rewrite at_u by (rewrite Uw; lia). rewrite Uw. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
      eexists _, d', bsr', bsw'. split; [reflexivity|]. split.
      - cldb Fo228 D_8ff60 bsw ltac:(exact Rw1).
        ab_ft Fo232 D_8ff64 ltac:(condz).
        ab_ft Fo236 D_8ff68 ltac:(condz).
        av Fo240 D_8ff6c (Z_to_bv 64 0) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end); change (bv_wrap 64 7) with 7%Z; unorm; rewrite land_7 by lia; rewrite C3; reflexivity).
        an Fo244 D_8ff70.
        ab_tk Fo248 D_8ff74 ltac:(condz).                  (* [comment removed for export] *)
        wd_refl.
      - post. 1: ((lazymatch goal with |- ?G => let G' := eval unfold uf_clobx in G in change_no_check G' end); ra_chain). all: try lia. all: try assumption. rewrite Ew'. exact CH.
    Qed.

    Lemma uf_step_outside : forall M k k1 r (x : word), (1 <= k < 30)%Z ->
      (U x < U this + 8 \/ U this + 256 <= U x)%Z -> uf_step M k k1 r x = M x.
    Proof using GS Gobj Gframe Gsp bp sp.
      intros M k k1 r x Hk Hx. (lazymatch goal with |- ?G => let G' := eval unfold uf_step in G in change_no_check G' end). destruct (Z.eqb k1 k); [reflexivity|]. apply uf_upd_outside; lia.
    Qed.
    Lemma uf_step_grows : forall M k k1 r, mem_grows M (uf_step M k k1 r).
    Proof using.
      intros M k k1 r. (lazymatch goal with |- ?G => let G' := eval unfold uf_step, uf_upd in G in change_no_check G' end). destruct (Z.eqb k1 k); [apply mem_grows_refl|].
      eapply mem_grows_trans; apply wbytes_grows.
    Qed.
    Lemma uf_step_frame : forall M k k1 r (x : word), (1 <= k < 30)%Z ->
      uf_step M k k1 r x <> M x -> uf_foot x.
    Proof using GS Gobj Gframe Gsp bp sp.
      intros M k k1 r x Hk Hx. pose proof (u64_range x). pose proof (u64_range this). (lazymatch goal with |- ?G => let G' := eval unfold uf_foot in G in change_no_check G' end).
      unfold uf_step in Hx. destruct (Z.eqb k1 k); [exfalso; exact (Hx eq_refl)|].
      destruct (Z.lt_ge_cases (U x) (U this + 8)); [exfalso; apply Hx; apply uf_upd_outside; lia|].
      destruct (Z.lt_ge_cases (U x) (U this + 12)); [left; lia|].
      destruct (Z.lt_ge_cases (U x) (U this + 16 + 8 * k)); [exfalso; apply Hx; apply uf_upd_outside; lia|].
      destruct (Z.lt_ge_cases (U x) (U this + 24 + 8 * k)); [right; lia|].
      exfalso; apply Hx; apply uf_upd_outside; lia.
    Qed.
    Lemma uf_step_sz : forall M k k1 r, (1 <= k < 30)%Z -> (k1 = k \/ k1 = k + 1)%Z ->
      rdn segs M (at_ this 8) 4 = Some (LE4 k) -> rdn segs (uf_step M k k1 r) (at_ this 8) 4 = Some (LE4 k1).
    Proof using GS Gobj Gframe Gsp bp sp.
      intros M k k1 r Hk [-> | ->] R; (lazymatch goal with |- ?G => let G' := eval unfold uf_step in G in change_no_check G' end).
      - rewrite Z.eqb_refl. exact R.
      - replace (Z.eqb (k + 1) k) with false by (symmetry; apply Z.eqb_neq; lia). (lazymatch goal with |- ?G => let G' := eval unfold uf_upd in G in change_no_check G' end).
        pose proof (u64_range this).
        rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes, !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ].
        pose proof (rdn_wbytes_hit segs (LE4 (k + 1)) M (at_ this 8)) as X. rewrite length_N_to_le_bytes in X.
        apply X. rewrite at_u by lia. lia.
    Qed.

    (* [comment removed for export] *)
    Record uf_inv (d : nat) (M : word -> option byte) (r0 : bvmap 5 word) (v : word) (k : Z) (bsr bsw : list byte) : Prop := UFI {
      ui_r2 : getr r0 2 = at_ sp (-64); ui_r10 : getr r0 10 = this; ui_r11 : getr r0 11 = pc0; ui_r12 : getr r0 12 = v;
      ui_r13 : getr r0 13 = Z_to_bv 64 4096; ui_r14 : getr r0 14 = at_ this 16; ui_r15 : getr r0 15 = Z_to_bv 64 k;
      ui_r8 : getr r0 8 = Z_to_bv 64 30; ui_r9 : getr r0 9 = at_ top (-16); ui_ag : regs_agree CLX regs r0;
      ui_k : (1 <= k <= 30)%Z; ui_bpv : (U bp <= U v)%Z; ui_v : (U v + 16 < 2 ^ 47)%Z;
      ui_rr : rdn segs mem (at_ v (-8)) 8 = Some bsr; ui_lr : length bsr = 8%nat;
      ui_rw : rdn segs mem (at_ v (-16)) 8 = Some bsw; ui_lw : length bsw = 8%nat;
      ui_fpc : fpc mem (lez bsw) (U v) d;
      ui_hm : forall x : word, (U bp - 16 <= U x)%Z -> M x = mem x;
      ui_gr : mem_grows mem M; ui_slots : uf_slots M;
      ui_sz : rdn segs M (at_ this 8) 4 = Some (LE4 k) }.
  (* [comment removed for export] *)

    (* [comment removed for export] *)
    Lemma uf_round : forall (d : nat) (M : word -> option byte) r0 (v : word) (k : Z) (bsr bsw : list byte),
      uf_inv d M r0 v k bsr bsw ->
      (exists r' M' (s : Z),
        msteps segs (mkst r0 (at_ base 192) M rom) (mkst r' ra M' rom)
        /\ getr r' 10 = this /\ getr r' 11 = pc0 /\ regs_agree CL regs r'
        /\ (k <= s <= 30)%Z /\ (s <= k + 1)%Z
        /\ rdn segs M' (at_ this 8) 4 = Some (LE4 s)
        /\ (forall x : word, M' x <> M x -> uf_foot x)
        /\ mem_grows M M')
      \/ (exists d' M1 r1 v1 k1 bsr' bsw', d = S d' /\ uf_inv d' M1 r1 v1 k1 bsr' bsw'
        /\ msteps segs (mkst r0 (at_ base 192) M rom) (mkst r1 (at_ base 192) M1 rom)
        /\ (k <= k1 <= k + 1)%Z
        /\ (forall x : word, M1 x <> M x -> uf_foot x)
        /\ mem_grows M M1).
    Proof using Hobj Gtop GS Gobj Gframe Gsp H15 H14 H13 H12 H2 H1 Hret bot HCODE.
      intros d M r0 v k bsr bsw [R2 R10 R11 R12 R13 R14 R15 R8 R9 AG0 Hk HSv Hv Rr Lr Rw Lw FPC HM GR RD RSZ].
      pose proof (u64_range sp) as Hspr. pose proof (u64_range this) as Hth. pose proof (u64_range top) as Htop.
      pose proof (u64_range bp) as Hbp. pose proof (u64_range v) as Hvr.
      pose proof (bytes_le_to_Z_bound bsr) as Br. rewrite Lr in Br. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Br.
      pose proof (bytes_le_to_Z_nonneg bsr) as Br0.
      assert (Rr1 : rdn segs M (at_ v (-8)) 8 = Some bsr)
        by (apply (rd_same M mem); [intros x Hx; apply HM; rewrite at_u in Hx by lia; lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Rr]).
      destruct (Z.lt_ge_cases k 30) as [Hk30|Hk30].
      2:{ (* [comment removed for export] *)
          left.
          assert (W : exists r1, msteps segs (mkst r0 (at_ base 192) M rom) (mkst r1 (at_ base 252) M rom)
                       /\ getr r1 2 = at_ sp (-64) /\ getr r1 10 = this /\ getr r1 11 = pc0 /\ regs_agree CLX regs r1).
          { wd_eexists. split.
            { ab_tk Fo192 D_8ff3c ltac:(condz).              (* [comment removed for export] *)
              wd_refl. }
            post; (lazymatch goal with |- ?G => let G' := eval unfold uf_clobx in G in change_no_check G' end); ra_chain. }
          destruct W as (r1 & W & Q2 & Q10 & Q11 & QAG).
          destruct (uf_exit M M r1 k k 0 Q2 Q10 Q11 QAG RD ltac:(lia) ltac:(lia) ltac:(lia) RSZ ltac:(intros x Hx; exfalso; exact (Hx eq_refl)) (mem_grows_refl M))
            as (r' & M' & s' & RUN & X).
          exists r', M', s'. split; [eapply msteps_trans; [exact W | exact RUN] | ].
          destruct X as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). repeat (split; [first [eassumption | lia]|]). exact A8. }
      destruct (Z.lt_ge_cases (lez bsr) 4096) as [Hr4|Hr4].
      { (* [comment removed for export] *)
        left.
        assert (W : exists r1, msteps segs (mkst r0 (at_ base 192) M rom) (mkst r1 (at_ base 252) M rom)
                     /\ getr r1 2 = at_ sp (-64) /\ getr r1 10 = this /\ getr r1 11 = pc0 /\ regs_agree CLX regs r1).
        { wd_eexists. split.
          { ab_ft Fo192 D_8ff3c ltac:(condz).
            cldb Fo196 D_8ff40 bsr ltac:(exact Rr1).         (* [comment removed for export] *)
            ab_tk Fo200 D_8ff44 ltac:(condz).                (* [comment removed for export] *)
            wd_refl. }
          post; (lazymatch goal with |- ?G => let G' := eval unfold uf_clobx in G in change_no_check G' end); ra_chain. }
        destruct W as (r1 & W & Q2 & Q10 & Q11 & QAG).
        destruct (uf_exit M M r1 k k 0 Q2 Q10 Q11 QAG RD ltac:(lia) ltac:(lia) ltac:(lia) RSZ ltac:(intros x Hx; exfalso; exact (Hx eq_refl)) (mem_grows_refl M))
          as (r' & M' & s' & RUN & X).
        exists r', M', s'. split; [eapply msteps_trans; [exact W | exact RUN] | ].
        destruct X as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). repeat (split; [first [eassumption | lia]|]). exact A8. }
      destruct (uf_head M r0 v k bsr R2 R10 R11 R12 R13 R14 R15 R8 R9 AG0 ltac:(lia) HSv Hv Rr1 Lr Hr4 GR)
        as (r1 & k1 & RUN1 & Q2 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q8 & Q9 & QAG & Hk1).
      set (M1 := uf_step M k k1 (Z_to_bv 64 (lez bsr))) in *.
      assert (HM1 : forall x : word, (U bp - 16 <= U x)%Z -> M1 x = mem x).
      { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). rewrite uf_step_outside by lia. apply HM. exact Hx. }
      assert (FR1 : forall x : word, M1 x <> M x -> uf_foot x) by (intros x; (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply uf_step_frame; lia).
      assert (GR1 : mem_grows M M1) by ((lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply uf_step_grows).
      assert (SZ1 : rdn segs M1 (at_ this 8) 4 = Some (LE4 k1)) by ((lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply uf_step_sz; [lia | exact Hk1 | exact RSZ]).
      assert (SL1 : uf_slots M1) by (apply (uf_slots_keep M M1 RD); intros x Hx; (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply uf_step_outside; lia).
      destruct (uf_tail d M1 r1 v k1 bsw Q2 Q10 Q11 Q12 Q13 Q14 Q15 Q8 Q9 QAG HSv Hv Rw Lw FPC HM1)
        as [(r2 & RUN2 & P2 & P10 & P11 & PAG) | (r2 & d' & bsr' & bsw' & Ed & RUN2 & P2 & P10 & P11 & P12 & P13 & P14 & P15 & P8 & P9 & PAG & B1 & B2 & Rr' & Lr' & Rw' & Lw' & FPC')].
      - left.
        destruct (uf_exit M M1 r2 k k1 0 P2 P10 P11 PAG SL1 ltac:(lia) ltac:(lia) ltac:(lia) SZ1 FR1 GR1) as (r' & M' & s' & RUN & X).
        exists r', M', s'. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; exact RUN |].
        destruct X as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). repeat (split; [first [eassumption | lia]|]). exact A8.
      - right. exists d', M1, r2, (Z_to_bv 64 (lez bsw)), k1, bsr', bsw'. split; [exact Ed|]. split.
        + pose proof (bytes_le_to_Z_bound bsw) as Bw. rewrite Lw in Bw. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bw.
          pose proof (bytes_le_to_Z_nonneg bsw) as Bw0.
          assert (Uw : U (Z_to_bv 64 (lez bsw)) = lez bsw) by (unorm; reflexivity).
          constructor; try assumption; try (rewrite Uw; assumption); try lia.
          eapply mem_grows_trans; [exact GR | exact GR1].
        + split; [| split; [lia | split; [exact FR1 | exact GR1]]].
          eapply msteps_trans; [exact RUN1 | exact RUN2].
    Qed.

    (* [comment removed for export] *)
    Lemma uf_loop : forall (d : nat) (M : word -> option byte) r0 (v : word) (k : Z) (bsr bsw : list byte),
      uf_inv d M r0 v k bsr bsw ->
      exists r' M' (s : Z),
        msteps segs (mkst r0 (at_ base 192) M rom) (mkst r' ra M' rom)
        /\ getr r' 10 = this /\ getr r' 11 = pc0 /\ regs_agree CL regs r'
        /\ (k <= s <= 30)%Z /\ (s <= k + 1 + Z.of_nat d)%Z
        /\ rdn segs M' (at_ this 8) 4 = Some (LE4 s)
        /\ (forall x : word, M' x <> M x -> uf_foot x)
        /\ mem_grows M M'.
    Proof using Hobj Gtop GS Gobj Gframe Gsp H15 H14 H13 H12 H2 H1 Hret bot HCODE.
      induction d as [|d IH]; intros M r0 v k bsr bsw INV.
      - destruct (uf_round 0%nat M r0 v k bsr bsw INV) as [(r' & M' & s & X) | (d' & M1 & r1 & v1 & k1 & bsr' & bsw' & Ed & _)]; [|discriminate Ed].
        exists r', M', s. destruct X as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). repeat (split; [first [eassumption | lia]|]). exact A9.
      - destruct (uf_round (S d) M r0 v k bsr bsw INV) as [(r' & M' & s & X) | (d' & M1 & r1 & v1 & k1 & bsr' & bsw' & Ed & INV1 & RUN1 & Hk1 & FR1 & GR1)].
        + exists r', M', s. destruct X as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). repeat (split; [first [eassumption | lia]|]). exact A9.
        + injection Ed as <-.
          destruct (IH M1 r1 v1 k1 bsr' bsw' INV1) as (r' & M' & s & RUN & P10 & P11 & PAG & S1 & S2 & SZ & FR & GR).
          exists r', M', s. split; [eapply msteps_trans; [exact RUN1 | exact RUN]|].
          repeat (split; [first [eassumption | lia]|]).
          split; [| eapply mem_grows_trans; [exact GR1 | exact GR]].
          intros x Hx. destruct (decide (M1 x = M x)) as [E|NE]; [apply FR; rewrite E; exact Hx | apply FR1; exact NE].
    Qed.

    (* [comment removed for export] *)
    Theorem uf_run : forall (D : nat) (bsr0 bsw0 : list byte),
      rdn segs mem (at_ bp (-8)) 8 = Some bsr0 -> length bsr0 = 8%nat ->
      rdn segs mem (at_ bp (-16)) 8 = Some bsw0 -> length bsw0 = 8%nat ->
      fpc mem (lez bsw0) (U bp) D ->
      exists r' M' (s : Z),
        msteps segs (mkst regs (at_ base 0) mem rom) (mkst r' ra M' rom)
        /\ getr r' 10 = this /\ getr r' 11 = pc0 /\ regs_agree CL regs r'
        /\ (1 <= s <= 30)%Z /\ (s <= 2 + Z.of_nat D)%Z
        /\ rdn segs M' (at_ this 8) 4 = Some (LE4 s)
        /\ rdn segs M' (at_ this 16) 8 = Some (LE8 pc0)
        /\ (forall x : word, M' x <> mem x -> (U sp - 64 <= U x < U sp)%Z \/ ((U this + 8 <= U x < U this + 12)%Z \/ (U this + 16 <= U x < U this + 256)%Z))
        /\ mem_grows mem M'.
    Proof using Hobj Hstk GP Gg RP Rg P Gbot Gtop GS8 GS Gobj Gframe Gsp H15 H14 H13 H12 H11 H10 H2 H1 Hret bot top G56 HCODE g_pgsz.
      intros D bsr0 bsw0 Rr Lr Rw Lw FPC.
      pose proof (u64_range sp) as Hspr. pose proof (u64_range this) as Hth. pose proof (u64_range top) as Htop. pose proof (u64_range bp) as Hbp.
      destruct uf_pro as (r0 & RUN0 & R2 & R10 & R11 & R12 & R13 & R14 & R15 & R8 & R9 & AG0).
      assert (GR2 : mem_grows mem (uf_mem2 mem)) by ((lazymatch goal with |- ?G => let G' := eval unfold uf_mem2, uf_frame in G in change_no_check G' end); repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
      assert (HM2 : forall x : word, (U bp - 16 <= U x)%Z -> uf_mem2 mem x = mem x) by (intros x Hx; apply uf_mem2_outside; lia).
      assert (SZ2 : rdn segs (uf_mem2 mem) (at_ this 8) 4 = Some (LE4 1)).
      { (lazymatch goal with |- ?G => let G' := eval unfold uf_mem2 in G in change_no_check G' end). rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes, !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ].
        pose proof (rdn_wbytes_hit segs (LE4 1) (uf_frame mem) (at_ this 8)) as X. rewrite length_N_to_le_bytes in X. apply X. rewrite at_u by lia. lia. }
      assert (PC2 : rdn segs (uf_mem2 mem) (at_ this 16) 8 = Some (LE8 pc0)).
      { (lazymatch goal with |- ?G => let G' := eval unfold uf_mem2 in G in change_no_check G' end). apply rdn_wbytes_hit8. rewrite at_u by lia. lia. }
      assert (FR2 : forall x : word, uf_mem2 mem x <> mem x -> (U sp - 64 <= U x < U sp)%Z \/ ((U this + 8 <= U x < U this + 12)%Z \/ (U this + 16 <= U x < U this + 256)%Z)).
      { intros x Hx. pose proof (u64_range x).
        destruct (Z.lt_ge_cases (U x) (U sp - 64)); [exfalso; apply Hx; apply uf_mem2_outside; lia|].
        destruct (Z.lt_ge_cases (U x) (U sp)); [left; lia|].
        destruct (Z.lt_ge_cases (U x) (U this + 8)); [exfalso; apply Hx; apply uf_mem2_outside; lia|].
        destruct (Z.lt_ge_cases (U x) (U this + 12)); [right; left; lia|].
        destruct (Z.lt_ge_cases (U x) (U this + 16)); [exfalso; apply Hx; apply uf_mem2_outside; lia|].
        destruct (Z.lt_ge_cases (U x) (U this + 24)); [right; right; lia|].
        exfalso; apply Hx; apply uf_mem2_outside; lia. }
      (* [comment removed for export] *)
      assert (EARLY : forall r1, msteps segs (mkst r0 (at_ base 164) (uf_mem2 mem) rom) (mkst r1 (at_ base 252) (uf_mem2 mem) rom) ->
                getr r1 2 = at_ sp (-64) -> getr r1 10 = this -> getr r1 11 = pc0 -> regs_agree CLX regs r1 ->
                exists r' M' (s : Z),
                  msteps segs (mkst regs (at_ base 0) mem rom) (mkst r' ra M' rom)
                  /\ getr r' 10 = this /\ getr r' 11 = pc0 /\ regs_agree CL regs r'
                  /\ (1 <= s <= 30)%Z /\ (s <= 2 + Z.of_nat D)%Z
                  /\ rdn segs M' (at_ this 8) 4 = Some (LE4 s)
                  /\ rdn segs M' (at_ this 16) 8 = Some (LE8 pc0)
                  /\ (forall x : word, M' x <> mem x -> (U sp - 64 <= U x < U sp)%Z \/ ((U this + 8 <= U x < U this + 12)%Z \/ (U this + 16 <= U x < U this + 256)%Z))
                  /\ mem_grows mem M').
      { intros r1 W Q2 Q10 Q11 QAG.
        destruct (uf_epi (uf_mem2 mem) r1 Q2 Q10 Q11 (uf_mem2_slots mem) QAG) as (r' & RUN & P10 & P11 & PAG).
        exists r', (uf_mem2 mem), 1%Z.
        split; [eapply msteps_trans; [exact RUN0|]; eapply msteps_trans; [exact W | exact RUN] |].
        repeat (split; [first [eassumption | lia] |]). exact GR2. }
      destruct (Z.lt_ge_cases (U bot) (U bp)) as [C1|C1].
      2:{ eapply EARLY. { ab_tk Fo164 D_8ff20 ltac:(condz). wd_refl. } all: gres; try assumption; (lazymatch goal with |- ?G => let G' := eval unfold uf_clobx in G in change_no_check G' end); ra_chain. }
      destruct (Z.lt_ge_cases (U bp) (U top - 16)) as [C2|C2].
      2:{ eapply EARLY.
          { ab_ft Fo164 D_8ff20 ltac:(condz).                (* [comment removed for export] *)
            av Fo168 D_8ff24 (at_ top (-16)) ltac:(reflexivity).   (* [comment removed for export] *)
            ab_tk Fo172 D_8ff28 ltac:(condz).                (* [comment removed for export] *)
            wd_refl. }
          all: gres; try assumption; (lazymatch goal with |- ?G => let G' := eval unfold uf_clobx in G in change_no_check G' end); ra_chain. }
      (* [comment removed for export] *)
      assert (G8 : (U bp mod 8 = 0)%Z).
      { rewrite (Z_div_mod_eq_full (U bp) 16). rewrite GS8, Z.add_0_r.
        replace (16 * (U bp / 16))%Z with ((2 * (U bp / 16)) * 8)%Z by lia. apply Z_mod_mult. }
      assert (W : exists r1, msteps segs (mkst r0 (at_ base 164) (uf_mem2 mem) rom) (mkst r1 (at_ base 192) (uf_mem2 mem) rom)
                   /\ uf_inv D (uf_mem2 mem) r1 bp 1 bsr0 bsw0).
      { wd_eexists. split.
        { ab_ft Fo164 D_8ff20 ltac:(condz).
          av Fo168 D_8ff24 (at_ top (-16)) ltac:(reflexivity).
          ab_ft Fo172 D_8ff28 ltac:(condz).
          av Fo176 D_8ff2c (Z_to_bv 64 0) ltac:(apply v_andi_7_aligned; exact G8).   (* [comment removed for export] *)
          ab_ft Fo180 D_8ff30 ltac:(condz).                (* [comment removed for export] *)
          av Fo184 D_8ff34 (at_ this 16) ltac:(reflexivity).   (* [comment removed for export] *)
          an Fo188 D_8ff38.                                  (* [comment removed for export] *)
          wd_refl. }
        constructor; gres; rewrite ?at_0; try assumption; try reflexivity; try lia.
        - (lazymatch goal with |- ?G => let G' := eval unfold uf_clobx in G in change_no_check G' end). ra_chain.
        - exact (uf_mem2_slots mem). }
      destruct W as (r1 & W & INV).
      destruct (uf_loop D (uf_mem2 mem) r1 bp 1 bsr0 bsw0 INV) as (r' & M' & s & RUN & P10 & P11 & PAG & S1 & S2 & SZ & FR & GR).
      exists r', M', s.
      split; [eapply msteps_trans; [exact RUN0|]; eapply msteps_trans; [exact W | exact RUN] |].
      repeat (split; [first [eassumption | lia] |]).
      split.
      { (* [comment removed for export] *)
        rewrite <- PC2. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx.
        destruct (decide (M' x = uf_mem2 mem x)) as [E|NE]; [exact E|]. exfalso. pose proof (FR x NE) as F. unfold uf_foot in F. lia. }
      split; [| eapply mem_grows_trans; [exact GR2 | exact GR]].
      intros x Hx. destruct (decide (M' x = uf_mem2 mem x)) as [E|NE].
      - apply FR2. rewrite <- E. exact Hx.
      - pose proof (FR x NE) as F. unfold uf_foot in F. right. lia.
    Qed.
  End Run.
End UF.
End FPGen1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPGen1b.
Context {fx : FPState}.

Definition gct_words : list (option (bv 32)) :=
  [Some W_78e2c; Some W_78e30; Some W_78e34; Some W_78e38; Some W_78e3c; Some W_78e40; Some W_78e44; Some W_78e48]%list.
Definition tsd_words : list (option (bv 32)) :=
  [None; None; Some W_714b4; Some W_714b8; Some W_714bc; None]%list.
Definition pgs_words : list (option (bv 32)) :=
  [Some W_fdd24; Some W_fdd28; Some W_fdd2c; Some W_fdd30; Some W_fdd34; Some W_fdd38; Some W_fdd3c]%list.
Definition gct_clob : list reg := [10; 11].

(* [comment removed for export] *)
Record gct_tab := GCT { gt_rb : word; gt_tsd : word; gt_pgs : word }.
Record gct_tab_ok (segs : list Segment) (t : gct_tab) : Prop := GCTOK {
  gto_gct : code_ato segs (gt_rb t) 0x78e2c gct_words;
  gto_tsd : code_ato segs (gt_rb t) 0x714ac tsd_words;
  gto_gaddr : gaddr2 segs (gt_rb t) 0x714ac 10 10 (gt_tsd t);
  gto_jmp : gjump segs (gt_rb t) (0x714ac + 20) (gt_pgs t);
  gto_pgs : code_ato segs (gt_pgs t) 0 pgs_words;
  gto_rb : (U (gt_rb t) mod 2 = 0)%Z /\ (U (gt_rb t) + 2 ^ 24 < 2 ^ 64)%Z }.

(* [comment removed for export] *)
Record gctH (segs : list Segment) (t : gct_tab) (mem : word -> option byte) (sp tp tsdp tctx thr : word) : Prop := GCTH {
  gh_flag : rdn segs mem (gt_tsd t) 1 = Some [Z_to_bv 8 1];
  gh_key : rdn segs mem (at_ (gt_tsd t) 4) 4 = Some (LE4 0);
  gh_tsdp : rdn segs mem (at_ tp (-88)) 8 = Some (LE8 tsdp);
  gh_tctx : rdn segs mem tsdp 8 = Some (LE8 tctx);
  gh_thr : rdn segs mem (at_ tctx 152) 8 = Some (LE8 thr);
  gh_tctx_nz : U tctx <> 0%Z;
  gh_stk : store_ok segs mem (at_ sp (-8)) 8 = true;
  (* [comment removed for export] *)
  gh_sp : (16 <= U sp)%Z /\ (U sp + 8 <= 2 ^ 64)%Z;
  gh_g1 : (U (gt_tsd t) + 8 <= U sp - 16)%Z;
  gh_g2 : (88 <= U tp)%Z /\ (U tp - 80 <= U sp - 16)%Z;
  gh_g3 : (U tsdp + 8 <= U sp - 16)%Z;
  gh_g4 : (U tctx + 160 <= U sp - 16)%Z }.

(* [comment removed for export] *)
Lemma gctH_keep : forall segs t (mem M' : word -> option byte) (sp tp tsdp tctx thr : word),
  gctH segs t mem sp tp tsdp tctx thr ->
  (forall x : word, (U x < U sp - 16)%Z -> M' x = mem x) -> mem_grows mem M' ->
  gctH segs t M' sp tp tsdp tctx thr.
Proof using.
  intros segs t mem M' sp tp tsdp tctx thr [Rf Rk Rt Rc Rth NZ SOK Gsp G1 G2 G3 G4] HM GR.
  pose proof (u64_range tp). pose proof (u64_range tsdp). pose proof (u64_range tctx). pose proof (u64_range (gt_tsd t)). pose proof (u64_range sp).
  split; try assumption.
  - rewrite <- Rf. apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x Hx; apply HM; cbn in Hx; lia].
  - rewrite <- Rk. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply HM; rewrite at_u in Hx by lia; cbn in Hx; lia].
  - rewrite <- Rt. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply HM; rewrite at_u in Hx by lia; cbn in Hx; lia].
  - rewrite <- Rc. apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x Hx; apply HM; cbn in Hx; lia].
  - rewrite <- Rth. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply HM; rewrite at_u in Hx by lia; cbn in Hx; lia].
  - eapply store_ok_mono; [exact GR | exact SOK].
Qed.

Section GCT.
  Variable segs : list Segment.
  Variable t : gct_tab.
  Hypothesis TOK : gct_tab_ok segs t.
  #[local] Abbreviation rb := (gt_rb t).

  Let HG : code_ato segs rb 0x78e2c gct_words := gto_gct _ _ TOK.
  Let HT : code_ato segs rb 0x714ac tsd_words := gto_tsd _ _ TOK.
  Let HP : code_ato segs (gt_pgs t) 0 pgs_words := gto_pgs _ _ TOK.

  Lemma Go0 : fetch_word segs (at_ rb 0x78e2c) = Some W_78e2c.  Proof using HG TOK fx. exact (code_ato_get segs rb 0x78e2c gct_words 0 _ HG eq_refl). Qed.
  Lemma Go4 : fetch_word segs (at_ rb 0x78e30) = Some W_78e30.  Proof using HG TOK fx. exact (code_ato_get segs rb 0x78e2c gct_words 1 _ HG eq_refl). Qed.
  Lemma Go8 : fetch_word segs (at_ rb 0x78e34) = Some W_78e34.  Proof using HG TOK fx. exact (code_ato_get segs rb 0x78e2c gct_words 2 _ HG eq_refl). Qed.
  Lemma Go12 : fetch_word segs (at_ rb 0x78e38) = Some W_78e38.  Proof using HG TOK fx. exact (code_ato_get segs rb 0x78e2c gct_words 3 _ HG eq_refl). Qed.
  Lemma Go16 : fetch_word segs (at_ rb 0x78e3c) = Some W_78e3c.  Proof using HG TOK fx. exact (code_ato_get segs rb 0x78e2c gct_words 4 _ HG eq_refl). Qed.
  Lemma Go20 : fetch_word segs (at_ rb 0x78e40) = Some W_78e40.  Proof using HG TOK fx. exact (code_ato_get segs rb 0x78e2c gct_words 5 _ HG eq_refl). Qed.
  Lemma Go24 : fetch_word segs (at_ rb 0x78e44) = Some W_78e44.  Proof using HG TOK fx. exact (code_ato_get segs rb 0x78e2c gct_words 6 _ HG eq_refl). Qed.
  Lemma Go28 : fetch_word segs (at_ rb 0x78e48) = Some W_78e48.  Proof using HG TOK fx. exact (code_ato_get segs rb 0x78e2c gct_words 7 _ HG eq_refl). Qed.
  Lemma To8 : fetch_word segs (at_ rb 0x714b4) = Some W_714b4.  Proof using HT TOK fx. exact (code_ato_get segs rb 0x714ac tsd_words 2 _ HT eq_refl). Qed.
  Lemma To12 : fetch_word segs (at_ rb 0x714b8) = Some W_714b8.  Proof using HT TOK fx. exact (code_ato_get segs rb 0x714ac tsd_words 3 _ HT eq_refl). Qed.
  Lemma To16 : fetch_word segs (at_ rb 0x714bc) = Some W_714bc.  Proof using HT TOK fx. exact (code_ato_get segs rb 0x714ac tsd_words 4 _ HT eq_refl). Qed.
  Lemma Po0 : fetch_word segs (at_ (gt_pgs t) 0) = Some W_fdd24.  Proof using HP TOK fx. exact (code_ato_get segs _ 0 pgs_words 0 _ HP eq_refl). Qed.
  Lemma Po4 : fetch_word segs (at_ (gt_pgs t) 4) = Some W_fdd28.  Proof using HP TOK fx. exact (code_ato_get segs _ 0 pgs_words 1 _ HP eq_refl). Qed.
  Lemma Po8 : fetch_word segs (at_ (gt_pgs t) 8) = Some W_fdd2c.  Proof using HP TOK fx. exact (code_ato_get segs _ 0 pgs_words 2 _ HP eq_refl). Qed.
  Lemma Po12 : fetch_word segs (at_ (gt_pgs t) 12) = Some W_fdd30.  Proof using HP TOK fx. exact (code_ato_get segs _ 0 pgs_words 3 _ HP eq_refl). Qed.
  Lemma Po16 : fetch_word segs (at_ (gt_pgs t) 16) = Some W_fdd34.  Proof using HP TOK fx. exact (code_ato_get segs _ 0 pgs_words 4 _ HP eq_refl). Qed.
  Lemma Po20 : fetch_word segs (at_ (gt_pgs t) 20) = Some W_fdd38.  Proof using HP TOK fx. exact (code_ato_get segs _ 0 pgs_words 5 _ HP eq_refl). Qed.
  Lemma Po24 : fetch_word segs (at_ (gt_pgs t) 24) = Some W_fdd3c.  Proof using HP TOK fx. exact (code_ato_get segs _ 0 pgs_words 6 _ HP eq_refl). Qed.

  Theorem gct_run : forall mem rom regs (ra sp tp tsdp tctx thr : word),
    gctH segs t mem sp tp tsdp tctx thr ->
    ret_ok ra -> getr regs 1 = ra -> getr regs 2 = sp -> getr regs 4 = tp ->
    exists r,
      msteps segs (mkst regs (at_ rb 0x78e2c) mem rom) (mkst r ra (wbytes mem (at_ sp (-8)) (LE8 ra)) rom)
      /\ getr r 10 = thr /\ getr r 11 = tsdp
      /\ regs_agree (fun x => In x gct_clob) regs r.
  Proof using HP HT HG TOK.
    intros mem rom regs ra sp tp tsdp tctx thr [Rf Rk Rt Rc Rth NZ SOK Gsp G1 G2 G3 G4] Hret H1 H2 H4.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range tp) as Htp. pose proof (u64_range tsdp) as Htsdp.
    pose proof (u64_range tctx) as Htc. pose proof (u64_range (gt_tsd t)) as Htsd.
    destruct (gto_gaddr _ _ TOK) as [gx GA]. pose proof (gto_jmp _ _ TOK) as GJ.
    set (M1 := wbytes mem (at_ sp (-8)) (LE8 ra)).
    assert (HM1 : forall x : word, (U x < U sp - 8 \/ U sp <= U x)%Z -> M1 x = mem x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). rewrite wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. reflexivity. }
    Ltac rdM1 HM1 Hr := apply (rd_same _ _ _ _ _ _ ) || idtac.
    wd_eexists. split; [|split; [|split]].
    - an Go0 D_78e2c.                                   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sd_at with (a := at_ sp (-8));
          [exact Go4 | reflexivity | exact D_78e30 | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia] | gres; rwH; reflexivity | exact SOK ]
        | step_simpl]; vn.                                (* [comment removed for export] *)
      change (wbytes _ _ _) with M1.
      an Go8 D_78e34.                                   (* [comment removed for export] *)
      eapply msteps_trans; [apply GA|]. zlit_at.          (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lbu with (b := Z_to_bv 8 1);
          [exact To8 | reflexivity | exact D_714b4
          | gres; rwH; imm_norm; rewrite ?v_addi_0; rewrite <- Rf; apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x Hx; apply HM1; cbn in Hx; lia] ]
        | step_simpl]; vn.                                (* [comment removed for export] *)
      ab_ft To12 D_714b8 ltac:(condz).                  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := LE4 0) (v := Z_to_bv 64 0);
          [exact To16 | reflexivity | exact D_714bc
          | gres; rwH; imm_norm; rewrite ?at_addi; change (v_addi (gt_tsd t) 4) with (at_ (gt_tsd t) 4); rewrite <- Rk; apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply HM1; rewrite at_u in Hx by lia; cbn in Hx; lia]
          | apply bytes4_small; lia ]
        | step_simpl]; vn.                                (* [comment removed for export] *)
      eapply msteps_trans; [apply GJ|].                   (* [comment removed for export] *)
      rewrite <- (at_0 (gt_pgs t)).
      an Po0 D_fdd24.                                    (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 tsdp) (v := tsdp);
          [exact Po4 | reflexivity | exact D_fdd28
          | gres; rwH; imm_norm; change (v_addi tp (-88)) with (at_ tp (-88)); rewrite <- Rt; apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply HM1; rewrite at_u in Hx by lia; cbn in Hx; lia]
          | apply bytes_le_to_Z_8 ]
        | step_simpl]; vn.                                (* [comment removed for export] *)
      an Po8 D_fdd2c.                                    (* [comment removed for export] *)
      an Po12 D_fdd30.                                   (* [comment removed for export] *)
      av Po16 D_fdd34 tsdp ltac:(rewrite v_add_0_r; reflexivity).   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 tctx) (v := tctx);
          [exact Po20 | reflexivity | exact D_fdd38
          | gres; rwH; imm_norm; rewrite ?v_addi_0; rewrite <- Rc; apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x Hx; apply HM1; cbn in Hx; lia]
          | apply bytes_le_to_Z_8 ]
        | step_simpl]; vn.                                (* [comment removed for export] *)
      assert (RA1 : ret_ok (at_ rb 0x78e38)) by (destruct (gto_rb _ _ TOK) as [E1 E2]; apply ret_ok_at; [exact E1 | reflexivity | pose proof (u64_range rb); lia]).
      aret Po24 D_fdd3c (at_ rb 0x78e38).                (* [comment removed for export] *)
      ab_ft Go12 D_78e38 ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, bv_eqb in G in change_no_check G' end); apply Z.eqb_neq; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); exact NZ || (unorm; exact NZ)).   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 thr) (v := thr);
          [exact Go16 | reflexivity | exact D_78e3c
          | gres; rwH; imm_norm; change (v_addi tctx 152) with (at_ tctx 152); rewrite <- Rth; apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply HM1; rewrite at_u in Hx by lia; cbn in Hx; lia]
          | apply bytes_le_to_Z_8 ]
        | step_simpl]; vn.                                (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 ra) (v := ra);
          [exact Go20 | reflexivity | exact D_78e40
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply rdn_wbytes_hit8; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]
          | apply bytes_le_to_Z_8 ]
        | step_simpl]; vn.                                (* [comment removed for export] *)
      an Go24 D_78e44.                                    (* [comment removed for export] *)
      aret Go28 D_78e48 ra.                               (* [comment removed for export] *)
      wd_refl.
    - gres. reflexivity.
    - gres. reflexivity.
    - apply (regs_agree_strengthen gct_clob [1; 2; 10; 11] regs).
      + ra_solve.
      + intros i Hi Hni. cbn [In] in Hi.
        repeat (destruct Hi as [<-|Hi]; [gres; rwH; rewrite ?at_addi, ?at_0; first [reflexivity | symmetry; assumption | f_equal; lia | exfalso; apply Hni; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto] |]).
        destruct Hi.
  Qed.
End GCT.
End FPGen1b.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPGen1c.
Context {fx : FPState}.

Definition stt_words : list (option (bv 32)) :=
  [Some W_78ff0; Some W_78ff4; Some W_78ff8; None; None; None; None; None; None; None; None; None; None; None; None; None;
   Some W_79030; Some W_79034; Some W_79038; Some W_7903c; Some W_79040; Some W_79044]%list.
Definition stb_words : list (option (bv 32)) :=
  [Some W_79048; Some W_7904c; Some W_79050; None; None; None; None; None; None; None; None; None; None; None; None; None;
   Some W_79088; Some W_7908c; Some W_79090; Some W_79094; Some W_79098; Some W_7909c]%list.
Definition ain_words : list (option (bv 32)) := [None; None; Some W_75724; Some W_75728; Some W_7572c; Some W_75730]%list.

Lemma v_and_m1_l : forall x : word, v_and (Z_to_bv 64 (-1)) x = x.
Proof using.
  intros x. (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end). change (bv_unsigned (Z_to_bv 64 (-1))) with (Z.ones 64).
  pose proof (u64_range x). rewrite Z.land_comm, Z.land_ones_low.
  - apply Z_to_bv_bv_unsigned.
  - lia.
  - destruct (Z.eq_dec (bv_unsigned x) 0) as [E|NE]; [rewrite E; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. apply Z.log2_lt_pow2; lia.
Qed.

Section STK.
  Variable segs : list Segment.
  Variable rb : word.
  Hypothesis HT : code_ato segs rb 0x78ff0 stt_words.
  Hypothesis HB : code_ato segs rb 0x79048 stb_words.

  Lemma So0 : fetch_word segs (at_ rb 0x78ff0) = Some W_78ff0.  Proof using HT. exact (code_ato_get segs rb 0x78ff0 stt_words 0 _ HT eq_refl). Qed.
  Lemma So4 : fetch_word segs (at_ rb 0x78ff4) = Some W_78ff4.  Proof using HT. exact (code_ato_get segs rb 0x78ff0 stt_words 1 _ HT eq_refl). Qed.
  Lemma So8 : fetch_word segs (at_ rb 0x78ff8) = Some W_78ff8.  Proof using HT. exact (code_ato_get segs rb 0x78ff0 stt_words 2 _ HT eq_refl). Qed.
  Lemma So64 : fetch_word segs (at_ rb 0x79030) = Some W_79030.  Proof using HT. exact (code_ato_get segs rb 0x78ff0 stt_words 16 _ HT eq_refl). Qed.
  Lemma So68 : fetch_word segs (at_ rb 0x79034) = Some W_79034.  Proof using HT. exact (code_ato_get segs rb 0x78ff0 stt_words 17 _ HT eq_refl). Qed.
  Lemma So72 : fetch_word segs (at_ rb 0x79038) = Some W_79038.  Proof using HT. exact (code_ato_get segs rb 0x78ff0 stt_words 18 _ HT eq_refl). Qed.
  Lemma So76 : fetch_word segs (at_ rb 0x7903c) = Some W_7903c.  Proof using HT. exact (code_ato_get segs rb 0x78ff0 stt_words 19 _ HT eq_refl). Qed.
  Lemma So80 : fetch_word segs (at_ rb 0x79040) = Some W_79040.  Proof using HT. exact (code_ato_get segs rb 0x78ff0 stt_words 20 _ HT eq_refl). Qed.
  Lemma So84 : fetch_word segs (at_ rb 0x79044) = Some W_79044.  Proof using HT. exact (code_ato_get segs rb 0x78ff0 stt_words 21 _ HT eq_refl). Qed.
  Lemma Bo0 : fetch_word segs (at_ rb 0x79048) = Some W_79048.  Proof using HB. exact (code_ato_get segs rb 0x79048 stb_words 0 _ HB eq_refl). Qed.
  Lemma Bo4 : fetch_word segs (at_ rb 0x7904c) = Some W_7904c.  Proof using HB. exact (code_ato_get segs rb 0x79048 stb_words 1 _ HB eq_refl). Qed.
  Lemma Bo8 : fetch_word segs (at_ rb 0x79050) = Some W_79050.  Proof using HB. exact (code_ato_get segs rb 0x79048 stb_words 2 _ HB eq_refl). Qed.
  Lemma Bo64 : fetch_word segs (at_ rb 0x79088) = Some W_79088.  Proof using HB. exact (code_ato_get segs rb 0x79048 stb_words 16 _ HB eq_refl). Qed.
  Lemma Bo68 : fetch_word segs (at_ rb 0x7908c) = Some W_7908c.  Proof using HB. exact (code_ato_get segs rb 0x79048 stb_words 17 _ HB eq_refl). Qed.
  Lemma Bo72 : fetch_word segs (at_ rb 0x79090) = Some W_79090.  Proof using HB. exact (code_ato_get segs rb 0x79048 stb_words 18 _ HB eq_refl). Qed.
  Lemma Bo76 : fetch_word segs (at_ rb 0x79094) = Some W_79094.  Proof using HB. exact (code_ato_get segs rb 0x79048 stb_words 19 _ HB eq_refl). Qed.
  Lemma Bo80 : fetch_word segs (at_ rb 0x79098) = Some W_79098.  Proof using HB. exact (code_ato_get segs rb 0x79048 stb_words 20 _ HB eq_refl). Qed.
  Lemma Bo84 : fetch_word segs (at_ rb 0x7909c) = Some W_7909c.  Proof using HB. exact (code_ato_get segs rb 0x79048 stb_words 21 _ HB eq_refl). Qed.

  (* [comment removed for export] *)
  Record stkH (mem : word -> option byte) (thr top bot : word) : Prop := STKH {
    sh_sw : rdn segs mem (at_ thr 40) 1 = Some [Z_to_bv 8 0];
    sh_top : rdn segs mem (at_ thr 8) 8 = Some (LE8 top);
    sh_bot : rdn segs mem (at_ thr 16) 8 = Some (LE8 bot);
    sh_lt : (U bot < U top)%Z;
    sh_rng : (U thr + 48 <= 2 ^ 64)%Z }.

  Ltac cld8 F D vv Hr :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi; zlit_at; Hr | apply bytes_le_to_Z_8]
      | step_simpl]; vn.

  Theorem stt_run : forall mem rom regs (ra thr top bot : word),
    stkH mem thr top bot -> ret_ok ra -> getr regs 1 = ra -> getr regs 10 = thr ->
    exists r, msteps segs (mkst regs (at_ rb 0x78ff0) mem rom) (mkst r ra mem rom)
      /\ getr r 10 = top /\ getr r 11 = top /\ regs_agree (fun x => In x [10; 11]) regs r.
  Proof using HT.
    intros mem rom regs ra thr top bot [Rsw Rt Rb LT RG] Hret H1 H10. pose proof (u64_range thr). pose proof (u64_range top). pose proof (u64_range bot).
    wd_eexists. split; [|split; [|split]].
    - chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0); [exact So0 | reflexivity | exact D_78ff0 | gres; rwH; imm_norm; exact Rsw]
        | step_simpl]; vn.                                (* [comment removed for export] *)
      afence So4 D_78ff4.                                 (* [comment removed for export] *)
      ab_tk So8 D_78ff8 ltac:(condz).                    (* [comment removed for export] *)
      cld8 So64 D_79030 top ltac:(exact Rt).              (* [comment removed for export] *)
      cld8 So68 D_79034 bot ltac:(exact Rb).              (* [comment removed for export] *)
      an So72 D_79038.                                    (* [comment removed for export] *)
      an So76 D_7903c.                                    (* [comment removed for export] *)
      an So80 D_79040.                                    (* [comment removed for export] *)
      aret So84 D_79044 ra.
      wd_refl.
    - gres. (lazymatch goal with |- ?G => let G' := eval unfold v_sltu in G in change_no_check G' end). replace (c_ltu bot top) with true by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold c_ltu, bv_ltu in G in change_no_check G' end); apply Z.ltb_lt; exact LT).
      change (v_sub (Z_to_bv 64 0) (Z_to_bv 64 1)) with (Z_to_bv 64 (-1)). apply v_and_m1_l.
    - gres; reflexivity.
    - ra_solve.
  Qed.

  Theorem stb_run : forall mem rom regs (ra thr top bot : word),
    stkH mem thr top bot -> ret_ok ra -> getr regs 1 = ra -> getr regs 10 = thr ->
    exists r, msteps segs (mkst regs (at_ rb 0x79048) mem rom) (mkst r ra mem rom)
      /\ getr r 10 = bot /\ getr r 11 = Z_to_bv 64 (-1) /\ regs_agree (fun x => In x [10; 11]) regs r.
  Proof using HB.
    intros mem rom regs ra thr top bot [Rsw Rt Rb LT RG] Hret H1 H10. pose proof (u64_range thr). pose proof (u64_range top). pose proof (u64_range bot).
    wd_eexists. split; [|split; [|split]].
    - chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0); [exact Bo0 | reflexivity | exact D_79048 | gres; rwH; imm_norm; exact Rsw]
        | step_simpl]; vn.                                (* [comment removed for export] *)
      afence Bo4 D_7904c.
      ab_tk Bo8 D_79050 ltac:(condz).                    (* [comment removed for export] *)
      cld8 Bo64 D_79088 top ltac:(exact Rt).              (* [comment removed for export] *)
      cld8 Bo68 D_7908c bot ltac:(exact Rb).              (* [comment removed for export] *)
      an Bo72 D_79090.                                    (* [comment removed for export] *)
      an Bo76 D_79094.                                    (* [comment removed for export] *)
      an Bo80 D_79098.                                    (* [comment removed for export] *)
      aret Bo84 D_7909c ra.
      wd_refl.
    - gres. (lazymatch goal with |- ?G => let G' := eval unfold v_sltu in G in change_no_check G' end). replace (c_ltu bot top) with true by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold c_ltu, bv_ltu in G in change_no_check G' end); apply Z.ltb_lt; exact LT).
      change (v_sub (Z_to_bv 64 0) (Z_to_bv 64 1)) with (Z_to_bv 64 (-1)). apply v_and_m1_l.
    - gres. (lazymatch goal with |- ?G => let G' := eval unfold v_sltu in G in change_no_check G' end). replace (c_ltu bot top) with true by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold c_ltu, bv_ltu in G in change_no_check G' end); apply Z.ltb_lt; exact LT). reflexivity.
    - ra_solve.
  Qed.
End STK.

Lemma stkH_keep : forall segs (mem M' : word -> option byte) (thr top bot : word),
  stkH segs mem thr top bot -> (forall x : word, (U thr <= U x < U thr + 48)%Z -> M' x = mem x) -> stkH segs M' thr top bot.
Proof using.
  intros segs mem M' thr top bot [Rsw Rt Rb LT RG] HM. pose proof (u64_range thr).
  split; try assumption.
  - rewrite <- Rsw. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply HM; rewrite at_u in Hx by lia; cbn in Hx; lia].
  - rewrite <- Rt. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply HM; rewrite at_u in Hx by lia; cbn in Hx; lia].
  - rewrite <- Rb. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply HM; rewrite at_u in Hx by lia; cbn in Hx; lia].
Qed.

Section AIN.
  Variable segs : list Segment.
  Variable rb : word.
  Variable g_inited : Z.
  Hypothesis HA : code_ato segs rb 0x7571c ain_words.
  Hypothesis GA : gloadb segs rb 0x7571c 10 g_inited.
  Lemma Ao8 : fetch_word segs (at_ rb 0x75724) = Some W_75724.  Proof using HA. exact (code_ato_get segs rb 0x7571c ain_words 2 _ HA eq_refl). Qed.
  Lemma Ao12 : fetch_word segs (at_ rb 0x75728) = Some W_75728.  Proof using HA. exact (code_ato_get segs rb 0x7571c ain_words 3 _ HA eq_refl). Qed.
  Lemma Ao16 : fetch_word segs (at_ rb 0x7572c) = Some W_7572c.  Proof using HA. exact (code_ato_get segs rb 0x7571c ain_words 4 _ HA eq_refl). Qed.
  Lemma Ao20 : fetch_word segs (at_ rb 0x75730) = Some W_75730.  Proof using HA. exact (code_ato_get segs rb 0x7571c ain_words 5 _ HA eq_refl). Qed.

  (* [comment removed for export] *)
  Theorem ain_run : forall mem rom regs (ra : word),
    rdn segs mem (Z_to_bv 64 g_inited) 1 = Some [Z_to_bv 8 1] ->
    ret_ok ra -> getr regs 1 = ra ->
    exists r, msteps segs (mkst regs (at_ rb 0x7571c) mem rom) (mkst r ra mem rom)
      /\ getr r 10 = Z_to_bv 64 1 /\ regs_agree (fun x => In x [10]) regs r.
  Proof using GA HA.
    intros mem rom regs ra Rin Hret H1.
    wd_eexists. split; [|split].
    - eapply msteps_trans; [eapply GA; exact Rin|]. zlit_at.
      afence Ao8 D_75724.
      an Ao12 D_75728.                                    (* [comment removed for export] *)
      an Ao16 D_7572c.                                    (* [comment removed for export] *)
      aret Ao20 D_75730 ra.
      wd_refl.
    - gres. reflexivity.
    - ra_solve.
  Qed.
End AIN.
End FPGen1c.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPGen1d.
Context {fx : FPState}.

Definition ui_words : list (option (bv 32)) :=
  [Some W_773c4; Some W_773c8; Some W_773cc; Some W_773d0; Some W_773d4; Some W_773d8; Some W_773dc; Some W_773e0;
   Some W_773e4; Some W_773e8; Some W_773ec; Some W_773f0; Some W_773f4; Some W_773f8; Some W_773fc; Some W_77400;
   Some W_77404; Some W_77408; Some W_7740c; Some W_77410; Some W_77414; Some W_77418; Some W_7741c; Some W_77420;
   Some W_77424; Some W_77428; Some W_7742c; Some W_77430; Some W_77434; Some W_77438; Some W_7743c; Some W_77440;
   Some W_77444; Some W_77448; Some W_7744c; Some W_77450; Some W_77454; Some W_77458; Some W_7745c; Some W_77460;
   Some W_77464; Some W_77468; Some W_7746c; Some W_77470; Some W_77474; Some W_77478; Some W_7747c; Some W_77480;
   Some W_77484; Some W_77488; Some W_7748c; Some W_77490; Some W_77494; Some W_77498; Some W_7749c; Some W_774a0;
   Some W_774a4; Some W_774a8; Some W_774ac; Some W_774b0; Some W_774b4; Some W_774b8; Some W_774bc; Some W_774c0;
   Some W_774c4; Some W_774c8; Some W_774cc; Some W_774d0; Some W_774d4; Some W_774d8; Some W_774dc; Some W_774e0;
   Some W_774e4; Some W_774e8; Some W_774ec; Some W_774f0; Some W_774f4; Some W_774f8; Some W_774fc; Some W_77500;
   Some W_77504; Some W_77508; Some W_7750c; Some W_77510]%list.
Definition uw_words : list (option (bv 32)) :=
  [Some W_904d8; Some W_904dc; Some W_904e0; Some W_904e4; Some W_904e8; Some W_904ec; Some W_904f0;
   Some W_904f4; Some W_904f8; Some W_904fc; Some W_90500; Some W_90504; Some W_90508; Some W_9050c;
   Some W_90510; Some W_90514; Some W_90518; Some W_9051c; Some W_90520; Some W_90524; Some W_90528;
   Some W_9052c; Some W_90530; Some W_90534; Some W_90538; Some W_9053c; Some W_90540; Some W_90544;
   Some W_90548; Some W_9054c; Some W_90550; Some W_90554; Some W_90558; Some W_9055c; Some W_90560;
   Some W_90564; Some W_90568; Some W_9056c; Some W_90570; Some W_90574; Some W_90578; Some W_9057c;
   Some W_90580; Some W_90584; Some W_90588; Some W_9058c; Some W_90590; Some W_90594; Some W_90598;
   Some W_9059c; Some W_905a0; Some W_905a4; Some W_905a8; Some W_905ac; Some W_905b0; Some W_905b4;
   Some W_905b8; Some W_905bc; Some W_905c0; Some W_905c4; Some W_905c8; Some W_905cc; Some W_905d0;
   Some W_905d4; Some W_905d8; Some W_905dc; Some W_905e0; Some W_905e4; Some W_905e8; Some W_905ec]%list.

(* [comment removed for export] *)
Definition ui_clob : list reg := [5; 6; 10; 11; 12; 13; 14; 15; 16; 17].
Definition ui_clobx : list reg := [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 5; 6; 10; 11; 12; 13; 14; 15; 16; 17].

(* [comment removed for export] *)
Record ui_tab := UIT { ut_rb : word; ut_gct : gct_tab; ut_g_inited : Z; ut_g_pgsz : Z;
                        ut_img_lo : Z; ut_img_hi : Z   (* [comment removed for export] *) }.
Record ui_tab_ok (segs : list Segment) (t : ui_tab) : Prop := UITOK {
  uto_ui : code_ato segs (ut_rb t) 0x773c4 ui_words;
  uto_uw : code_ato segs (ut_rb t) 0x904d8 uw_words;
  uto_uf : code_ato segs (at_ (ut_rb t) 0x8fe7c) 0 uf_words;
  uto_uf56 : gload2 segs (at_ (ut_rb t) 0x8fe7c) 56 13 18 (ut_g_pgsz t);
  uto_gct : gct_tab_ok segs (ut_gct t);
  uto_gct_rb : gt_rb (ut_gct t) = ut_rb t;
  uto_stt : code_ato segs (ut_rb t) 0x78ff0 stt_words;
  uto_stb : code_ato segs (ut_rb t) 0x79048 stb_words;
  uto_ain : code_ato segs (ut_rb t) 0x7571c ain_words;
  uto_ainb : gloadb segs (ut_rb t) 0x7571c 10 (ut_g_inited t);
  uto_rb : (U (ut_rb t) mod 2 = 0)%Z /\ (U (ut_rb t) + 2 ^ 24 < 2 ^ 64)%Z }.

(* [comment removed for export] *)
Record uiH (segs : list Segment) (t : ui_tab) (mem : word -> option byte) (sp this bp thr P : word) : Prop := UIH {
  uh_inited : rdn segs mem (Z_to_bv 64 (ut_g_inited t)) 1 = Some [Z_to_bv 8 1];
  uh_unw : rdn segs mem (at_ thr 3168) 1 = Some [Z_to_bv 8 0];
  uh_unw_ok : store_ok segs mem (at_ thr 3168) 1 = true;
  uh_pg : rdn segs mem (Z_to_bv 64 (ut_g_pgsz t)) 8 = Some (LE8 P);
  uh_P : rdn segs mem P 8 = Some (LE8 (Z_to_bv 64 4096));
  uh_stk : store_ok segs mem (at_ sp (-144)) 144 = true;
  uh_obj : store_ok segs mem (at_ this 8) 2056 = true;
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  uh_g0 : ((ut_img_lo t <= ut_g_inited t /\ ut_g_inited t + 1 <= ut_img_hi t)
           /\ (ut_img_lo t <= ut_g_pgsz t /\ ut_g_pgsz t + 8 <= ut_img_hi t)
           /\ (ut_img_lo t <= U P /\ U P + 8 <= ut_img_hi t)
           /\ (0 <= ut_img_lo t /\ ut_img_hi t <= 4294967296))%Z;
  uh_g1 : (2 ^ 32 + 144 <= U sp)%Z /\ (U sp <= U this)%Z /\ (U this + 2064 <= U bp - 16)%Z /\ (U bp + 16 <= 2 ^ 47)%Z /\ (U bp mod 16 = 0)%Z;
  uh_g2 : ((U thr + 4096 <= ut_img_lo t \/ ut_img_hi t <= U thr) /\ 4096 <= U thr /\ U thr + 4096 <= U sp - 144)%Z }.

Section UI.
  Variable segs : list Segment.
  Variable t : ui_tab.
  Hypothesis TOK : ui_tab_ok segs t.
  #[local] Abbreviation rb := (ut_rb t).
  Let HUI : code_ato segs rb 0x773c4 ui_words := uto_ui _ _ TOK.
  Let HUW : code_ato segs rb 0x904d8 uw_words := uto_uw _ _ TOK.

  Lemma If7ca8 : fetch_word segs (at_ rb 0x773c4) = Some W_773c4.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 0 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7cac : fetch_word segs (at_ rb 0x773c8) = Some W_773c8.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 1 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7cb0 : fetch_word segs (at_ rb 0x773cc) = Some W_773cc.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 2 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7cb4 : fetch_word segs (at_ rb 0x773d0) = Some W_773d0.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 3 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7cb8 : fetch_word segs (at_ rb 0x773d4) = Some W_773d4.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 4 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7cbc : fetch_word segs (at_ rb 0x773d8) = Some W_773d8.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 5 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7cc0 : fetch_word segs (at_ rb 0x773dc) = Some W_773dc.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 6 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7cc4 : fetch_word segs (at_ rb 0x773e0) = Some W_773e0.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 7 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7cc8 : fetch_word segs (at_ rb 0x773e4) = Some W_773e4.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 8 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7ccc : fetch_word segs (at_ rb 0x773e8) = Some W_773e8.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 9 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7cd0 : fetch_word segs (at_ rb 0x773ec) = Some W_773ec.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 10 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7cd4 : fetch_word segs (at_ rb 0x773f0) = Some W_773f0.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 11 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7cd8 : fetch_word segs (at_ rb 0x773f4) = Some W_773f4.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 12 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7cdc : fetch_word segs (at_ rb 0x773f8) = Some W_773f8.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 13 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7ce0 : fetch_word segs (at_ rb 0x773fc) = Some W_773fc.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 14 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7ce4 : fetch_word segs (at_ rb 0x77400) = Some W_77400.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 15 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7ce8 : fetch_word segs (at_ rb 0x77404) = Some W_77404.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 16 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7cec : fetch_word segs (at_ rb 0x77408) = Some W_77408.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 17 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7cf0 : fetch_word segs (at_ rb 0x7740c) = Some W_7740c.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 18 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7cf4 : fetch_word segs (at_ rb 0x77410) = Some W_77410.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 19 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7cf8 : fetch_word segs (at_ rb 0x77414) = Some W_77414.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 20 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7cfc : fetch_word segs (at_ rb 0x77418) = Some W_77418.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 21 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7d00 : fetch_word segs (at_ rb 0x7741c) = Some W_7741c.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 22 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7d04 : fetch_word segs (at_ rb 0x77420) = Some W_77420.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 23 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7d08 : fetch_word segs (at_ rb 0x77424) = Some W_77424.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 24 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7d0c : fetch_word segs (at_ rb 0x77428) = Some W_77428.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 25 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7d10 : fetch_word segs (at_ rb 0x7742c) = Some W_7742c.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 26 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7d14 : fetch_word segs (at_ rb 0x77430) = Some W_77430.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 27 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7d18 : fetch_word segs (at_ rb 0x77434) = Some W_77434.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 28 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7d1c : fetch_word segs (at_ rb 0x77438) = Some W_77438.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 29 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7d20 : fetch_word segs (at_ rb 0x7743c) = Some W_7743c.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 30 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7d24 : fetch_word segs (at_ rb 0x77440) = Some W_77440.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 31 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7d28 : fetch_word segs (at_ rb 0x77444) = Some W_77444.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 32 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7d2c : fetch_word segs (at_ rb 0x77448) = Some W_77448.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 33 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7d30 : fetch_word segs (at_ rb 0x7744c) = Some W_7744c.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 34 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7d34 : fetch_word segs (at_ rb 0x77450) = Some W_77450.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 35 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7d38 : fetch_word segs (at_ rb 0x77454) = Some W_77454.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 36 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7d3c : fetch_word segs (at_ rb 0x77458) = Some W_77458.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 37 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7d40 : fetch_word segs (at_ rb 0x7745c) = Some W_7745c.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 38 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7d44 : fetch_word segs (at_ rb 0x77460) = Some W_77460.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 39 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7d48 : fetch_word segs (at_ rb 0x77464) = Some W_77464.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 40 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7d4c : fetch_word segs (at_ rb 0x77468) = Some W_77468.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 41 _ HUI eq_refl). Qed.



























   (* [comment removed for export] *)
  Lemma If7dc0 : fetch_word segs (at_ rb 0x774dc) = Some W_774dc.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 70 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7dc4 : fetch_word segs (at_ rb 0x774e0) = Some W_774e0.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 71 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7dc8 : fetch_word segs (at_ rb 0x774e4) = Some W_774e4.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 72 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7dcc : fetch_word segs (at_ rb 0x774e8) = Some W_774e8.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 73 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7dd0 : fetch_word segs (at_ rb 0x774ec) = Some W_774ec.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 74 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7dd4 : fetch_word segs (at_ rb 0x774f0) = Some W_774f0.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 75 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7dd8 : fetch_word segs (at_ rb 0x774f4) = Some W_774f4.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 76 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7ddc : fetch_word segs (at_ rb 0x774f8) = Some W_774f8.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 77 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7de0 : fetch_word segs (at_ rb 0x774fc) = Some W_774fc.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 78 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7de4 : fetch_word segs (at_ rb 0x77500) = Some W_77500.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 79 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7de8 : fetch_word segs (at_ rb 0x77504) = Some W_77504.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 80 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7dec : fetch_word segs (at_ rb 0x77508) = Some W_77508.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 81 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7df0 : fetch_word segs (at_ rb 0x7750c) = Some W_7750c.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 82 _ HUI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7df4 : fetch_word segs (at_ rb 0x77510) = Some W_77510.  Proof using HUI TOK fx. exact (code_ato_get segs rb 0x773c4 ui_words 83 _ HUI eq_refl). Qed.   (* [comment removed for export] *)

  Lemma I114484 : fetch_word segs (at_ rb 0x904d8) = Some W_904d8.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 0 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I114488 : fetch_word segs (at_ rb 0x904dc) = Some W_904dc.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 1 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I11448c : fetch_word segs (at_ rb 0x904e0) = Some W_904e0.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 2 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I114490 : fetch_word segs (at_ rb 0x904e4) = Some W_904e4.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 3 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I114494 : fetch_word segs (at_ rb 0x904e8) = Some W_904e8.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 4 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I114498 : fetch_word segs (at_ rb 0x904ec) = Some W_904ec.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 5 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I11449c : fetch_word segs (at_ rb 0x904f0) = Some W_904f0.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 6 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I1144a0 : fetch_word segs (at_ rb 0x904f4) = Some W_904f4.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 7 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I1144a4 : fetch_word segs (at_ rb 0x904f8) = Some W_904f8.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 8 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I1144a8 : fetch_word segs (at_ rb 0x904fc) = Some W_904fc.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 9 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I1144ac : fetch_word segs (at_ rb 0x90500) = Some W_90500.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 10 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I1144b0 : fetch_word segs (at_ rb 0x90504) = Some W_90504.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 11 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I1144b4 : fetch_word segs (at_ rb 0x90508) = Some W_90508.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 12 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I1144b8 : fetch_word segs (at_ rb 0x9050c) = Some W_9050c.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 13 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I1144bc : fetch_word segs (at_ rb 0x90510) = Some W_90510.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 14 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I1144c0 : fetch_word segs (at_ rb 0x90514) = Some W_90514.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 15 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I1144c4 : fetch_word segs (at_ rb 0x90518) = Some W_90518.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 16 _ HUW eq_refl). Qed.












   (* [comment removed for export] *)
  Lemma I1144fc : fetch_word segs (at_ rb 0x90550) = Some W_90550.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 30 _ HUW eq_refl). Qed.
























   (* [comment removed for export] *)
  Lemma I114564 : fetch_word segs (at_ rb 0x905b8) = Some W_905b8.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 56 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I114568 : fetch_word segs (at_ rb 0x905bc) = Some W_905bc.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 57 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I11456c : fetch_word segs (at_ rb 0x905c0) = Some W_905c0.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 58 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I114570 : fetch_word segs (at_ rb 0x905c4) = Some W_905c4.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 59 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I114574 : fetch_word segs (at_ rb 0x905c8) = Some W_905c8.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 60 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I114578 : fetch_word segs (at_ rb 0x905cc) = Some W_905cc.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 61 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I11457c : fetch_word segs (at_ rb 0x905d0) = Some W_905d0.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 62 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I114580 : fetch_word segs (at_ rb 0x905d4) = Some W_905d4.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 63 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I114584 : fetch_word segs (at_ rb 0x905d8) = Some W_905d8.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 64 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I114588 : fetch_word segs (at_ rb 0x905dc) = Some W_905dc.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 65 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I11458c : fetch_word segs (at_ rb 0x905e0) = Some W_905e0.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 66 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I114590 : fetch_word segs (at_ rb 0x905e4) = Some W_905e4.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 67 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I114594 : fetch_word segs (at_ rb 0x905e8) = Some W_905e8.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 68 _ HUW eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I114598 : fetch_word segs (at_ rb 0x905ec) = Some W_905ec.  Proof using HUW TOK fx. exact (code_ato_get segs rb 0x904d8 uw_words 69 _ HUW eq_refl). Qed.   (* [comment removed for export] *)


  Variables (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ra sp tp this pc0 bp fast thr top bot tsdp tctx P : word).
  Hypothesis Hret : ret_ok ra.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H4 : getr regs 4 = tp.
  Hypothesis H10 : getr regs 10 = this.
  Hypothesis H11 : getr regs 11 = pc0.
  Hypothesis H12 : getr regs 12 = bp.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 0.
  Hypothesis H14 : getr regs 14 = fast.
  Hypothesis H15 : getr regs 15 = Z_to_bv 64 30.
  Hypothesis Hfast : U fast <> 0%Z.
  Hypothesis UH : uiH segs t mem sp this bp thr P.
  Hypothesis GH : gctH segs (ut_gct t) mem (at_ sp (-80)) tp tsdp tctx thr.
  Hypothesis SH : stkH segs mem thr top bot.
  Hypothesis Gtop : (4096 <= U top <= 2 ^ 47)%Z.

  #[local] Abbreviation CL := (fun r => In r ui_clob).
  #[local] Abbreviation CLX := (fun r => In r ui_clobx).

  (* [comment removed for export] *)
  Definition ui_m1 : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
      (at_ sp (-8)) (LE8 ra)) (at_ sp (-16)) (LE8 (getr regs 8))) (at_ sp (-24)) (LE8 (getr regs 9)))
      (at_ sp (-32)) (LE8 (getr regs 18))) (at_ sp (-40)) (LE8 (getr regs 19))) (at_ sp (-48)) (LE8 (getr regs 20)))
      (at_ sp (-56)) (LE8 (getr regs 21))) (at_ sp (-64)) (LE8 (getr regs 22))) (at_ sp (-72)) (LE8 (getr regs 23)))
      (at_ sp (-80)) (LE8 (getr regs 24))) (at_ this 8) (LE4 0).

  Lemma ui_m1_outside : forall x : word,
    (U x < U sp - 80)%Z \/ (U sp <= U x < U this + 8)%Z \/ (U this + 12 <= U x)%Z -> ui_m1 x = mem x.
  Proof using UH P thr bp t segs.
    intros x Hx. destruct UH as [_ _ _ _ _ _ _ G0 G1 G2]. pose proof (u64_range sp). pose proof (u64_range this). (lazymatch goal with |- ?G => let G' := eval unfold ui_m1 in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. reflexivity.
  Qed.
  Lemma ui_m1_slots : forall (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19);
               (-48, getr regs 20); (-56, getr regs 21); (-64, getr regs 22); (-72, getr regs 23); (-80, getr regs 24)]%Z ->
    rdn segs ui_m1 (at_ sp k) 8 = Some (LE8 v).
  Proof using UH P thr bp t.
    intros k v Hin. destruct UH as [_ _ _ _ _ _ _ G0 G1 G2]. pose proof (u64_range sp). pose proof (u64_range this). (lazymatch goal with |- ?G => let G' := eval unfold ui_m1 in G in change_no_check G' end).
    cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
  Qed.

  Ltac sokS Hs lo N :=
    repeat (eapply store_ok_mono; [apply wbytes_grows|]);
    eapply (store_ok_sub segs mem lo _ N); [rewrite at_u; lia | exact Hs | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia].
  Ltac fsd8 F D aa Hs lo N :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | sokS Hs lo N ]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  Lemma uiA :
    exists r,
      msteps segs (mkst regs (at_ rb 0x773c4) mem rom) (mkst r (at_ rb 0x7571c) ui_m1 rom)
      /\ getr r 1 = at_ rb 0x77410 /\ getr r 2 = at_ sp (-80) /\ getr r 4 = tp
      /\ getr r 9 = Z_to_bv 64 30 /\ getr r 21 = fast /\ getr r 20 = Z_to_bv 64 0 /\ getr r 8 = bp /\ getr r 18 = pc0 /\ getr r 19 = this
      /\ regs_agree CLX regs r.
  Proof using UH H15 H14 H13 H12 H11 H10 H4 H2 H1 P thr HUI TOK.
    destruct UH as [_ _ _ _ _ Hstk Hobj G0 G1 G2]. pose proof (u64_range sp) as Hspr. pose proof (u64_range this) as Hth.
    wd_eexists. split.
    - an If7ca8 D_773c4.                                   (* [comment removed for export] *)
      fsd8 If7cac D_773c8 (at_ sp (-8)) Hstk (at_ sp (-144)) 144%nat.
      fsd8 If7cb0 D_773cc (at_ sp (-16)) Hstk (at_ sp (-144)) 144%nat.
      fsd8 If7cb4 D_773d0 (at_ sp (-24)) Hstk (at_ sp (-144)) 144%nat.
      fsd8 If7cb8 D_773d4 (at_ sp (-32)) Hstk (at_ sp (-144)) 144%nat.
      fsd8 If7cbc D_773d8 (at_ sp (-40)) Hstk (at_ sp (-144)) 144%nat.
      fsd8 If7cc0 D_773dc (at_ sp (-48)) Hstk (at_ sp (-144)) 144%nat.
      fsd8 If7cc4 D_773e0 (at_ sp (-56)) Hstk (at_ sp (-144)) 144%nat.
      fsd8 If7cc8 D_773e4 (at_ sp (-64)) Hstk (at_ sp (-144)) 144%nat.
      fsd8 If7ccc D_773e8 (at_ sp (-72)) Hstk (at_ sp (-144)) 144%nat.
      fsd8 If7cd0 D_773ec (at_ sp (-80)) Hstk (at_ sp (-144)) 144%nat.
      an If7cd4 D_773f0. an If7cd8 D_773f4. an If7cdc D_773f8. an If7ce0 D_773fc. an If7ce4 D_77400. an If7ce8 D_77404.   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sw_at with (a := at_ this 8);
          [exact If7cec | reflexivity | exact D_77408
          | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
          | gres; rwH; reflexivity
          | sokS Hobj (at_ this 8) 2056%nat ]
        | step_simpl]; vn.                                  (* [comment removed for export] *)
      change (wbytes _ _ _) with ui_m1.
      an If7cf0 D_7740c.                                    (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold ui_clobx in G in change_no_check G' end). ra_solve.
  Qed.

  Ltac cldg F D bs0 vv Hr :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := bs0) (v := vv);
        [exact F | reflexivity | exact D | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi; zlit_at; Hr | first [apply bytes_le_to_Z_8 | unorm; reflexivity] ]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  Lemma uiB : forall (M : word -> option byte) r0,
    getr r0 10 = Z_to_bv 64 1 -> regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ rb 0x77410) M rom) (mkst r (at_ rb 0x78e2c) M rom)
      /\ getr r 1 = at_ rb 0x77418
      /\ (forall i : reg, In i [2; 4; 8; 9; 18; 19; 20; 21] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using HUI TOK.
    intros M r0 R10 AG0.
    wd_eexists. split.
    - ab_ft If7cf4 D_77410 ltac:(condz).                  (* [comment removed for export] *)
      an If7cf8 D_77414.                                   (* [comment removed for export] *)
      wd_refl.
    - post. 2: ((lazymatch goal with |- ?G => let G' := eval unfold ui_clobx in G in change_no_check G' end); ra_chain).
      intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [gres; reflexivity|]); destruct Hi.
  Qed.

  (* [comment removed for export] *)
  Lemma uiC : forall (M : word -> option byte) r0,
    getr r0 10 = thr -> rdn segs M (at_ thr 3168) 1 = Some [Z_to_bv 8 0] -> store_ok segs M (at_ thr 3168) 1 = true ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ rb 0x77418) M rom) (mkst r (at_ rb 0x78ff0) (wbytes M (at_ thr 3168) [Z_to_bv 8 1]) rom)
      /\ getr r 1 = at_ rb 0x77438 /\ getr r 10 = thr /\ getr r 23 = thr /\ getr r 24 = at_ thr 2047
      /\ (forall i : reg, In i [2; 4; 8; 9; 18; 19; 20; 21] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using UH P bp this sp mem HUI TOK.
    intros M r0 R10 Ru SOK AG0. destruct UH as [_ _ _ _ _ _ _ G0 G1 G2]. pose proof (u64_range thr).
    wd_eexists. split.
    - ab_ft If7cfc D_77418 ltac:(condz).                  (* [comment removed for export] *)
      an If7d00 D_7741c.                                   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lbu with (b := Z_to_bv 8 0); [exact If7d04 | reflexivity | exact D_77420 | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; exact Ru]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      an If7d08 D_77424.                                   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sb_at with (a := at_ thr 3168) (b := Z_to_bv 8 1);
          [exact If7d0c | reflexivity | exact D_77428 | gres; rwH; imm_norm; rewrite ?at_addi; reflexivity | gres; rwH; reflexivity | reflexivity | exact SOK]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      ab_ft If7d10 D_7742c ltac:(condz).                  (* [comment removed for export] *)
      an If7d14 D_77430.                                   (* [comment removed for export] *)
      an If7d18 D_77434.                                   (* [comment removed for export] *)
      wd_refl.
    - post. 2: ((lazymatch goal with |- ?G => let G' := eval unfold ui_clobx in G in change_no_check G' end); ra_chain).
      intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [gres; reflexivity|]); destruct Hi.
  Qed.

  (* [comment removed for export] *)
  Lemma uiD : forall (M : word -> option byte) r0,
    getr r0 10 = top -> getr r0 23 = thr -> regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ rb 0x77438) M rom) (mkst r (at_ rb 0x79048) M rom)
      /\ getr r 1 = at_ rb 0x77444 /\ getr r 10 = thr /\ getr r 22 = top
      /\ (forall i : reg, In i [2; 4; 8; 9; 18; 19; 20; 21; 23; 24] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using HUI TOK.
    intros M r0 R10 R23 AG0.
    wd_eexists. split.
    - an If7d1c D_77438.                                   (* [comment removed for export] *)
      an If7d20 D_7743c.                                   (* [comment removed for export] *)
      an If7d24 D_77440.                                   (* [comment removed for export] *)
      wd_refl.
    - post. 2: ((lazymatch goal with |- ?G => let G' := eval unfold ui_clobx in G in change_no_check G' end); ra_chain).
      intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [gres; reflexivity|]); destruct Hi.
  Qed.

  (* [comment removed for export] *)
  Definition uw_mem (M : word -> option byte) (s1v s4v : word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
      (at_ sp (-88)) (LE8 (at_ rb 0x774e0))) (at_ sp (-96)) (LE8 bp)) (at_ sp (-104)) (LE8 s1v))
      (at_ sp (-112)) (LE8 pc0)) (at_ sp (-120)) (LE8 this)) (at_ sp (-128)) (LE8 s4v))
      (at_ sp (-136)) (LE8 fast)) (at_ this 2056) (LE8 bp).

  Lemma uw_mem_outside : forall M s1v s4v (x : word),
    (U x < U sp - 136)%Z \/ (U sp - 80 <= U x < U this + 2056)%Z \/ (U this + 2064 <= U x)%Z -> uw_mem M s1v s4v x = M x.
  Proof using UH P thr mem segs.
    intros M s1v s4v x Hx. destruct UH as [_ _ _ _ _ _ _ G0 G1 G2]. pose proof (u64_range sp). pose proof (u64_range this). (lazymatch goal with |- ?G => let G' := eval unfold uw_mem in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma uiE : forall (M : word -> option byte) r0,
    mem_grows mem M ->
    getr r0 10 = bot -> getr r0 22 = top -> getr r0 23 = thr -> getr r0 24 = at_ thr 2047 ->
    getr r0 2 = at_ sp (-80) -> getr r0 4 = tp -> getr r0 8 = bp -> getr r0 9 = Z_to_bv 64 30 -> getr r0 18 = pc0 -> getr r0 19 = this ->
    getr r0 20 = Z_to_bv 64 0 -> getr r0 21 = fast ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ rb 0x77444) M rom) (mkst r (at_ (at_ rb 0x8fe7c) 0) (uw_mem M (Z_to_bv 64 30) (Z_to_bv 64 0)) rom)
      /\ getr r 1 = at_ rb 0x774e0 /\ getr r 2 = at_ sp (-80) /\ getr r 10 = this /\ getr r 11 = pc0 /\ getr r 12 = bp
      /\ getr r 13 = top /\ getr r 14 = bot /\ getr r 15 = Z_to_bv 64 30
      /\ getr r 4 = tp /\ getr r 8 = bp /\ getr r 9 = Z_to_bv 64 30 /\ getr r 18 = pc0 /\ getr r 19 = this
      /\ getr r 20 = Z_to_bv 64 0 /\ getr r 21 = fast /\ getr r 22 = top /\ getr r 23 = thr /\ getr r 24 = at_ thr 2047
      /\ regs_agree CLX regs r.
  Proof using UH Hfast P HUW HUI TOK.
    intros M r0 GR R10 R22 R23 R24 R2 R4 R8 R9 R18 R19 R20 R21 AG0.
    destruct UH as [_ _ _ _ _ Hstk Hobj G0 G1 G2]. pose proof (u64_range sp) as Hspr. pose proof (u64_range this) as Hth. pose proof (u64_range bp) as Hbp.
    Ltac sokG GR Hs lo N :=
      repeat (eapply store_ok_mono; [apply wbytes_grows|]); eapply store_ok_mono; [exact GR|];
      eapply (store_ok_sub segs mem lo _ N); [rewrite at_u; lia | exact Hs | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia].
    Ltac fsdG F D aa GR Hs lo N :=
      chain_step; [reflexivity
        | eapply step_sd_at with (a := aa);
          [exact F | reflexivity | exact D
          | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
          | gres; rwH; reflexivity
          | sokG GR Hs lo N ]
        | step_simpl]; vn.
    assert (RDW : forall (k : Z) (v : word),
      In (k, v) [(-88, at_ rb 0x774e0); (-96, bp); (-104, Z_to_bv 64 30); (-112, pc0); (-120, this); (-128, Z_to_bv 64 0); (-136, fast)]%Z ->
      rdn segs (uw_mem M (Z_to_bv 64 30) (Z_to_bv 64 0)) (at_ sp k) 8 = Some (LE8 v)).
    { intros k v Hin. (lazymatch goal with |- ?G => let G' := eval unfold uw_mem in G in change_no_check G' end).
      assert (Hk : (-136 <= k <= -88)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E; intros; lia|]); destruct Hin).
      rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes, !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ].
      cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin. }
    wd_eexists. split.
    - an If7d28 D_77444.                                   (* [comment removed for export] *)
      ab_ft If7d2c D_77448 ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, bv_eqb in G in change_no_check G' end); apply Z.eqb_neq; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); exact Hfast || (unorm; exact Hfast)).   (* [comment removed for export] *)
      an If7d30 D_7744c. an If7d34 D_77450. an If7d38 D_77454. an If7d3c D_77458. an If7d40 D_7745c. an If7d44 D_77460. an If7d48 D_77464.
      an If7d4c D_77468.                                   (* [comment removed for export] *)
      an If7dc0 D_774dc.                                   (* [comment removed for export] *)
      an I114484 D_904d8.                                 (* [comment removed for export] *)
      fsdG I114488 D_904dc (at_ sp (-88)) GR Hstk (at_ sp (-144)) 144%nat.     (* [comment removed for export] *)
      fsdG I11448c D_904e0 (at_ sp (-96)) GR Hstk (at_ sp (-144)) 144%nat.     (* [comment removed for export] *)
      fsdG I114490 D_904e4 (at_ sp (-104)) GR Hstk (at_ sp (-144)) 144%nat.    (* [comment removed for export] *)
      fsdG I114494 D_904e8 (at_ sp (-112)) GR Hstk (at_ sp (-144)) 144%nat.    (* [comment removed for export] *)
      fsdG I114498 D_904ec (at_ sp (-120)) GR Hstk (at_ sp (-144)) 144%nat.    (* [comment removed for export] *)
      fsdG I11449c D_904f0 (at_ sp (-128)) GR Hstk (at_ sp (-144)) 144%nat.    (* [comment removed for export] *)
      fsdG I1144a0 D_904f4 (at_ sp (-136)) GR Hstk (at_ sp (-144)) 144%nat.    (* [comment removed for export] *)
      an I1144a4 D_904f8.                                 (* [comment removed for export] *)
      an I1144a8 D_904fc.                                 (* [comment removed for export] *)
      an I1144ac D_90500.                                 (* [comment removed for export] *)
      an I1144b0 D_90504.                                 (* [comment removed for export] *)
      an I1144b4 D_90508.                                 (* [comment removed for export] *)
      match goal with |- context [v_and ?m bp] => replace (v_and m bp) with bp by (symmetry; etransitivity; [|apply v_and_m1_l]; f_equal; apply bv_eq; reflexivity) end.
      an I1144b8 D_9050c.                                 (* [comment removed for export] *)
      fsdG I1144bc D_90510 (at_ this 2056) GR Hobj (at_ this 8) 2056%nat.      (* [comment removed for export] *)
      change (wbytes _ _ _) with (uw_mem M (Z_to_bv 64 30) (Z_to_bv 64 0)).
      ab_ft I1144c0 D_90514 ltac:(condz).                (* [comment removed for export] *)
      ab_tk I1144c4 D_90518 ltac:(condz).                (* [comment removed for export] *)
      ab_tk I1144fc D_90550 ltac:(condz).                (* [comment removed for export] *)
      an I114564 D_905b8. an I114568 D_905bc. an I11456c D_905c0. an I114570 D_905c4. an I114574 D_905c8.   (* [comment removed for export] *)
      cldg I114578 D_905cc (LE8 (at_ rb 0x774e0)) (at_ rb 0x774e0) ltac:(apply RDW; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).    (* [comment removed for export] *)
      cldg I11457c D_905d0 (LE8 bp) bp ltac:(apply RDW; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).                                (* [comment removed for export] *)
      cldg I114580 D_905d4 (LE8 (Z_to_bv 64 30)) (Z_to_bv 64 30) ltac:(apply RDW; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).    (* [comment removed for export] *)
      cldg I114584 D_905d8 (LE8 pc0) pc0 ltac:(apply RDW; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).                              (* [comment removed for export] *)
      cldg I114588 D_905dc (LE8 this) this ltac:(apply RDW; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).                            (* [comment removed for export] *)
      cldg I11458c D_905e0 (LE8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(apply RDW; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).      (* [comment removed for export] *)
      cldg I114590 D_905e4 (LE8 fast) fast ltac:(apply RDW; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).                            (* [comment removed for export] *)
      an I114594 D_905e8.                                 (* [comment removed for export] *)
      an I114598 D_905ec.                                 (* [comment removed for export] *)
      rewrite ?at_at. wd_refl.
    - rewrite ?at_at. post. (lazymatch goal with |- ?G => let G' := eval unfold ui_clobx in G in change_no_check G' end). ra_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma uiF : forall (M : word -> option byte) r0,
    getr r0 2 = at_ sp (-80) -> getr r0 24 = at_ thr 2047 -> store_ok segs M (at_ thr 3168) 1 = true ->
    (forall (k : Z) (v : word),
       In (k, v) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19);
                  (-48, getr regs 20); (-56, getr regs 21); (-64, getr regs 22); (-72, getr regs 23); (-80, getr regs 24)]%Z ->
       rdn segs M (at_ sp k) 8 = Some (LE8 v)) ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ rb 0x774e0) M rom) (mkst r ra (wbytes M (at_ thr 3168) [Z_to_bv 8 0]) rom)
      /\ regs_agree CL regs r.
  Proof using UH H15 H14 H13 H12 H11 H10 H2 H1 Hret P fast bp pc0 this mem HUI TOK.
    intros M r0 R2 R24 SOK RD AG0. destruct UH as [_ _ _ _ _ _ _ G0 G1 G2]. pose proof (u64_range sp) as Hspr. pose proof (u64_range thr).
    assert (RD' : forall (k : Z) (v : word),
       In (k, v) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19);
                  (-48, getr regs 20); (-56, getr regs 21); (-64, getr regs 22); (-72, getr regs 23); (-80, getr regs 24)]%Z ->
       rdn segs (wbytes M (at_ thr 3168) [Z_to_bv 8 0]) (at_ sp k) 8 = Some (LE8 v)).
    { intros k v Hin. assert (Hk : (-80 <= k <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E; intros; lia|]); destruct Hin).
      rewrite rdn_wbytes_out; [exact (RD k v Hin) | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]]. }
    wd_eexists. split.
    - chain_step; [reflexivity
        | eapply step_sb_at with (a := at_ thr 3168) (b := Z_to_bv 8 0);
          [exact If7dc4 | reflexivity | exact D_774e0 | gres; rwH; imm_norm; rewrite ?at_addi; reflexivity | gres; rwH; reflexivity | reflexivity | exact SOK]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      cldg If7dc8 D_774e4 (LE8 ra) ra ltac:(apply RD'; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      cldg If7dcc D_774e8 (LE8 (getr regs 8)) (getr regs 8) ltac:(apply RD'; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      cldg If7dd0 D_774ec (LE8 (getr regs 9)) (getr regs 9) ltac:(apply RD'; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      cldg If7dd4 D_774f0 (LE8 (getr regs 18)) (getr regs 18) ltac:(apply RD'; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      cldg If7dd8 D_774f4 (LE8 (getr regs 19)) (getr regs 19) ltac:(apply RD'; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      cldg If7ddc D_774f8 (LE8 (getr regs 20)) (getr regs 20) ltac:(apply RD'; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      cldg If7de0 D_774fc (LE8 (getr regs 21)) (getr regs 21) ltac:(apply RD'; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      cldg If7de4 D_77500 (LE8 (getr regs 22)) (getr regs 22) ltac:(apply RD'; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      cldg If7de8 D_77504 (LE8 (getr regs 23)) (getr regs 23) ltac:(apply RD'; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      cldg If7dec D_77508 (LE8 (getr regs 24)) (getr regs 24) ltac:(apply RD'; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      an If7df0 D_7750c.                                   (* [comment removed for export] *)
      aret If7df4 D_77510 ra.                              (* [comment removed for export] *)
      wd_refl.
    - apply (regs_agree_strengthen ui_clob ui_clobx regs).
      + (lazymatch goal with |- ?G => let G' := eval unfold ui_clobx in G in change_no_check G' end). ra_solve.
      + intros i Hi Hni. cbn [ui_clobx In] in Hi.
        repeat (destruct Hi as [<-|Hi]; [gres; rwH; rewrite ?at_addi, ?at_0; first [reflexivity | symmetry; assumption | f_equal; lia | exfalso; apply Hni; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto] |]).
        destruct Hi.
  Qed.

  (* [comment removed for export] *)
  Ltac via AG r H :=
    let T := fresh in pose proof (AG r ltac:(notin_list)) as T; rewrite H in T; exact T.

  (* [comment removed for export] *)
  Theorem ui_run_s : forall (D : nat) (bsr0 bsw0 : list byte),
    rdn segs mem (at_ bp (-8)) 8 = Some bsr0 -> length bsr0 = 8%nat ->
    rdn segs mem (at_ bp (-16)) 8 = Some bsw0 -> length bsw0 = 8%nat ->
    fpc mem (bytes_le_to_Z bsw0) (U bp) D ->
    exists r' M' (s : Z),
      msteps segs (mkst regs (at_ rb 0x773c4) mem rom) (mkst r' ra M' rom)
      /\ regs_agree CL regs r'
      /\ (1 <= s <= 30)%Z /\ (s <= 2 + Z.of_nat D)%Z
      /\ rdn segs M' (at_ this 8) 4 = Some (LE4 s)
      /\ rdn segs M' (at_ this 16) 8 = Some (LE8 pc0)
      /\ rdn segs M' (at_ thr 3168) 1 = Some [Z_to_bv 8 0]
      /\ (forall x : word, M' x <> mem x ->
            (U sp - 144 <= U x < U sp)%Z \/ (U this + 8 <= U x < U this + 12)%Z \/ (U this + 16 <= U x < U this + 256)%Z
            \/ (U this + 2056 <= U x < U this + 2064)%Z \/ U x = (U thr + 3168)%Z)
      /\ mem_grows mem M'.
  Proof using Gtop SH GH UH Hfast H15 H14 H13 H12 H11 H10 H4 H2 H1 Hret P tctx tsdp bot top fast tp HUW HUI TOK.
    intros D bsr0 bsw0 Rr Lr Rw Lw FPC.
    pose proof TOK as TOK'. destruct TOK' as [_ _ UFC UF56 GTOK GRB STT STB AIN AINB RB].
    pose proof UH as UH'. destruct UH' as [Rin Ru SOKu Rg RP Hstk Hobj G0 G1 G2].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range this) as Hth. pose proof (u64_range bp) as Hbp. pose proof (u64_range thr) as Hthr.
    pose proof (u64_range rb) as Hrb. pose proof (u64_range P) as HP.
    assert (RET : forall d, (d mod 2 = 0)%Z -> (0 <= d < 2 ^ 24)%Z -> ret_ok (at_ rb d)).
    { intros d Hd Hdr. apply ret_ok_at; [exact (proj1 RB) | exact Hd | lia]. }
    (* [comment removed for export] *)
    destruct uiA as (r1 & RUN1 & A1 & A2 & A4 & A9 & A21 & A20 & A8 & A18 & A19 & AG1).
    assert (GR1 : mem_grows mem ui_m1) by ((lazymatch goal with |- ?G => let G' := eval unfold ui_m1 in G in change_no_check G' end); repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    (* [comment removed for export] *)
    destruct (ain_run segs rb (ut_g_inited t) AIN AINB ui_m1 rom r1 (at_ rb 0x77410)) as (r2 & RUN2 & B10 & AG2).
    { rewrite <- Rin. apply rdn_ext; [wd_ulia_c|]. intros x Hx. apply ui_m1_outside. revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx. lia. }
    { apply RET; [reflexivity | lia]. }
    { exact A1. }
    (* [comment removed for export] *)
    destruct (uiB ui_m1 r2 B10 ltac:(eapply regs_agree_trans; [exact AG1 | regs_agree_weaken AG2])) as (r3 & RUN3 & C1 & CK & AG3).
    (* [comment removed for export] *)
    assert (GH1 : gctH segs (ut_gct t) ui_m1 (at_ sp (-80)) tp tsdp tctx thr).
    { apply (gctH_keep segs (ut_gct t) mem ui_m1); [exact GH | | exact GR1]. intros x Hx. rewrite at_u in Hx by lia. apply ui_m1_outside. lia. }
    destruct (gct_run segs (ut_gct t) GTOK ui_m1 rom r3 (at_ rb 0x77418) (at_ sp (-80)) tp tsdp tctx thr GH1) as (r4 & RUN4 & D10 & D11 & AG4).
    { apply RET; [reflexivity | lia]. }
    { exact C1. }
    { rewrite (CK 2) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto). via AG2 (2 : reg) A2. }
    { rewrite (CK 4) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto). via AG2 (4 : reg) A4. }
    rewrite GRB in RUN4. rewrite at_at in RUN4. cbn [Z.add] in RUN4.
    set (M2 := wbytes ui_m1 (at_ sp (-88)) (LE8 (at_ rb 0x77418))) in RUN4.
    assert (HM2 : forall x : word, (U x < U sp - 88)%Z \/ (U sp <= U x < U this + 8)%Z \/ (U this + 12 <= U x)%Z -> M2 x = mem x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M2 in G in change_no_check G' end). rewrite wbytes_outside; [apply ui_m1_outside; lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    assert (GR2 : mem_grows mem M2) by ((lazymatch goal with |- ?G => let G' := eval unfold M2 in G in change_no_check G' end); eapply mem_grows_trans; [exact GR1 | apply wbytes_grows]).
    (* [comment removed for export] *)
    destruct (uiC M2 r4 D10) as (r5 & RUN5 & E1 & E10 & E23 & E24 & EK & AG5).
    { rewrite <- Ru. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. apply HM2. cbn in Hx. lia. }
    { eapply store_ok_mono; [exact GR2 | exact SOKu]. }
    { eapply regs_agree_trans; [exact AG3 | regs_agree_weaken AG4]. }
    set (M3 := wbytes M2 (at_ thr 3168) [Z_to_bv 8 1]) in RUN5.
    assert (HM3 : forall x : word, U x <> (U thr + 3168)%Z ->
              (U x < U sp - 88)%Z \/ (U sp <= U x < U this + 8)%Z \/ (U this + 12 <= U x)%Z -> M3 x = mem x).
    { intros x Hx1 Hx2. (lazymatch goal with |- ?G => let G' := eval unfold M3 in G in change_no_check G' end). rewrite wbytes_outside; [apply HM2; exact Hx2 | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]]. }
    assert (GR3 : mem_grows mem M3) by ((lazymatch goal with |- ?G => let G' := eval unfold M3 in G in change_no_check G' end); eapply mem_grows_trans; [exact GR2 | apply wbytes_grows]).
    assert (SH3 : stkH segs M3 thr top bot).
    { apply (stkH_keep segs mem M3 _ _ _ SH). intros x Hx. apply HM3; lia. }
    (* [comment removed for export] *)
    destruct (stt_run segs rb STT M3 rom r5 (at_ rb 0x77438) thr top bot SH3 ltac:(apply RET; [reflexivity | lia]) E1 E10) as (r6 & RUN6 & F10 & F11 & AG6).
    (* [comment removed for export] *)
    destruct (uiD M3 r6 F10 ltac:(via AG6 (23 : reg) E23) ltac:(eapply regs_agree_trans; [exact AG5 | regs_agree_weaken AG6])) as (r7 & RUN7 & G1' & G10 & G22 & GK & AG7).
    (* [comment removed for export] *)
    destruct (stb_run segs rb STB M3 rom r7 (at_ rb 0x77444) thr top bot SH3 ltac:(apply RET; [reflexivity | lia]) G1' G10) as (r8 & RUN8 & I10 & I11 & AG8).
    (* [comment removed for export] *)
    assert (K2 : getr r8 2 = at_ sp (-80)).
    { rewrite (AG8 2) by notin_list. rewrite (GK 2) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto). rewrite (AG6 2) by notin_list. rewrite (EK 2) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto).
      rewrite (AG4 2) by notin_list. rewrite (CK 2) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto). via AG2 (2 : reg) A2. }
    Ltac thread8 AG8 GK AG6 EK AG4 CK AG2 r A :=
      rewrite (AG8 r) by notin_list; rewrite (GK r) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); rewrite (AG6 r) by notin_list; rewrite (EK r) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto);
      rewrite (AG4 r) by notin_list; rewrite (CK r) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); via AG2 r A.
    assert (K4 : getr r8 4 = tp) by (thread8 AG8 GK AG6 EK AG4 CK AG2 (4 : reg) A4).
    assert (K8 : getr r8 8 = bp) by (thread8 AG8 GK AG6 EK AG4 CK AG2 (8 : reg) A8).
    assert (K9 : getr r8 9 = Z_to_bv 64 30) by (thread8 AG8 GK AG6 EK AG4 CK AG2 (9 : reg) A9).
    assert (K18 : getr r8 18 = pc0) by (thread8 AG8 GK AG6 EK AG4 CK AG2 (18 : reg) A18).
    assert (K19 : getr r8 19 = this) by (thread8 AG8 GK AG6 EK AG4 CK AG2 (19 : reg) A19).
    assert (K20 : getr r8 20 = Z_to_bv 64 0) by (thread8 AG8 GK AG6 EK AG4 CK AG2 (20 : reg) A20).
    assert (K21 : getr r8 21 = fast) by (thread8 AG8 GK AG6 EK AG4 CK AG2 (21 : reg) A21).
    assert (K22 : getr r8 22 = top) by (rewrite (AG8 22) by notin_list; exact G22).
    assert (K23 : getr r8 23 = thr) by (rewrite (AG8 23) by notin_list; rewrite (GK 23) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); via AG6 (23 : reg) E23).
    assert (K24 : getr r8 24 = at_ thr 2047) by (rewrite (AG8 24) by notin_list; rewrite (GK 24) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); via AG6 (24 : reg) E24).
    destruct (uiE M3 r8 GR3 I10 K22 K23 K24 K2 K4 K8 K9 K18 K19 K20 K21 ltac:(eapply regs_agree_trans; [exact AG7 | regs_agree_weaken AG8]))
      as (r9 & RUN9 & J1 & J2 & J10 & J11 & J12 & J13 & J14 & J15 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J23 & J24 & AG9).
    set (M4 := uw_mem M3 (Z_to_bv 64 30) (Z_to_bv 64 0)) in RUN9.
    assert (HM4 : forall x : word, U x <> (U thr + 3168)%Z ->
              (U x < U sp - 144)%Z \/ (U sp <= U x < U this + 8)%Z \/ (U this + 12 <= U x < U this + 2056)%Z \/ (U this + 2064 <= U x)%Z -> M4 x = mem x).
    { intros x Hx1 Hx2. (lazymatch goal with |- ?G => let G' := eval unfold M4 in G in change_no_check G' end). rewrite uw_mem_outside by lia. apply HM3; lia. }
    assert (GR4 : mem_grows mem M4).
    { (lazymatch goal with |- ?G => let G' := eval unfold M4, uw_mem in G in change_no_check G' end). eapply mem_grows_trans; [exact GR3|]. do 8 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. }
    (* [comment removed for export] *)
    destruct (uf_run segs (at_ rb 0x8fe7c) (ut_g_pgsz t) UFC UF56 r9 rom (at_ rb 0x774e0) (at_ sp (-80)) this pc0 bp top bot
                ltac:(apply RET; [reflexivity | lia]) J1 J2 J10 J11 J12 J13 J14 J15
                ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(lia) ltac:(lia) ltac:(lia) Gtop (sh_lt _ _ _ _ _ SH)
                M4 P) with (D := D) (bsr0 := bsr0) (bsw0 := bsw0)
      as (r10 & M5 & s & RUN10 & L10 & L11 & AG10 & S1 & S2 & SZ & PC & FR5 & GR5).
    { rewrite <- Rg. apply rdn_ext; [wd_ulia_c|]. intros x Hx. apply HM4; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia. }
    { rewrite <- RP. apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. apply HM4; cbn in Hx; lia. }
    { lia. }
    { lia. }
    { eapply store_ok_mono; [exact GR4|]. rewrite at_at. (lazymatch goal with |- ?G => let G' := eval cbn [Z.add] in G in change_no_check G' end).
      eapply (store_ok_sub segs mem (at_ sp (-144)) _ 144); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { eapply store_ok_mono; [exact GR4|].
      eapply (store_ok_sub segs mem (at_ this 8) _ 2056); [rewrite at_u; lia | exact Hobj | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { rewrite <- Rr. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. apply HM4; cbn in Hx; lia. }
    { exact Lr. }
    { rewrite <- Rw. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. apply HM4; cbn in Hx; lia. }
    { exact Lw. }
    { pose proof (bytes_le_to_Z_bound bsw0) as Bw. rewrite Lw in Bw. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bw.
      apply (fpc_kept_gen mem _ _ _ FPC M4).
      destruct (fpc_shape _ _ _ _ FPC) as [ST | FRM]; [left; exact ST | right].
      intros a Ha. pose proof (u64_range (Z_to_bv 64 a)).
      apply HM4; rewrite u_Z2bv by (unfold PTRHI in Ha; lia); lia. }
    (* [comment removed for export] *)
    assert (HM5 : forall x : word, (U sp - 80 <= U x < U sp)%Z -> M5 x = ui_m1 x).
    { intros x Hx. destruct (decide (M5 x = M4 x)) as [E5|NE5].
      2:{ exfalso. destruct (FR5 x NE5) as [F|F]; rewrite ?at_u in F by lia; lia. }
      rewrite E5. (lazymatch goal with |- ?G => let G' := eval unfold M4 in G in change_no_check G' end). rewrite uw_mem_outside by lia. (lazymatch goal with |- ?G => let G' := eval unfold M3 in G in change_no_check G' end). rewrite wbytes_outside by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
      (lazymatch goal with |- ?G => let G' := eval unfold M2 in G in change_no_check G' end). rewrite wbytes_outside by (rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia). reflexivity. }
    destruct (uiF M5 r10) as (r11 & RUN11 & AG11).
    { rewrite (AG10 2) by notin_list. exact J2. }
    { rewrite (AG10 24) by notin_list. exact J24. }
    { eapply store_ok_mono; [| exact SOKu]. eapply mem_grows_trans; [exact GR4 | exact GR5]. }
    { intros k v Hin. assert (Hk : (-80 <= k <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E; intros; lia|]); destruct Hin).
      rewrite <- (ui_m1_slots k v Hin). apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. apply HM5. cbn in Hx. lia. }
    { eapply regs_agree_trans; [exact AG9 | regs_agree_weaken AG10]. }
    (* [comment removed for export] *)
    exists r11, (wbytes M5 (at_ thr 3168) [Z_to_bv 8 0]), s.
    split.
    { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
      eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|].
      eapply msteps_trans; [exact RUN7|]. eapply msteps_trans; [exact RUN8|]. eapply msteps_trans; [exact RUN9|].
      eapply msteps_trans; [exact RUN10|]. exact RUN11. }
    split; [exact AG11|]. split; [exact S1|]. split; [exact S2|].
    split. { rewrite rdn_wbytes_out; [exact SZ | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]]. }
    split. { rewrite rdn_wbytes_out; [exact PC | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]]. }
    split. { pose proof (rdn_wbytes_hit segs [Z_to_bv 8 0] M5 (at_ thr 3168)) as X. cbn [length] in X. apply X. rewrite at_u by lia. lia. }
    split.
    { intros x Hx. pose proof (u64_range x).
      destruct (Z.eq_dec (U x) (U thr + 3168)) as [E|NE]; [right; right; right; right; exact E|].
      rewrite wbytes_outside in Hx by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
      destruct (decide (M5 x = M4 x)) as [E5|NE5].
      2:{ destruct (FR5 x NE5) as [F|[F|F]]; rewrite ?at_u in F by lia; [left; lia | right; left; lia | right; right; left; lia]. }
      rewrite E5 in Hx.
      destruct (Z.lt_ge_cases (U x) (U sp - 144)); [exfalso; apply Hx; apply HM4; lia|].
      destruct (Z.lt_ge_cases (U x) (U sp)); [left; lia|].
      destruct (Z.lt_ge_cases (U x) (U this + 8)); [exfalso; apply Hx; apply HM4; lia|].
      destruct (Z.lt_ge_cases (U x) (U this + 12)); [right; left; lia|].
      destruct (Z.lt_ge_cases (U x) (U this + 2056)); [exfalso; apply Hx; apply HM4; lia|].
      destruct (Z.lt_ge_cases (U x) (U this + 2064)); [right; right; right; left; lia|].
      exfalso; apply Hx; apply HM4; lia. }
    eapply mem_grows_trans; [exact GR4|]. eapply mem_grows_trans; [exact GR5 | apply wbytes_grows].
  Qed.

  (* [comment removed for export] *)
  Theorem ui_run : forall (D : nat) (bsr0 bsw0 : list byte),
    rdn segs mem (at_ bp (-8)) 8 = Some bsr0 -> length bsr0 = 8%nat ->
    rdn segs mem (at_ bp (-16)) 8 = Some bsw0 -> length bsw0 = 8%nat ->
    fpc mem (bytes_le_to_Z bsw0) (U bp) D ->
    exists r' M' (s : Z),
      msteps segs (mkst regs (at_ rb 0x773c4) mem rom) (mkst r' ra M' rom)
      /\ regs_agree CL regs r'
      /\ (1 <= s <= 30)%Z /\ (s <= 2 + Z.of_nat D)%Z
      /\ rdn segs M' (at_ this 8) 4 = Some (LE4 s)
      /\ rdn segs M' (at_ this 16) 8 = Some (LE8 pc0)
      /\ rdn segs M' (at_ thr 3168) 1 = Some [Z_to_bv 8 0]
      /\ (forall x : word, M' x <> mem x ->
            (U sp - 144 <= U x < U sp)%Z \/ (U this + 8 <= U x < U this + 256)%Z \/ (U this + 2056 <= U x < U this + 2064)%Z \/ U x = (U thr + 3168)%Z)
      /\ mem_grows mem M'.
  Proof using Gtop SH GH UH Hfast H15 H14 H13 H12 H11 H10 H4 H2 H1 Hret P tctx tsdp bot top fast tp HUW HUI TOK.
    intros D bsr0 bsw0 Rr Lr Rw Lw FPC.
    destruct (ui_run_s D bsr0 bsw0 Rr Lr Rw Lw FPC) as (r' & M' & s & RUN & AG & S1 & S2 & SZ & PC & UN & FR & GR).
    exists r', M', s. repeat (split; [assumption|]). split; [|exact GR].
    intros x Hx. destruct (FR x Hx) as [F|[F|[F|[F|F]]]]; [left | right; left | right; left | right; right; left | right; right; right]; try lia; try exact F.
  Qed.
End UI.
End FPGen1d.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.

Section FPGen2.
Context {fx : FPState}.
#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Definition both_gct_tab : gct_tab := GCT (Z_to_bv 64 0) (Z_to_bv 64 0x10da20) (Z_to_bv 64 0xfdd18).
Definition both_ui_tab : ui_tab := UIT (Z_to_bv 64 0) both_gct_tab 0x10ee98 0x105ef8 0x10000 0x663000.

Lemma both_gct_tab_ok : gct_tab_ok BSEGS both_gct_tab.
Proof using.
  split; (lazymatch goal with |- ?G => let G' := eval cbn [gt_rb gt_tsd gt_pgs both_gct_tab] in G in change_no_check G' end).
  - (lazymatch goal with |- ?G => let G' := eval unfold gct_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold tsd_words in G in change_no_check G' end). code_ato_vm.
  - gaddr2_tac F_714ac D_714ac F_714b0 D_714b0.
  - gjump_tac F_714c0 D_714c0.
  - (lazymatch goal with |- ?G => let G' := eval unfold pgs_words in G in change_no_check G' end). code_ato_vm.
  - split; vm_compute; [reflexivity | exact eq_refl].
Qed.

Lemma both_ui_tab_ok : ui_tab_ok BSEGS both_ui_tab.
Proof using.
  split; (lazymatch goal with |- ?G => let G' := eval cbn [ut_rb ut_gct ut_g_inited ut_g_pgsz ut_img_lo ut_img_hi both_ui_tab] in G in change_no_check G' end).
  - (lazymatch goal with |- ?G => let G' := eval unfold ui_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold uw_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold uf_words in G in change_no_check G' end). code_ato_vm.
  - gload_tac F_8feb4 D_8feb4 F_8feb8 D_8feb8.
  - exact both_gct_tab_ok.
  - reflexivity.
  - (lazymatch goal with |- ?G => let G' := eval unfold stt_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold stb_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold ain_words in G in change_no_check G' end). code_ato_vm.
  - gload_tac F_7571c D_7571c F_75720 D_75720.
  - split; vm_compute; [reflexivity | exact eq_refl].
Qed.

(* [comment removed for export] *)
Definition both_ui_run := ui_run BSEGS both_ui_tab both_ui_tab_ok.
Definition both_ui_run_s := ui_run_s BSEGS both_ui_tab both_ui_tab_ok.
End FPGen2.
