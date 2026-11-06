(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.InstrEnc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Bo_code_7c9f4_7cb58.
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
Definition W_7c9f4 : bv 32 := @BV 32 0xfd010113%Z I.
Lemma F_7c9f4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7c9f4%Z I : word) = Some W_7c9f4.
Proof. vm_refl. Qed.
Lemma D_7c9f4 : decode_any W_7c9f4 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4048%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c9f8 : bv 32 := @BV 32 0x02113423%Z I.
Lemma F_7c9f8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7c9f8%Z I : word) = Some W_7c9f8.
Proof. vm_refl. Qed.
Lemma D_7c9f8 : decode_any W_7c9f8 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c9fc : bv 32 := @BV 32 0x02813023%Z I.
Lemma F_7c9fc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7c9fc%Z I : word) = Some W_7c9fc.
Proof. vm_refl. Qed.
Lemma D_7c9fc : decode_any W_7c9fc = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ca00 : bv 32 := @BV 32 0x00913c23%Z I.
Lemma F_7ca00 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7ca00%Z I : word) = Some W_7ca00.
Proof. vm_refl. Qed.
Lemma D_7ca00 : decode_any W_7ca00 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ca04 : bv 32 := @BV 32 0x01213823%Z I.
Lemma F_7ca04 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7ca04%Z I : word) = Some W_7ca04.
Proof. vm_refl. Qed.
Lemma D_7ca04 : decode_any W_7ca04 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ca08 : bv 32 := @BV 32 0x01313423%Z I.
Lemma F_7ca08 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7ca08%Z I : word) = Some W_7ca08.
Proof. vm_refl. Qed.
Lemma D_7ca08 : decode_any W_7ca08 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 19%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ca0c : bv 32 := @BV 32 0x00089797%Z I.
Lemma F_7ca0c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7ca0c%Z I : word) = Some W_7ca0c.
Proof. vm_refl. Qed.
Lemma D_7ca0c : decode_any W_7ca0c = Some (Auipc (@BV 5 15%Z I) (@BV 20 137%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ca10 : bv 32 := @BV 32 0x54c7b783%Z I.
Lemma F_7ca10 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7ca10%Z I : word) = Some W_7ca10.
Proof. vm_refl. Qed.
Lemma D_7ca10 : decode_any W_7ca10 = Some (Load SZ8 true (@BV 5 15%Z I) (@BV 5 15%Z I) (@BV 12 1356%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ca14 : bv 32 := @BV 32 0x00078a63%Z I.
Lemma F_7ca14 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7ca14%Z I : word) = Some W_7ca14.
Proof. vm_refl. Qed.
Lemma D_7ca14 : decode_any W_7ca14 = Some (Branch BC_EQ (@BV 5 15%Z I) (@BV 5 0%Z I) (@BV 13 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ca18 : bv 32 := @BV 32 0x00123517%Z I.
Lemma F_7ca18 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7ca18%Z I : word) = Some W_7ca18.
Proof. vm_refl. Qed.
Lemma D_7ca18 : decode_any W_7ca18 = Some (Auipc (@BV 5 10%Z I) (@BV 20 291%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ca1c : bv 32 := @BV 32 0x2c452503%Z I.
Lemma F_7ca1c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7ca1c%Z I : word) = Some W_7ca1c.
Proof. vm_refl. Qed.
Lemma D_7ca1c : decode_any W_7ca1c = Some (Load SZ4 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 708%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ca20 : bv 32 := @BV 32 0x04051a63%Z I.
Lemma F_7ca20 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7ca20%Z I : word) = Some W_7ca20.
Proof. vm_refl. Qed.
Lemma D_7ca20 : decode_any W_7ca20 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 84%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ca24 : bv 32 := @BV 32 0x0000006f%Z I.
Lemma F_7ca24 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7ca24%Z I : word) = Some W_7ca24.
Proof. vm_refl. Qed.
Lemma D_7ca24 : decode_any W_7ca24 = Some (Jal (@BV 5 0%Z I) (@BV 21 0%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_7c9f4_7cb58.
Module Bo_code_8ae68_8b254.
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
Definition W_8b0f8 : bv 32 := @BV 32 0xfe010113%Z I.
Lemma F_8b0f8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8b0f8%Z I : word) = Some W_8b0f8.
Proof. vm_refl. Qed.
Lemma D_8b0f8 : decode_any W_8b0f8 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4064%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b0fc : bv 32 := @BV 32 0x00113c23%Z I.
Lemma F_8b0fc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8b0fc%Z I : word) = Some W_8b0fc.
Proof. vm_refl. Qed.
Lemma D_8b0fc : decode_any W_8b0fc = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b100 : bv 32 := @BV 32 0x00813823%Z I.
Lemma F_8b100 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8b100%Z I : word) = Some W_8b100.
Proof. vm_refl. Qed.
Lemma D_8b100 : decode_any W_8b100 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b104 : bv 32 := @BV 32 0x00913423%Z I.
Lemma F_8b104 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8b104%Z I : word) = Some W_8b104.
Proof. vm_refl. Qed.
Lemma D_8b104 : decode_any W_8b104 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b108 : bv 32 := @BV 32 0x01213023%Z I.
Lemma F_8b108 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8b108%Z I : word) = Some W_8b108.
Proof. vm_refl. Qed.
Lemma D_8b108 : decode_any W_8b108 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b10c : bv 32 := @BV 32 0x00060413%Z I.
Lemma F_8b10c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8b10c%Z I : word) = Some W_8b10c.
Proof. vm_refl. Qed.
Lemma D_8b10c : decode_any W_8b10c = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b110 : bv 32 := @BV 32 0x00058493%Z I.
Lemma F_8b110 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8b110%Z I : word) = Some W_8b110.
Proof. vm_refl. Qed.
Lemma D_8b110 : decode_any W_8b110 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b114 : bv 32 := @BV 32 0x00058513%Z I.
Lemma F_8b114 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8b114%Z I : word) = Some W_8b114.
Proof. vm_refl. Qed.
Lemma D_8b114 : decode_any W_8b114 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b118 : bv 32 := @BV 32 0x00060593%Z I.
Lemma F_8b118 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8b118%Z I : word) = Some W_8b118.
Proof. vm_refl. Qed.
Lemma D_8b118 : decode_any W_8b118 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b11c : bv 32 := @BV 32 0x00068613%Z I.
Lemma F_8b11c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8b11c%Z I : word) = Some W_8b11c.
Proof. vm_refl. Qed.
Lemma D_8b11c : decode_any W_8b11c = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b120 : bv 32 := @BV 32 0xf19f70ef%Z I.
Lemma F_8b120 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8b120%Z I : word) = Some W_8b120.
Proof. vm_refl. Qed.
Lemma D_8b120 : decode_any W_8b120 = Some (Jal (@BV 5 1%Z I) (@BV 21 2064152%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b124 : bv 32 := @BV 32 0x00050e63%Z I.
Lemma F_8b124 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8b124%Z I : word) = Some W_8b124.
Proof. vm_refl. Qed.
Lemma D_8b124 : decode_any W_8b124 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 28%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b128 : bv 32 := @BV 32 0x01813083%Z I.
Lemma F_8b128 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8b128%Z I : word) = Some W_8b128.
Proof. vm_refl. Qed.
Lemma D_8b128 : decode_any W_8b128 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b12c : bv 32 := @BV 32 0x01013403%Z I.
Lemma F_8b12c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8b12c%Z I : word) = Some W_8b12c.
Proof. vm_refl. Qed.
Lemma D_8b12c : decode_any W_8b12c = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b130 : bv 32 := @BV 32 0x00813483%Z I.
Lemma F_8b130 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8b130%Z I : word) = Some W_8b130.
Proof. vm_refl. Qed.
Lemma D_8b130 : decode_any W_8b130 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b134 : bv 32 := @BV 32 0x00013903%Z I.
Lemma F_8b134 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8b134%Z I : word) = Some W_8b134.
Proof. vm_refl. Qed.
Lemma D_8b134 : decode_any W_8b134 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b138 : bv 32 := @BV 32 0x02010113%Z I.
Lemma F_8b138 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8b138%Z I : word) = Some W_8b138.
Proof. vm_refl. Qed.
Lemma D_8b138 : decode_any W_8b138 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b13c : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_8b13c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8b13c%Z I : word) = Some W_8b13c.
Proof. vm_refl. Qed.
Lemma D_8b13c : decode_any W_8b13c = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b244 : bv 32 := @BV 32 0x00058513%Z I.
Lemma F_8b244 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8b244%Z I : word) = Some W_8b244.
Proof. vm_refl. Qed.
Lemma D_8b244 : decode_any W_8b244 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b248 : bv 32 := @BV 32 0x00060593%Z I.
Lemma F_8b248 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8b248%Z I : word) = Some W_8b248.
Proof. vm_refl. Qed.
Lemma D_8b248 : decode_any W_8b248 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b24c : bv 32 := @BV 32 0x00068613%Z I.
Lemma F_8b24c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8b24c%Z I : word) = Some W_8b24c.
Proof. vm_refl. Qed.
Lemma D_8b24c : decode_any W_8b24c = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b250 : bv 32 := @BV 32 0xc65f706f%Z I.
Lemma F_8b250 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8b250%Z I : word) = Some W_8b250.
Proof. vm_refl. Qed.
Lemma D_8b250 : decode_any W_8b250 = Some (Jal (@BV 5 0%Z I) (@BV 21 2063460%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_8ae68_8b254.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_82b14_83760 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvIStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac Bo_code_8ae68_8b254 OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_82b14_83760 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvIStrlen.Bo_code_80b0c_815a0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0.Bo_code_7d08c_7db0c.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Lemma rdn_wbytes_hit4 : forall segs (m : word -> option byte) (a : word) z,
  (bv_unsigned a + 4 <= 2 ^ 64)%Z -> rdn segs (wbytes m a (LE4 z)) a 4 = Some (LE4 z).
Proof.
  intros segs m a z Ha. pose proof (rdn_wbytes_hit segs (LE4 z) m a) as H.
  rewrite length_N_to_le_bytes in H. apply H. exact Ha.
Qed.

(* [comment removed for export] *)
Ltac sltu0 :=
  match goal with |- context [v_sltu ?a ?b] =>
    replace (v_sltu a b) with (Z_to_bv 64 0)
      by (symmetry; rwH; (lazymatch goal with |- ?G => let G' := eval unfold v_sltu in G in change_no_check G' end); rewrite c_ltu_ltb; unorm; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity) end.

Ltac av_and F D vv tac :=
  chain_step;
  [ reflexivity
  | eapply step_and_at with (v := vv); [ exact F | reflexivity | exact D | reflexivity | gres; rwH; imm_norm; tac ]
  | step_simpl ]; vn.

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition mfi_clob : list reg := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31].

(* [comment removed for export] *)
Definition mfi_m0 (mem : word -> option byte) (sp ra s0v s1v s2v s3v s4v addr size : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ sp (-8)) (LE8 ra))
    (at_ sp (-16)) (LE8 s0v))
    (at_ sp (-24)) (LE8 s1v))
    (at_ sp (-32)) (LE8 s2v))
    (at_ sp (-40)) (LE8 (Z_to_bv 64 0x8b124)))
    (at_ sp (-48)) (LE8 size))
    (at_ sp (-56)) (LE8 addr))
    (at_ sp (-64)) (LE8 s2v))
    (at_ sp (-72)) (LE8 s3v))
    (at_ sp (-80)) (LE8 s4v).
Definition mfi_m1 (mem : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v addr size name : word) (PGP : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (mfi_m0 mem sp ra s0v s1v s2v s3v s4v addr size)
    (at_ sp (-128)) (LE4 50))
    (at_ sp (-136)) (LE8 (Z_to_bv 64 0x82f50)))
    (at_ sp (-144)) (LE8 size))
    (at_ sp (-152)) (LE8 (Z_to_bv 64 1)))
    (at_ sp (-160)) (LE8 addr))
    (at_ sp (-168)) (LE8 name))
    (at_ sp (-176)) (LE8 (Z_to_bv 64 PGP)))
    (at_ sp (-184)) (LE8 s5v).
#[local] Hint Unfold mfi_m0 mfi_m1 : asfr.

Section MFIPRE.
  Variables (mem rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v addr size name : word) (PGP CF : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H11 : getr regs 11 = addr.
  Hypothesis H12 : getr regs 12 = size.
  Hypothesis H13 : getr regs 13 = name.
  Hypothesis H8 : getr regs 8 = s0v.   Hypothesis H9 : getr regs 9 = s1v.   Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v. Hypothesis H20 : getr regs 20 = s4v. Hypothesis H21 : getr regs 21 = s5v.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Haddr : (U addr mod 4096 = 0)%Z.
  Hypothesis Hsize : (U size mod 4096 = 0 /\ U size + 4096 < 2 ^ 63)%Z.
  Hypothesis Hname : (U name <> 0)%Z.
  Hypothesis HPGP : (AIMGLO <= PGP /\ PGP + 8 <= AIMGHI)%Z.
  Hypothesis HCF : (AIMGLO <= CF /\ CF + 264 <= AIMGHI)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ sp (-400)) 400 = true.
  Hypothesis Rgpg : rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 PGP)).
  Hypothesis Rpg : rdn BSEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis Rgcf : rdn BSEGS mem (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 CF)).
  Hypothesis Rdpm : rdn BSEGS mem (Z_to_bv 64 (CF + 260)) 1 = Some [Z_to_bv 8 0].

  #[local] Abbreviation M1 := (mfi_m1 mem sp ra s0v s1v s2v s3v s4v s5v addr size name PGP).

  Lemma mfi_pre :
    exists r, msteps BSEGS (mkst regs (0x8b0f8 : word) mem rom) (mkst r (0x811ac : word) M1 rom)
      /\ getr r 1 = Z_to_bv 64 0x82f6c /\ getr r 2 = at_ sp (-128)
      /\ getr r 8 = size /\ getr r 9 = Z_to_bv 64 1 /\ getr r 18 = addr /\ getr r 19 = name /\ getr r 20 = Z_to_bv 64 PGP
      /\ getr r 10 = addr /\ getr r 11 = size /\ getr r 12 = Z_to_bv 64 3 /\ getr r 13 = Z_to_bv 64 50
      /\ getr r 14 = Z_to_bv 64 (2 ^ 64 - 1) /\ getr r 15 = Z_to_bv 64 0 /\ getr r 17 = Z_to_bv 64 222
      /\ regs_agree (fun i : reg => In i (1%bv :: 2%bv :: 8%bv :: 9%bv :: 18%bv :: 19%bv :: 20%bv :: mfi_clob)) regs r.
  Proof using Rdpm Rgcf Rpg Rgpg Hstk HCF HPGP Hname Hsize Haddr Hsp H21 H20 H19 H18 H9 H8 H13 H12 H11 H2 H1 CF.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range addr) as Har. pose proof (u64_range size) as Hsr. pose proof (u64_range name) as Hnr.
    destruct Hsize as [Hsz1 Hsz2].
    wd_eexists. split.
    - an F_8b0f8 D_8b0f8.                              (* [comment removed for export] *)
      fsd F_8b0fc D_8b0fc (at_ sp (-8)).               (* [comment removed for export] *)
      fsd F_8b100 D_8b100 (at_ sp (-16)).              (* [comment removed for export] *)
      fsd F_8b104 D_8b104 (at_ sp (-24)).              (* [comment removed for export] *)
      fsd F_8b108 D_8b108 (at_ sp (-32)).              (* [comment removed for export] *)
      an F_8b10c D_8b10c.                              (* [comment removed for export] *)
      an F_8b110 D_8b110.                              (* [comment removed for export] *)
      an F_8b114 D_8b114.                              (* [comment removed for export] *)
      an F_8b118 D_8b118.                              (* [comment removed for export] *)
      an F_8b11c D_8b11c.                              (* [comment removed for export] *)
      an F_8b120 D_8b120.                              (* [comment removed for export] *)
      an F_83038 D_83038.                              (* [comment removed for export] *)
      an F_8303c D_8303c.                              (* [comment removed for export] *)
      an F_83040 D_83040.                              (* [comment removed for export] *)
      an F_82ec0 D_82ec0.                              (* [comment removed for export] *)
      fsd F_82ec4 D_82ec4 (at_ sp (-40)).              (* [comment removed for export] *)
      fsd F_82ec8 D_82ec8 (at_ sp (-48)).              (* [comment removed for export] *)
      fsd F_82ecc D_82ecc (at_ sp (-56)).              (* [comment removed for export] *)
      fsd F_82ed0 D_82ed0 (at_ sp (-64)).              (* [comment removed for export] *)
      fsd F_82ed4 D_82ed4 (at_ sp (-72)).              (* [comment removed for export] *)
      fsd F_82ed8 D_82ed8 (at_ sp (-80)).              (* [comment removed for export] *)
      an F_82edc D_82edc.                              (* [comment removed for export] *)
      an F_82ee0 D_82ee0.                              (* [comment removed for export] *)
      an F_82ee4 D_82ee4.                              (* [comment removed for export] *)
      an F_82ee8 D_82ee8.                              (* [comment removed for export] *)
      cld8 F_82eec D_82eec (Z_to_bv 64 PGP) Rgpg.      (* [comment removed for export] *)
      cld8 F_82ef0 D_82ef0 (Z_to_bv 64 4096) Rpg.      (* [comment removed for export] *)
      an F_82ef4 D_82ef4.                              (* [comment removed for export] *)
      ab_tk F_82ef8 D_82ef8 ltac:(condz).              (* [comment removed for export] *)
      an F_82f08 D_82f08.                              (* [comment removed for export] *)
      an F_82f0c D_82f0c.                              (* [comment removed for export] *)
      ab_ft F_82f10 D_82f10 ltac:(condz).              (* [comment removed for export] *)
      av F_82f14 D_82f14 (Z_to_bv 64 (U size + 4096)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av F_82f18 D_82f18 (Z_to_bv 64 (U size + 4095)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av F_82f1c D_82f1c (Z_to_bv 64 (2 ^ 64 - 2 ^ 12)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); unorm; apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av_and F_82f20 D_82f20 size
        ltac:(rewrite v_and_m4k; unorm; replace (U size + 4095 - (U size + 4095) mod 4096)%Z with (U size) by (Z.div_mod_to_equations; lia); apply Z_to_bv_bv_unsigned).   (* [comment removed for export] *)
      ab_tk F_82f24 D_82f24 ltac:(condz).              (* [comment removed for export] *)
      av_and F_82f34 D_82f34 addr
        ltac:(rewrite v_and_m4k; replace (U addr - U addr mod 4096)%Z with (U addr) by lia; apply Z_to_bv_bv_unsigned).   (* [comment removed for export] *)
      an F_82f38 D_82f38.                              (* [comment removed for export] *)
      fsw F_82f3c D_82f3c (at_ sp (-128)).             (* [comment removed for export] *)
      an F_82f40 D_82f40.                              (* [comment removed for export] *)
      an F_82f44 D_82f44.                              (* [comment removed for export] *)
      an F_82f48 D_82f48.                              (* [comment removed for export] *)
      an F_82f4c D_82f4c.                              (* [comment removed for export] *)
      an F_83554 D_83554.                              (* [comment removed for export] *)
      fsd F_83558 D_83558 (at_ sp (-136)).             (* [comment removed for export] *)
      fsd F_8355c D_8355c (at_ sp (-144)).             (* [comment removed for export] *)
      fsd F_83560 D_83560 (at_ sp (-152)).             (* [comment removed for export] *)
      fsd F_83564 D_83564 (at_ sp (-160)).             (* [comment removed for export] *)
      fsd F_83568 D_83568 (at_ sp (-168)).             (* [comment removed for export] *)
      fsd F_8356c D_8356c (at_ sp (-176)).             (* [comment removed for export] *)
      fsd F_83570 D_83570 (at_ sp (-184)).             (* [comment removed for export] *)
      change (wbytes _ _ _) with M1.
      an F_83574 D_83574.                              (* [comment removed for export] *)
      an F_83578 D_83578.                              (* [comment removed for export] *)
      ab_ft F_8357c D_8357c ltac:(condz).              (* [comment removed for export] *)
      an F_83580 D_83580.                              (* [comment removed for export] *)
      an F_83584 D_83584.                              (* [comment removed for export] *)
      cld8 F_83588 D_83588 (Z_to_bv 64 CF) Rgcf.       (* [comment removed for export] *)
      clbu F_8358c D_8358c (Z_to_bv 8 0) Rdpm.         (* [comment removed for export] *)
      an F_83590 D_83590.                              (* [comment removed for export] *)
      ab_tk F_83594 D_83594 ltac:(condz).              (* [comment removed for export] *)
      an F_836a4 D_836a4.                              (* [comment removed for export] *)
      fld F_836a8 D_836a8 (Z_to_bv 64 0x82f50).        (* [comment removed for export] *)
      fld F_836ac D_836ac size.                        (* [comment removed for export] *)
      fld F_836b0 D_836b0 (Z_to_bv 64 1).              (* [comment removed for export] *)
      fld F_836b4 D_836b4 addr.                        (* [comment removed for export] *)
      fld F_836b8 D_836b8 name.                        (* [comment removed for export] *)
      fld F_836bc D_836bc (Z_to_bv 64 PGP).            (* [comment removed for export] *)
      fld F_836c0 D_836c0 s5v.                         (* [comment removed for export] *)
      an F_836c4 D_836c4.                              (* [comment removed for export] *)
      rt F_836c8 D_836c8.                              (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := LE4 50) (v := Z_to_bv 64 50);
          [exact F_82f50 | reflexivity | exact D_82f50
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold mfi_m1 in G in change_no_check G' end);
            repeat (rewrite wc_rdn_wbytes_out3; [ | rd8_side ]);
            apply rdn_wbytes_hit4; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia
          | reflexivity]
        | step_simpl]; rewrite (v_lw_small 50) by lia; vn.   (* [comment removed for export] *)
      an F_82f54 D_82f54.                              (* [comment removed for export] *)
      an F_82f58 D_82f58.                              (* [comment removed for export] *)
      an F_82f5c D_82f5c.                              (* [comment removed for export] *)
      an F_82f60 D_82f60.                              (* [comment removed for export] *)
      an F_82f64 D_82f64.                              (* [comment removed for export] *)
      an F_82f68 D_82f68.                              (* [comment removed for export] *)
      an F_811a8 D_811a8.                              (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.

  (* [comment removed for export] *)
  Lemma mfi_m1_outside : forall x : word, (U x < U sp - 400 \/ U sp <= U x)%Z -> M1 x = mem x.
  Proof using Hsp.
    intros x Hx. pose proof (u64_range sp) as Hspr. (lazymatch goal with |- ?G => let G' := eval unfold mfi_m1, mfi_m0 in G in change_no_check G' end).
    repeat (rewrite wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
    reflexivity.
  Qed.
  Lemma mfi_m1_grows : mem_grows mem M1.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold mfi_m1, mfi_m0 in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma mfi_m1_slots : forall (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, Z_to_bv 64 0x8b124); (-48, size); (-56, addr); (-64, s2v);
               (-72, s3v); (-80, s4v)]%Z -> rdn BSEGS M1 (at_ sp k) 8 = Some (LE8 v).
  Proof using Hsp.
    intros k v Hin. pose proof (u64_range sp) as Hspr. (lazymatch goal with |- ?G => let G' := eval unfold mfi_m1, mfi_m0 in G in change_no_check G' end). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
  Qed.
End MFIPRE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MFIPOST.
  Variables (M2 rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v addr size name : word) (PGP CF : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = Z_to_bv 64 0x82f6c.
  Hypothesis H2 : getr regs 2 = at_ sp (-128).
  Hypothesis H8 : getr regs 8 = size.
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 1.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HCF : (AIMGLO <= CF /\ CF + 264 <= AIMGHI)%Z.
  Hypothesis Hsok : store_ok BSEGS M2 (at_ sp (-84)) 4 = true.
  Hypothesis S_ra : rdn BSEGS M2 (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis S_s0 : rdn BSEGS M2 (at_ sp (-16)) 8 = Some (LE8 s0v).
  Hypothesis S_s1 : rdn BSEGS M2 (at_ sp (-24)) 8 = Some (LE8 s1v).
  Hypothesis S_s2 : rdn BSEGS M2 (at_ sp (-32)) 8 = Some (LE8 s2v).
  Hypothesis S_cra : rdn BSEGS M2 (at_ sp (-40)) 8 = Some (LE8 (Z_to_bv 64 0x8b124)).
  Hypothesis S_c0 : rdn BSEGS M2 (at_ sp (-48)) 8 = Some (LE8 size).
  Hypothesis S_c1 : rdn BSEGS M2 (at_ sp (-56)) 8 = Some (LE8 addr).
  Hypothesis S_c2 : rdn BSEGS M2 (at_ sp (-64)) 8 = Some (LE8 s2v).
  Hypothesis S_s3 : rdn BSEGS M2 (at_ sp (-72)) 8 = Some (LE8 s3v).
  Hypothesis S_s4 : rdn BSEGS M2 (at_ sp (-80)) 8 = Some (LE8 s4v).

  Definition mfi_clob2 : list reg := 1%bv :: 2%bv :: 8%bv :: 9%bv :: 18%bv :: 19%bv :: 20%bv :: mfi_clob.

  (* [comment removed for export] *)
  Section OK.
    Hypothesis H10 : getr regs 10 = addr.
    Hypothesis Haddr : (U addr < 2 ^ 63)%Z.
    Hypothesis Hanz : (0 < U addr)%Z.
    Hypothesis Rgcf : rdn BSEGS M2 (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 CF)).
    Hypothesis Rlim : rdn BSEGS M2 (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)).
    Lemma mfi_ok :
      exists r, msteps BSEGS (mkst regs (0x811b0 : word) M2 rom)
                             (mkst r ra (wbytes M2 (at_ sp (-84)) (LE4 0xffffffffaaaaaaaa)) rom)
        /\ getr r 10 = addr /\ getr r 2 = sp /\ getr r 1 = ra
        /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v
        /\ regs_agree (fun i : reg => In i mfi_clob2) regs r.
    Proof using Rlim Rgcf Hanz Haddr H10 S_s4 S_s3 S_c2 S_c1 S_c0 S_cra S_s2 S_s1 S_s0 S_ra Hsok HCF Hret Hsp H8 H2 H1 CF size.
      pose proof (u64_range sp) as Hspr. pose proof (u64_range addr) as Har.
      wd_eexists. split.
      - rt F_811b0 D_811b0.                            (* [comment removed for export] *)
        an F_82f6c D_82f6c.                            (* [comment removed for export] *)
        an F_82f70 D_82f70.                            (* [comment removed for export] *)
        an F_82f74 D_82f74.                            (* [comment removed for export] *)
        an F_81188 D_81188.                            (* [comment removed for export] *)
        an F_8118c D_8118c.                            (* [comment removed for export] *)
        ab_tk F_81190 D_81190 ltac:(condz).            (* [comment removed for export] *)
        an F_811a0 D_811a0. sltu0.                     (* [comment removed for export] *)
        rt F_811a4 D_811a4.                            (* [comment removed for export] *)
        an F_82f78 D_82f78.                            (* [comment removed for export] *)
        an F_82f7c D_82f7c.                            (* [comment removed for export] *)
        fsw F_82f80 D_82f80 (at_ sp (-84)).            (* [comment removed for export] *)
        an F_82f84 D_82f84.                            (* [comment removed for export] *)
        an F_82f88 D_82f88.                            (* [comment removed for export] *)
        an F_82f8c D_82f8c.                            (* [comment removed for export] *)
        an F_81188 D_81188.                            (* [comment removed for export] *)
        an F_8118c D_8118c.                            (* [comment removed for export] *)
        ab_tk F_81190 D_81190 ltac:(condz).            (* [comment removed for export] *)
        an F_811a0 D_811a0. sltu0.                     (* [comment removed for export] *)
        rt F_811a4 D_811a4.                            (* [comment removed for export] *)
        ab_ft F_82f90 D_82f90 ltac:(condz).            (* [comment removed for export] *)
        an F_82f94 D_82f94.                            (* [comment removed for export] *)
        an F_82f98 D_82f98.                            (* [comment removed for export] *)
        an F_7d08c D_7d08c.                            (* [comment removed for export] *)
        cld8 F_7d090 D_7d090 (Z_to_bv 64 CF) Rgcf.     (* [comment removed for export] *)
        cld8 F_7d094 D_7d094 (Z_to_bv 64 0) Rlim.      (* [comment removed for export] *)
        ab_tk F_7d098 D_7d098 ltac:(condz).            (* [comment removed for export] *)
        rt F_7d0b4 D_7d0b4.                            (* [comment removed for export] *)
        an F_82f9c D_82f9c.                            (* [comment removed for export] *)
        cld8 F_82fa0 D_82fa0 (Z_to_bv 64 0x8b124) S_cra.   (* [comment removed for export] *)
        cld8 F_82fa4 D_82fa4 size S_c0.                (* [comment removed for export] *)
        cld8 F_82fa8 D_82fa8 addr S_c1.                (* [comment removed for export] *)
        cld8 F_82fac D_82fac s2v S_c2.                 (* [comment removed for export] *)
        cld8 F_82fb0 D_82fb0 s3v S_s3.                 (* [comment removed for export] *)
        cld8 F_82fb4 D_82fb4 s4v S_s4.                 (* [comment removed for export] *)
        an F_82fb8 D_82fb8.                            (* [comment removed for export] *)
        rt F_82fbc D_82fbc.                            (* [comment removed for export] *)
        ab_ft F_8b124 D_8b124 ltac:(condz).            (* [comment removed for export] *)
        cld8 F_8b128 D_8b128 ra S_ra.                  (* [comment removed for export] *)
        cld8 F_8b12c D_8b12c s0v S_s0.                 (* [comment removed for export] *)
        cld8 F_8b130 D_8b130 s1v S_s1.                 (* [comment removed for export] *)
        cld8 F_8b134 D_8b134 s2v S_s2.                 (* [comment removed for export] *)
        an F_8b138 D_8b138.                            (* [comment removed for export] *)
        aret F_8b13c D_8b13c ra.                       (* [comment removed for export] *)
        wd_refl.
      - post. (lazymatch goal with |- ?G => let G' := eval unfold mfi_clob2, mfi_clob in G in change_no_check G' end). ra_solve.
    Qed.
  End OK.
End MFIPOST.
End FPGen.
