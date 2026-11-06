(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.InstrEnc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Bo_code_8cef4_8dab4.
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
Definition W_8cef4 : bv 32 := @BV 32 0xfc010113%Z I.
Lemma F_8cef4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cef4%Z I : word) = Some W_8cef4.
Proof. vm_refl. Qed.
Lemma D_8cef4 : decode_any W_8cef4 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4032%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cef8 : bv 32 := @BV 32 0x02113c23%Z I.
Lemma F_8cef8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cef8%Z I : word) = Some W_8cef8.
Proof. vm_refl. Qed.
Lemma D_8cef8 : decode_any W_8cef8 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cefc : bv 32 := @BV 32 0x02813823%Z I.
Lemma F_8cefc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cefc%Z I : word) = Some W_8cefc.
Proof. vm_refl. Qed.
Lemma D_8cefc : decode_any W_8cefc = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf00 : bv 32 := @BV 32 0x02913423%Z I.
Lemma F_8cf00 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf00%Z I : word) = Some W_8cf00.
Proof. vm_refl. Qed.
Lemma D_8cf00 : decode_any W_8cf00 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf04 : bv 32 := @BV 32 0x03213023%Z I.
Lemma F_8cf04 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf04%Z I : word) = Some W_8cf04.
Proof. vm_refl. Qed.
Lemma D_8cf04 : decode_any W_8cf04 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf08 : bv 32 := @BV 32 0x01313c23%Z I.
Lemma F_8cf08 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf08%Z I : word) = Some W_8cf08.
Proof. vm_refl. Qed.
Lemma D_8cf08 : decode_any W_8cf08 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 19%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf0c : bv 32 := @BV 32 0x01413823%Z I.
Lemma F_8cf0c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf0c%Z I : word) = Some W_8cf0c.
Proof. vm_refl. Qed.
Lemma D_8cf0c : decode_any W_8cf0c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 20%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf10 : bv 32 := @BV 32 0x01513423%Z I.
Lemma F_8cf10 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf10%Z I : word) = Some W_8cf10.
Proof. vm_refl. Qed.
Lemma D_8cf10 : decode_any W_8cf10 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 21%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf14 : bv 32 := @BV 32 0x00058993%Z I.
Lemma F_8cf14 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf14%Z I : word) = Some W_8cf14.
Proof. vm_refl. Qed.
Lemma D_8cf14 : decode_any W_8cf14 = Some (OpImm ALU_ADD (@BV 5 19%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf18 : bv 32 := @BV 32 0x0085aa03%Z I.
Lemma F_8cf18 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf18%Z I : word) = Some W_8cf18.
Proof. vm_refl. Qed.
Lemma D_8cf18 : decode_any W_8cf18 = Some (Load SZ4 true (@BV 5 20%Z I) (@BV 5 11%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf1c : bv 32 := @BV 32 0x00c5aa83%Z I.
Lemma F_8cf1c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf1c%Z I : word) = Some W_8cf1c.
Proof. vm_refl. Qed.
Lemma D_8cf1c : decode_any W_8cf1c = Some (Load SZ4 true (@BV 5 21%Z I) (@BV 5 11%Z I) (@BV 12 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf20 : bv 32 := @BV 32 0x015a65b3%Z I.
Lemma F_8cf20 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf20%Z I : word) = Some W_8cf20.
Proof. vm_refl. Qed.
Lemma D_8cf20 : decode_any W_8cf20 = Some (Op ALU_OR (@BV 5 11%Z I) (@BV 5 20%Z I) (@BV 5 21%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf24 : bv 32 := @BV 32 0x00059663%Z I.
Lemma F_8cf24 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf24%Z I : word) = Some W_8cf24.
Proof. vm_refl. Qed.
Lemma D_8cf24 : decode_any W_8cf24 = Some (Branch BC_NE (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf30 : bv 32 := @BV 32 0x00050493%Z I.
Lemma F_8cf30 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf30%Z I : word) = Some W_8cf30.
Proof. vm_refl. Qed.
Lemma D_8cf30 : decode_any W_8cf30 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf34 : bv 32 := @BV 32 0x10000513%Z I.
Lemma F_8cf34 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf34%Z I : word) = Some W_8cf34.
Proof. vm_refl. Qed.
Lemma D_8cf34 : decode_any W_8cf34 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 256%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf38 : bv 32 := @BV 32 0x0aaafe63%Z I.
Lemma F_8cf38 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf38%Z I : word) = Some W_8cf38.
Proof. vm_refl. Qed.
Lemma D_8cf38 : decode_any W_8cf38 = Some (Branch BC_GEU (@BV 5 21%Z I) (@BV 5 10%Z I) (@BV 13 188%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf3c : bv 32 := @BV 32 0x00060413%Z I.
Lemma F_8cf3c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf3c%Z I : word) = Some W_8cf3c.
Proof. vm_refl. Qed.
Lemma D_8cf3c : decode_any W_8cf3c = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf40 : bv 32 := @BV 32 0x0ff00513%Z I.
Lemma F_8cf40 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf40%Z I : word) = Some W_8cf40.
Proof. vm_refl. Qed.
Lemma D_8cf40 : decode_any W_8cf40 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 255%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf44 : bv 32 := @BV 32 0x00aa6463%Z I.
Lemma F_8cf44 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf44%Z I : word) = Some W_8cf44.
Proof. vm_refl. Qed.
Lemma D_8cf44 : decode_any W_8cf44 = Some (Branch BC_LTU (@BV 5 20%Z I) (@BV 5 10%Z I) (@BV 13 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf4c : bv 32 := @BV 32 0x00013023%Z I.
Lemma F_8cf4c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf4c%Z I : word) = Some W_8cf4c.
Proof. vm_refl. Qed.
Lemma D_8cf4c : decode_any W_8cf4c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf50 : bv 32 := @BV 32 0x00043023%Z I.
Lemma F_8cf50 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf50%Z I : word) = Some W_8cf50.
Proof. vm_refl. Qed.
Lemma D_8cf50 : decode_any W_8cf50 = Some (Store SZ8 (@BV 5 8%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf54 : bv 32 := @BV 32 0x001a0913%Z I.
Lemma F_8cf54 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf54%Z I : word) = Some W_8cf54.
Proof. vm_refl. Qed.
Lemma D_8cf54 : decode_any W_8cf54 = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 20%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf58 : bv 32 := @BV 32 0x00010613%Z I.
Lemma F_8cf58 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf58%Z I : word) = Some W_8cf58.
Proof. vm_refl. Qed.
Lemma D_8cf58 : decode_any W_8cf58 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf5c : bv 32 := @BV 32 0x00048513%Z I.
Lemma F_8cf5c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf5c%Z I : word) = Some W_8cf5c.
Proof. vm_refl. Qed.
Lemma D_8cf5c : decode_any W_8cf5c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf60 : bv 32 := @BV 32 0x00090593%Z I.
Lemma F_8cf60 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf60%Z I : word) = Some W_8cf60.
Proof. vm_refl. Qed.
Lemma D_8cf60 : decode_any W_8cf60 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf64 : bv 32 := @BV 32 0x00040693%Z I.
Lemma F_8cf64 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf64%Z I : word) = Some W_8cf64.
Proof. vm_refl. Qed.
Lemma D_8cf64 : decode_any W_8cf64 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf68 : bv 32 := @BV 32 0x0b0000ef%Z I.
Lemma F_8cf68 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf68%Z I : word) = Some W_8cf68.
Proof. vm_refl. Qed.
Lemma D_8cf68 : decode_any W_8cf68 = Some (Jal (@BV 5 1%Z I) (@BV 21 176%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf6c : bv 32 := @BV 32 0x06050263%Z I.
Lemma F_8cf6c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf6c%Z I : word) = Some W_8cf6c.
Proof. vm_refl. Qed.
Lemma D_8cf6c : decode_any W_8cf6c = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 100%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf70 : bv 32 := @BV 32 0x008a961b%Z I.
Lemma F_8cf70 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf70%Z I : word) = Some W_8cf70.
Proof. vm_refl. Qed.
Lemma D_8cf70 : decode_any W_8cf70 = Some (ShiftImm32 ALU_SLL (@BV 5 12%Z I) (@BV 5 21%Z I) (@BV 5 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf74 : bv 32 := @BV 32 0x0009b583%Z I.
Lemma F_8cf74 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf74%Z I : word) = Some W_8cf74.
Proof. vm_refl. Qed.
Lemma D_8cf74 : decode_any W_8cf74 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf78 : bv 32 := @BV 32 0x01466633%Z I.
Lemma F_8cf78 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf78%Z I : word) = Some W_8cf78.
Proof. vm_refl. Qed.
Lemma D_8cf78 : decode_any W_8cf78 = Some (Op ALU_OR (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 5 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf7c : bv 32 := @BV 32 0x00c53023%Z I.
Lemma F_8cf7c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf7c%Z I : word) = Some W_8cf7c.
Proof. vm_refl. Qed.
Lemma D_8cf7c : decode_any W_8cf7c = Some (Store SZ8 (@BV 5 10%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf80 : bv 32 := @BV 32 0x00850513%Z I.
Lemma F_8cf80 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf80%Z I : word) = Some W_8cf80.
Proof. vm_refl. Qed.
Lemma D_8cf80 : decode_any W_8cf80 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf84 : bv 32 := @BV 32 0x003a1613%Z I.
Lemma F_8cf84 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf84%Z I : word) = Some W_8cf84.
Proof. vm_refl. Qed.
Lemma D_8cf84 : decode_any W_8cf84 = Some (ShiftImm ALU_SLL (@BV 5 12%Z I) (@BV 5 20%Z I) (@BV 6 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf88 : bv 32 := @BV 32 0x9a5f30ef%Z I.
Lemma F_8cf88 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf88%Z I : word) = Some W_8cf88.
Proof. vm_refl. Qed.
Lemma D_8cf88 : decode_any W_8cf88 = Some (Jal (@BV 5 1%Z I) (@BV 21 2046372%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf8c : bv 32 := @BV 32 0x00013503%Z I.
Lemma F_8cf8c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf8c%Z I : word) = Some W_8cf8c.
Proof. vm_refl. Qed.
Lemma D_8cf8c : decode_any W_8cf8c = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf90 : bv 32 := @BV 32 0x01055513%Z I.
Lemma F_8cf90 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf90%Z I : word) = Some W_8cf90.
Proof. vm_refl. Qed.
Lemma D_8cf90 : decode_any W_8cf90 = Some (ShiftImm ALU_SRL (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 6 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf94 : bv 32 := @BV 32 0xff057513%Z I.
Lemma F_8cf94 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf94%Z I : word) = Some W_8cf94.
Proof. vm_refl. Qed.
Lemma D_8cf94 : decode_any W_8cf94 = Some (OpImm ALU_AND (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 4080%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf98 : bv 32 := @BV 32 0x00a48533%Z I.
Lemma F_8cf98 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf98%Z I : word) = Some W_8cf98.
Proof. vm_refl. Qed.
Lemma D_8cf98 : decode_any W_8cf98 = Some (Op ALU_ADD (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cf9c : bv 32 := @BV 32 0x01850513%Z I.
Lemma F_8cf9c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cf9c%Z I : word) = Some W_8cf9c.
Proof. vm_refl. Qed.
Lemma D_8cf9c : decode_any W_8cf9c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cfa0 : bv 32 := @BV 32 0x0325252f%Z I.
Lemma F_8cfa0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cfa0%Z I : word) = Some W_8cfa0.
Proof. vm_refl. Qed.
Lemma D_8cfa0 : decode_any W_8cfa0 = Some (Amo AMO_ADD AW false true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 5 18%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cfa4 : bv 32 := @BV 32 0x001005b7%Z I.
Lemma F_8cfa4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cfa4%Z I : word) = Some W_8cfa4.
Proof. vm_refl. Qed.
Lemma D_8cfa4 : decode_any W_8cfa4 = Some (Lui (@BV 5 11%Z I) (@BV 20 256%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cfa8 : bv 32 := @BV 32 0x02051513%Z I.
Lemma F_8cfa8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cfa8%Z I : word) = Some W_8cfa8.
Proof. vm_refl. Qed.
Lemma D_8cfa8 : decode_any W_8cfa8 = Some (ShiftImm ALU_SLL (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cfac : bv 32 := @BV 32 0x02055513%Z I.
Lemma F_8cfac : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cfac%Z I : word) = Some W_8cfac.
Proof. vm_refl. Qed.
Lemma D_8cfac : decode_any W_8cfac = Some (ShiftImm ALU_SRL (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cfb0 : bv 32 := @BV 32 0x00a90533%Z I.
Lemma F_8cfb0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cfb0%Z I : word) = Some W_8cfb0.
Proof. vm_refl. Qed.
Lemma D_8cfb0 : decode_any W_8cfb0 = Some (Op ALU_ADD (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cfb4 : bv 32 := @BV 32 0x00043603%Z I.
Lemma F_8cfb4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cfb4%Z I : word) = Some W_8cfb4.
Proof. vm_refl. Qed.
Lemma D_8cfb4 : decode_any W_8cfb4 = Some (Load SZ8 true (@BV 5 12%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cfb8 : bv 32 := @BV 32 0x00b54533%Z I.
Lemma F_8cfb8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cfb8%Z I : word) = Some W_8cfb8.
Proof. vm_refl. Qed.
Lemma D_8cfb8 : decode_any W_8cfb8 = Some (Op ALU_XOR (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cfbc : bv 32 := @BV 32 0x00012583%Z I.
Lemma F_8cfbc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cfbc%Z I : word) = Some W_8cfbc.
Proof. vm_refl. Qed.
Lemma D_8cfbc : decode_any W_8cfbc = Some (Load SZ4 true (@BV 5 11%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cfc0 : bv 32 := @BV 32 0x00153513%Z I.
Lemma F_8cfc0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cfc0%Z I : word) = Some W_8cfc0.
Proof. vm_refl. Qed.
Lemma D_8cfc0 : decode_any W_8cfc0 = Some (OpImm ALU_SLTU (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cfc4 : bv 32 := @BV 32 0x00a60533%Z I.
Lemma F_8cfc4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cfc4%Z I : word) = Some W_8cfc4.
Proof. vm_refl. Qed.
Lemma D_8cfc4 : decode_any W_8cfc4 = Some (Op ALU_ADD (@BV 5 10%Z I) (@BV 5 12%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cfc8 : bv 32 := @BV 32 0x00a43023%Z I.
Lemma F_8cfc8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cfc8%Z I : word) = Some W_8cfc8.
Proof. vm_refl. Qed.
Lemma D_8cfc8 : decode_any W_8cfc8 = Some (Store SZ8 (@BV 5 8%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cfcc : bv 32 := @BV 32 0x0015851b%Z I.
Lemma F_8cfcc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cfcc%Z I : word) = Some W_8cfcc.
Proof. vm_refl. Qed.
Lemma D_8cfcc : decode_any W_8cfcc = Some (OpImm32 (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cfd0 : bv 32 := @BV 32 0x03813083%Z I.
Lemma F_8cfd0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cfd0%Z I : word) = Some W_8cfd0.
Proof. vm_refl. Qed.
Lemma D_8cfd0 : decode_any W_8cfd0 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cfd4 : bv 32 := @BV 32 0x03013403%Z I.
Lemma F_8cfd4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cfd4%Z I : word) = Some W_8cfd4.
Proof. vm_refl. Qed.
Lemma D_8cfd4 : decode_any W_8cfd4 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cfd8 : bv 32 := @BV 32 0x02813483%Z I.
Lemma F_8cfd8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cfd8%Z I : word) = Some W_8cfd8.
Proof. vm_refl. Qed.
Lemma D_8cfd8 : decode_any W_8cfd8 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cfdc : bv 32 := @BV 32 0x02013903%Z I.
Lemma F_8cfdc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cfdc%Z I : word) = Some W_8cfdc.
Proof. vm_refl. Qed.
Lemma D_8cfdc : decode_any W_8cfdc = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cfe0 : bv 32 := @BV 32 0x01813983%Z I.
Lemma F_8cfe0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cfe0%Z I : word) = Some W_8cfe0.
Proof. vm_refl. Qed.
Lemma D_8cfe0 : decode_any W_8cfe0 = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cfe4 : bv 32 := @BV 32 0x01013a03%Z I.
Lemma F_8cfe4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cfe4%Z I : word) = Some W_8cfe4.
Proof. vm_refl. Qed.
Lemma D_8cfe4 : decode_any W_8cfe4 = Some (Load SZ8 true (@BV 5 20%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cfe8 : bv 32 := @BV 32 0x00813a83%Z I.
Lemma F_8cfe8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cfe8%Z I : word) = Some W_8cfe8.
Proof. vm_refl. Qed.
Lemma D_8cfe8 : decode_any W_8cfe8 = Some (Load SZ8 true (@BV 5 21%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cfec : bv 32 := @BV 32 0x04010113%Z I.
Lemma F_8cfec : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cfec%Z I : word) = Some W_8cfec.
Proof. vm_refl. Qed.
Lemma D_8cfec : decode_any W_8cfec = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cff0 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_8cff0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8cff0%Z I : word) = Some W_8cff0.
Proof. vm_refl. Qed.
Lemma D_8cff0 : decode_any W_8cff0 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.




























(* [comment removed for export] *)
Definition W_8d018 : bv 32 := @BV 32 0xff010113%Z I.
Lemma F_8d018 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d018%Z I : word) = Some W_8d018.
Proof. vm_refl. Qed.
Lemma D_8d018 : decode_any W_8d018 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4080%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d01c : bv 32 := @BV 32 0x00113423%Z I.
Lemma F_8d01c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d01c%Z I : word) = Some W_8d01c.
Proof. vm_refl. Qed.
Lemma D_8d01c : decode_any W_8d01c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d020 : bv 32 := @BV 32 0x00813023%Z I.
Lemma F_8d020 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d020%Z I : word) = Some W_8d020.
Proof. vm_refl. Qed.
Lemma D_8d020 : decode_any W_8d020 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d024 : bv 32 := @BV 32 0x00058793%Z I.
Lemma F_8d024 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d024%Z I : word) = Some W_8d024.
Proof. vm_refl. Qed.
Lemma D_8d024 : decode_any W_8d024 = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d028 : bv 32 := @BV 32 0x00050593%Z I.
Lemma F_8d028 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d028%Z I : word) = Some W_8d028.
Proof. vm_refl. Qed.
Lemma D_8d028 : decode_any W_8d028 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d02c : bv 32 := @BV 32 0x00f5342f%Z I.
Lemma F_8d02c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d02c%Z I : word) = Some W_8d02c.
Proof. vm_refl. Qed.
Lemma D_8d02c : decode_any W_8d02c = Some (Amo AMO_ADD AD false false (@BV 5 8%Z I) (@BV 5 10%Z I) (@BV 5 15%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d030 : bv 32 := @BV 32 0xfff78513%Z I.
Lemma F_8d030 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d030%Z I : word) = Some W_8d030.
Proof. vm_refl. Qed.
Lemma D_8d030 : decode_any W_8d030 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 15%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d034 : bv 32 := @BV 32 0x01445293%Z I.
Lemma F_8d034 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d034%Z I : word) = Some W_8d034.
Proof. vm_refl. Qed.
Lemma D_8d034 : decode_any W_8d034 = Some (ShiftImm ALU_SRL (@BV 5 5%Z I) (@BV 5 8%Z I) (@BV 6 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d038 : bv 32 := @BV 32 0x00850733%Z I.
Lemma F_8d038 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d038%Z I : word) = Some W_8d038.
Proof. vm_refl. Qed.
Lemma D_8d038 : decode_any W_8d038 = Some (Op ALU_ADD (@BV 5 14%Z I) (@BV 5 10%Z I) (@BV 5 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d03c : bv 32 := @BV 32 0x01475313%Z I.
Lemma F_8d03c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d03c%Z I : word) = Some W_8d03c.
Proof. vm_refl. Qed.
Lemma D_8d03c : decode_any W_8d03c = Some (ShiftImm ALU_SRL (@BV 5 6%Z I) (@BV 5 14%Z I) (@BV 6 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d040 : bv 32 := @BV 32 0x04629863%Z I.
Lemma F_8d040 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d040%Z I : word) = Some W_8d040.
Proof. vm_refl. Qed.
Lemma D_8d040 : decode_any W_8d040 = Some (Branch BC_NE (@BV 5 5%Z I) (@BV 5 6%Z I) (@BV 13 80%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d044 : bv 32 := @BV 32 0x02045513%Z I.
Lemma F_8d044 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d044%Z I : word) = Some W_8d044.
Proof. vm_refl. Qed.
Lemma D_8d044 : decode_any W_8d044 = Some (ShiftImm ALU_SRL (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d048 : bv 32 := @BV 32 0x00050c63%Z I.
Lemma F_8d048 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d048%Z I : word) = Some W_8d048.
Proof. vm_refl. Qed.
Lemma D_8d048 : decode_any W_8d048 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d060 : bv 32 := @BV 32 0x00863023%Z I.
Lemma F_8d060 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d060%Z I : word) = Some W_8d060.
Proof. vm_refl. Qed.
Lemma D_8d060 : decode_any W_8d060 = Some (Store SZ8 (@BV 5 12%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d064 : bv 32 := @BV 32 0x00429613%Z I.
Lemma F_8d064 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d064%Z I : word) = Some W_8d064.
Proof. vm_refl. Qed.
Lemma D_8d064 : decode_any W_8d064 = Some (ShiftImm ALU_SLL (@BV 5 12%Z I) (@BV 5 5%Z I) (@BV 6 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d068 : bv 32 := @BV 32 0x00c58633%Z I.
Lemma F_8d068 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d068%Z I : word) = Some W_8d068.
Proof. vm_refl. Qed.
Lemma D_8d068 : decode_any W_8d068 = Some (Op ALU_ADD (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d06c : bv 32 := @BV 32 0x01063503%Z I.
Lemma F_8d06c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d06c%Z I : word) = Some W_8d06c.
Proof. vm_refl. Qed.
Lemma D_8d06c : decode_any W_8d06c = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 12%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d070 : bv 32 := @BV 32 0x0a050a63%Z I.
Lemma F_8d070 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d070%Z I : word) = Some W_8d070.
Proof. vm_refl. Qed.
Lemma D_8d070 : decode_any W_8d070 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 180%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d074 : bv 32 := @BV 32 0x02c41413%Z I.
Lemma F_8d074 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d074%Z I : word) = Some W_8d074.
Proof. vm_refl. Qed.
Lemma D_8d074 : decode_any W_8d074 = Some (ShiftImm ALU_SLL (@BV 5 8%Z I) (@BV 5 8%Z I) (@BV 6 44%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d078 : bv 32 := @BV 32 0x02945413%Z I.
Lemma F_8d078 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d078%Z I : word) = Some W_8d078.
Proof. vm_refl. Qed.
Lemma D_8d078 : decode_any W_8d078 = Some (ShiftImm ALU_SRL (@BV 5 8%Z I) (@BV 5 8%Z I) (@BV 6 41%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d07c : bv 32 := @BV 32 0x00850533%Z I.
Lemma F_8d07c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d07c%Z I : word) = Some W_8d07c.
Proof. vm_refl. Qed.
Lemma D_8d07c : decode_any W_8d07c = Some (Op ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 5 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d080 : bv 32 := @BV 32 0x00813083%Z I.
Lemma F_8d080 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d080%Z I : word) = Some W_8d080.
Proof. vm_refl. Qed.
Lemma D_8d080 : decode_any W_8d080 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d084 : bv 32 := @BV 32 0x00013403%Z I.
Lemma F_8d084 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d084%Z I : word) = Some W_8d084.
Proof. vm_refl. Qed.
Lemma D_8d084 : decode_any W_8d084 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d088 : bv 32 := @BV 32 0x01010113%Z I.
Lemma F_8d088 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d088%Z I : word) = Some W_8d088.
Proof. vm_refl. Qed.
Lemma D_8d088 : decode_any W_8d088 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d08c : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_8d08c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d08c%Z I : word) = Some W_8d08c.
Proof. vm_refl. Qed.
Lemma D_8d08c : decode_any W_8d08c = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d090 : bv 32 := @BV 32 0x00100737%Z I.
Lemma F_8d090 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d090%Z I : word) = Some W_8d090.
Proof. vm_refl. Qed.
Lemma D_8d090 : decode_any W_8d090 = Some (Lui (@BV 5 14%Z I) (@BV 20 256%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d094 : bv 32 := @BV 32 0x08f76e63%Z I.
Lemma F_8d094 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d094%Z I : word) = Some W_8d094.
Proof. vm_refl. Qed.
Lemma D_8d094 : decode_any W_8d094 = Some (Branch BC_LTU (@BV 5 14%Z I) (@BV 5 15%Z I) (@BV 13 156%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d098 : bv 32 := @BV 32 0x01058813%Z I.
Lemma F_8d098 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d098%Z I : word) = Some W_8d098.
Proof. vm_refl. Qed.
Lemma D_8d098 : decode_any W_8d098 = Some (OpImm ALU_ADD (@BV 5 16%Z I) (@BV 5 11%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d09c : bv 32 := @BV 32 0xfff7089b%Z I.
Lemma F_8d09c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d09c%Z I : word) = Some W_8d09c.
Proof. vm_refl. Qed.
Lemma D_8d09c : decode_any W_8d09c = Some (OpImm32 (@BV 5 17%Z I) (@BV 5 14%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0a0 : bv 32 := @BV 32 0x011473b3%Z I.
Lemma F_8d0a0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d0a0%Z I : word) = Some W_8d0a0.
Proof. vm_refl. Qed.
Lemma D_8d0a0 : decode_any W_8d0a0 = Some (Op ALU_AND (@BV 5 7%Z I) (@BV 5 8%Z I) (@BV 5 17%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0a4 : bv 32 := @BV 32 0x00429293%Z I.
Lemma F_8d0a4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d0a4%Z I : word) = Some W_8d0a4.
Proof. vm_refl. Qed.
Lemma D_8d0a4 : decode_any W_8d0a4 = Some (ShiftImm ALU_SLL (@BV 5 5%Z I) (@BV 5 5%Z I) (@BV 6 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0a8 : bv 32 := @BV 32 0x407703b3%Z I.
Lemma F_8d0a8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d0a8%Z I : word) = Some W_8d0a8.
Proof. vm_refl. Qed.
Lemma D_8d0a8 : decode_any W_8d0a8 = Some (Op ALU_SUB (@BV 5 7%Z I) (@BV 5 14%Z I) (@BV 5 7%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0ac : bv 32 := @BV 32 0x005802b3%Z I.
Lemma F_8d0ac : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d0ac%Z I : word) = Some W_8d0ac.
Proof. vm_refl. Qed.
Lemma D_8d0ac : decode_any W_8d0ac = Some (Op ALU_ADD (@BV 5 5%Z I) (@BV 5 16%Z I) (@BV 5 5%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0b0 : bv 32 := @BV 32 0x00828293%Z I.
Lemma F_8d0b0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d0b0%Z I : word) = Some W_8d0b0.
Proof. vm_refl. Qed.
Lemma D_8d0b0 : decode_any W_8d0b0 = Some (OpImm ALU_ADD (@BV 5 5%Z I) (@BV 5 5%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0b4 : bv 32 := @BV 32 0x0272a2af%Z I.
Lemma F_8d0b4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d0b4%Z I : word) = Some W_8d0b4.
Proof. vm_refl. Qed.
Lemma D_8d0b4 : decode_any W_8d0b4 = Some (Amo AMO_ADD AW false true (@BV 5 5%Z I) (@BV 5 5%Z I) (@BV 5 7%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0b8 : bv 32 := @BV 32 0x00431313%Z I.
Lemma F_8d0b8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d0b8%Z I : word) = Some W_8d0b8.
Proof. vm_refl. Qed.
Lemma D_8d0b8 : decode_any W_8d0b8 = Some (ShiftImm ALU_SLL (@BV 5 6%Z I) (@BV 5 6%Z I) (@BV 6 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0bc : bv 32 := @BV 32 0x00680333%Z I.
Lemma F_8d0bc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d0bc%Z I : word) = Some W_8d0bc.
Proof. vm_refl. Qed.
Lemma D_8d0bc : decode_any W_8d0bc = Some (Op ALU_ADD (@BV 5 6%Z I) (@BV 5 16%Z I) (@BV 5 6%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0c0 : bv 32 := @BV 32 0x40778e33%Z I.
Lemma F_8d0c0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d0c0%Z I : word) = Some W_8d0c0.
Proof. vm_refl. Qed.
Lemma D_8d0c0 : decode_any W_8d0c0 = Some (Op ALU_SUB (@BV 5 28%Z I) (@BV 5 15%Z I) (@BV 5 7%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0c4 : bv 32 := @BV 32 0x02029293%Z I.
Lemma F_8d0c4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d0c4%Z I : word) = Some W_8d0c4.
Proof. vm_refl. Qed.
Lemma D_8d0c4 : decode_any W_8d0c4 = Some (ShiftImm ALU_SLL (@BV 5 5%Z I) (@BV 5 5%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0c8 : bv 32 := @BV 32 0x0202d293%Z I.
Lemma F_8d0c8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d0c8%Z I : word) = Some W_8d0c8.
Proof. vm_refl. Qed.
Lemma D_8d0c8 : decode_any W_8d0c8 = Some (ShiftImm ALU_SRL (@BV 5 5%Z I) (@BV 5 5%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0cc : bv 32 := @BV 32 0x005382b3%Z I.
Lemma F_8d0cc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d0cc%Z I : word) = Some W_8d0cc.
Proof. vm_refl. Qed.
Lemma D_8d0cc : decode_any W_8d0cc = Some (Op ALU_ADD (@BV 5 5%Z I) (@BV 5 7%Z I) (@BV 5 5%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0d0 : bv 32 := @BV 32 0x0006b383%Z I.
Lemma F_8d0d0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d0d0%Z I : word) = Some W_8d0d0.
Proof. vm_refl. Qed.
Lemma D_8d0d0 : decode_any W_8d0d0 = Some (Load SZ8 true (@BV 5 7%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0d4 : bv 32 := @BV 32 0x00830313%Z I.
Lemma F_8d0d4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d0d4%Z I : word) = Some W_8d0d4.
Proof. vm_refl. Qed.
Lemma D_8d0d4 : decode_any W_8d0d4 = Some (OpImm ALU_ADD (@BV 5 6%Z I) (@BV 5 6%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0d8 : bv 32 := @BV 32 0x00e2c2b3%Z I.
Lemma F_8d0d8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d0d8%Z I : word) = Some W_8d0d8.
Proof. vm_refl. Qed.
Lemma D_8d0d8 : decode_any W_8d0d8 = Some (Op ALU_XOR (@BV 5 5%Z I) (@BV 5 5%Z I) (@BV 5 14%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0dc : bv 32 := @BV 32 0x0012b293%Z I.
Lemma F_8d0dc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d0dc%Z I : word) = Some W_8d0dc.
Proof. vm_refl. Qed.
Lemma D_8d0dc : decode_any W_8d0dc = Some (OpImm ALU_SLTU (@BV 5 5%Z I) (@BV 5 5%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0e0 : bv 32 := @BV 32 0x005382b3%Z I.
Lemma F_8d0e0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d0e0%Z I : word) = Some W_8d0e0.
Proof. vm_refl. Qed.
Lemma D_8d0e0 : decode_any W_8d0e0 = Some (Op ALU_ADD (@BV 5 5%Z I) (@BV 5 7%Z I) (@BV 5 5%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0e4 : bv 32 := @BV 32 0x0056b023%Z I.
Lemma F_8d0e4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d0e4%Z I : word) = Some W_8d0e4.
Proof. vm_refl. Qed.
Lemma D_8d0e4 : decode_any W_8d0e4 = Some (Store SZ8 (@BV 5 13%Z I) (@BV 5 5%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0e8 : bv 32 := @BV 32 0x03c322af%Z I.
Lemma F_8d0e8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d0e8%Z I : word) = Some W_8d0e8.
Proof. vm_refl. Qed.
Lemma D_8d0e8 : decode_any W_8d0e8 = Some (Amo AMO_ADD AW false true (@BV 5 5%Z I) (@BV 5 6%Z I) (@BV 5 28%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0ec : bv 32 := @BV 32 0x0006b303%Z I.
Lemma F_8d0ec : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d0ec%Z I : word) = Some W_8d0ec.
Proof. vm_refl. Qed.
Lemma D_8d0ec : decode_any W_8d0ec = Some (Load SZ8 true (@BV 5 6%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0f0 : bv 32 := @BV 32 0x02029293%Z I.
Lemma F_8d0f0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d0f0%Z I : word) = Some W_8d0f0.
Proof. vm_refl. Qed.
Lemma D_8d0f0 : decode_any W_8d0f0 = Some (ShiftImm ALU_SLL (@BV 5 5%Z I) (@BV 5 5%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0f4 : bv 32 := @BV 32 0x0202d293%Z I.
Lemma F_8d0f4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d0f4%Z I : word) = Some W_8d0f4.
Proof. vm_refl. Qed.
Lemma D_8d0f4 : decode_any W_8d0f4 = Some (ShiftImm ALU_SRL (@BV 5 5%Z I) (@BV 5 5%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0f8 : bv 32 := @BV 32 0x005e02b3%Z I.
Lemma F_8d0f8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d0f8%Z I : word) = Some W_8d0f8.
Proof. vm_refl. Qed.
Lemma D_8d0f8 : decode_any W_8d0f8 = Some (Op ALU_ADD (@BV 5 5%Z I) (@BV 5 28%Z I) (@BV 5 5%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0fc : bv 32 := @BV 32 0x00e2c2b3%Z I.
Lemma F_8d0fc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d0fc%Z I : word) = Some W_8d0fc.
Proof. vm_refl. Qed.
Lemma D_8d0fc : decode_any W_8d0fc = Some (Op ALU_XOR (@BV 5 5%Z I) (@BV 5 5%Z I) (@BV 5 14%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d100 : bv 32 := @BV 32 0x0012b293%Z I.
Lemma F_8d100 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d100%Z I : word) = Some W_8d100.
Proof. vm_refl. Qed.
Lemma D_8d100 : decode_any W_8d100 = Some (OpImm ALU_SLTU (@BV 5 5%Z I) (@BV 5 5%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d104 : bv 32 := @BV 32 0x005302b3%Z I.
Lemma F_8d104 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d104%Z I : word) = Some W_8d104.
Proof. vm_refl. Qed.
Lemma D_8d104 : decode_any W_8d104 = Some (Op ALU_ADD (@BV 5 5%Z I) (@BV 5 6%Z I) (@BV 5 5%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d108 : bv 32 := @BV 32 0x0056b023%Z I.
Lemma F_8d108 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d108%Z I : word) = Some W_8d108.
Proof. vm_refl. Qed.
Lemma D_8d108 : decode_any W_8d108 = Some (Store SZ8 (@BV 5 13%Z I) (@BV 5 5%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d10c : bv 32 := @BV 32 0x00f5b42f%Z I.
Lemma F_8d10c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d10c%Z I : word) = Some W_8d10c.
Proof. vm_refl. Qed.
Lemma D_8d10c : decode_any W_8d10c = Some (Amo AMO_ADD AD false false (@BV 5 8%Z I) (@BV 5 11%Z I) (@BV 5 15%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d110 : bv 32 := @BV 32 0x01445293%Z I.
Lemma F_8d110 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d110%Z I : word) = Some W_8d110.
Proof. vm_refl. Qed.
Lemma D_8d110 : decode_any W_8d110 = Some (ShiftImm ALU_SRL (@BV 5 5%Z I) (@BV 5 8%Z I) (@BV 6 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d114 : bv 32 := @BV 32 0x00850333%Z I.
Lemma F_8d114 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d114%Z I : word) = Some W_8d114.
Proof. vm_refl. Qed.
Lemma D_8d114 : decode_any W_8d114 = Some (Op ALU_ADD (@BV 5 6%Z I) (@BV 5 10%Z I) (@BV 5 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d118 : bv 32 := @BV 32 0x01435313%Z I.
Lemma F_8d118 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d118%Z I : word) = Some W_8d118.
Proof. vm_refl. Qed.
Lemma D_8d118 : decode_any W_8d118 = Some (ShiftImm ALU_SRL (@BV 5 6%Z I) (@BV 5 6%Z I) (@BV 6 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d11c : bv 32 := @BV 32 0xf26284e3%Z I.
Lemma F_8d11c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d11c%Z I : word) = Some W_8d11c.
Proof. vm_refl. Qed.
Lemma D_8d11c : decode_any W_8d11c = Some (Branch BC_EQ (@BV 5 5%Z I) (@BV 5 6%Z I) (@BV 13 7976%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d124 : bv 32 := @BV 32 0x01060513%Z I.
Lemma F_8d124 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d124%Z I : word) = Some W_8d124.
Proof. vm_refl. Qed.
Lemma D_8d124 : decode_any W_8d124 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 12%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d128 : bv 32 := @BV 32 0x0d9000ef%Z I.
Lemma F_8d128 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d128%Z I : word) = Some W_8d128.
Proof. vm_refl. Qed.
Lemma D_8d128 : decode_any W_8d128 = Some (Jal (@BV 5 1%Z I) (@BV 21 2264%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d12c : bv 32 := @BV 32 0xf49ff06f%Z I.
Lemma F_8d12c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8d12c%Z I : word) = Some W_8d12c.
Proof. vm_refl. Qed.
Lemma D_8d12c : decode_any W_8d12c = Some (Jal (@BV 5 0%Z I) (@BV 21 2096968%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da00 : bv 32 := @BV 32 0xfe010113%Z I.
Lemma F_8da00 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da00%Z I : word) = Some W_8da00.
Proof. vm_refl. Qed.
Lemma D_8da00 : decode_any W_8da00 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4064%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da04 : bv 32 := @BV 32 0x00113c23%Z I.
Lemma F_8da04 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da04%Z I : word) = Some W_8da04.
Proof. vm_refl. Qed.
Lemma D_8da04 : decode_any W_8da04 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da08 : bv 32 := @BV 32 0x00813823%Z I.
Lemma F_8da08 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da08%Z I : word) = Some W_8da08.
Proof. vm_refl. Qed.
Lemma D_8da08 : decode_any W_8da08 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da0c : bv 32 := @BV 32 0x00913423%Z I.
Lemma F_8da0c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da0c%Z I : word) = Some W_8da0c.
Proof. vm_refl. Qed.
Lemma D_8da0c : decode_any W_8da0c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da10 : bv 32 := @BV 32 0x01213023%Z I.
Lemma F_8da10 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da10%Z I : word) = Some W_8da10.
Proof. vm_refl. Qed.
Lemma D_8da10 : decode_any W_8da10 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da14 : bv 32 := @BV 32 0x00050493%Z I.
Lemma F_8da14 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da14%Z I : word) = Some W_8da14.
Proof. vm_refl. Qed.
Lemma D_8da14 : decode_any W_8da14 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da18 : bv 32 := @BV 32 0x00c50413%Z I.
Lemma F_8da18 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da18%Z I : word) = Some W_8da18.
Proof. vm_refl. Qed.
Lemma D_8da18 : decode_any W_8da18 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 10%Z I) (@BV 12 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da1c : bv 32 := @BV 32 0x0ff00513%Z I.
Lemma F_8da1c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da1c%Z I : word) = Some W_8da1c.
Proof. vm_refl. Qed.
Lemma D_8da1c : decode_any W_8da1c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 255%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da20 : bv 32 := @BV 32 0xffc47613%Z I.
Lemma F_8da20 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da20%Z I : word) = Some W_8da20.
Proof. vm_refl. Qed.
Lemma D_8da20 : decode_any W_8da20 = Some (OpImm ALU_AND (@BV 5 12%Z I) (@BV 5 8%Z I) (@BV 12 4092%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da24 : bv 32 := @BV 32 0x00100693%Z I.
Lemma F_8da24 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da24%Z I : word) = Some W_8da24.
Proof. vm_refl. Qed.
Lemma D_8da24 : decode_any W_8da24 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da28 : bv 32 := @BV 32 0x1406272f%Z I.
Lemma F_8da28 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da28%Z I : word) = Some W_8da28.
Proof. vm_refl. Qed.
Lemma D_8da28 : decode_any W_8da28 = Some (Lr AW true false (@BV 5 14%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da2c : bv 32 := @BV 32 0x00068793%Z I.
Lemma F_8da2c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da2c%Z I : word) = Some W_8da2c.
Proof. vm_refl. Qed.
Lemma D_8da2c : decode_any W_8da2c = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da30 : bv 32 := @BV 32 0x00f747b3%Z I.
Lemma F_8da30 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da30%Z I : word) = Some W_8da30.
Proof. vm_refl. Qed.
Lemma D_8da30 : decode_any W_8da30 = Some (Op ALU_XOR (@BV 5 15%Z I) (@BV 5 14%Z I) (@BV 5 15%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da34 : bv 32 := @BV 32 0x00a7f7b3%Z I.
Lemma F_8da34 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da34%Z I : word) = Some W_8da34.
Proof. vm_refl. Qed.
Lemma D_8da34 : decode_any W_8da34 = Some (Op ALU_AND (@BV 5 15%Z I) (@BV 5 15%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da38 : bv 32 := @BV 32 0x00f747b3%Z I.
Lemma F_8da38 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da38%Z I : word) = Some W_8da38.
Proof. vm_refl. Qed.
Lemma D_8da38 : decode_any W_8da38 = Some (Op ALU_XOR (@BV 5 15%Z I) (@BV 5 14%Z I) (@BV 5 15%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da3c : bv 32 := @BV 32 0x18f627af%Z I.
Lemma F_8da3c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da3c%Z I : word) = Some W_8da3c.
Proof. vm_refl. Qed.
Lemma D_8da3c : decode_any W_8da3c = Some (Sc AW false false (@BV 5 15%Z I) (@BV 5 12%Z I) (@BV 5 15%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da40 : bv 32 := @BV 32 0xfe0794e3%Z I.
Lemma F_8da40 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da40%Z I : word) = Some W_8da40.
Proof. vm_refl. Qed.
Lemma D_8da40 : decode_any W_8da40 = Some (Branch BC_NE (@BV 5 15%Z I) (@BV 5 0%Z I) (@BV 13 8168%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da44 : bv 32 := @BV 32 0x0ff77513%Z I.
Lemma F_8da44 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da44%Z I : word) = Some W_8da44.
Proof. vm_refl. Qed.
Lemma D_8da44 : decode_any W_8da44 = Some (OpImm ALU_AND (@BV 5 10%Z I) (@BV 5 14%Z I) (@BV 12 255%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da48 : bv 32 := @BV 32 0x04051863%Z I.
Lemma F_8da48 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da48%Z I : word) = Some W_8da48.
Proof. vm_refl. Qed.
Lemma D_8da48 : decode_any W_8da48 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 80%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da4c : bv 32 := @BV 32 0x0004b503%Z I.
Lemma F_8da4c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da4c%Z I : word) = Some W_8da4c.
Proof. vm_refl. Qed.
Lemma D_8da4c : decode_any W_8da4c = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da50 : bv 32 := @BV 32 0x02051463%Z I.
Lemma F_8da50 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da50%Z I : word) = Some W_8da50.
Proof. vm_refl. Qed.
Lemma D_8da50 : decode_any W_8da50 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da54 : bv 32 := @BV 32 0x00858593%Z I.
Lemma F_8da54 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da54%Z I : word) = Some W_8da54.
Proof. vm_refl. Qed.
Lemma D_8da54 : decode_any W_8da54 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da58 : bv 32 := @BV 32 0x00800537%Z I.
Lemma F_8da58 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da58%Z I : word) = Some W_8da58.
Proof. vm_refl. Qed.
Lemma D_8da58 : decode_any W_8da58 = Some (Lui (@BV 5 10%Z I) (@BV 20 2048%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da5c : bv 32 := @BV 32 0x00a5b02f%Z I.
Lemma F_8da5c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da5c%Z I : word) = Some W_8da5c.
Proof. vm_refl. Qed.
Lemma D_8da5c : decode_any W_8da5c = Some (Amo AMO_ADD AD false false (@BV 5 0%Z I) (@BV 5 11%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da60 : bv 32 := @BV 32 0xfff94517%Z I.
Lemma F_8da60 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da60%Z I : word) = Some W_8da60.
Proof. vm_refl. Qed.
Lemma D_8da60 : decode_any W_8da60 = Some (Auipc (@BV 5 10%Z I) (@BV 20 1048468%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da64 : bv 32 := @BV 32 0x4e550593%Z I.
Lemma F_8da64 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da64%Z I : word) = Some W_8da64.
Proof. vm_refl. Qed.
Lemma D_8da64 : decode_any W_8da64 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 1253%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da68 : bv 32 := @BV 32 0x00800537%Z I.
Lemma F_8da68 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da68%Z I : word) = Some W_8da68.
Proof. vm_refl. Qed.
Lemma D_8da68 : decode_any W_8da68 = Some (Lui (@BV 5 10%Z I) (@BV 20 2048%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da6c : bv 32 := @BV 32 0xb44f50ef%Z I.
Lemma F_8da6c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da6c%Z I : word) = Some W_8da6c.
Proof. vm_refl. Qed.
Lemma D_8da6c : decode_any W_8da6c = Some (Jal (@BV 5 1%Z I) (@BV 21 2052932%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da70 : bv 32 := @BV 32 0x0310000f%Z I.
Lemma F_8da70 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da70%Z I : word) = Some W_8da70.
Proof. vm_refl. Qed.
Lemma D_8da70 : decode_any W_8da70 = Some (Fence (@BV 4 0%Z I) (@BV 4 3%Z I) (@BV 4 1%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da74 : bv 32 := @BV 32 0x00a4b023%Z I.
Lemma F_8da74 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da74%Z I : word) = Some W_8da74.
Proof. vm_refl. Qed.
Lemma D_8da74 : decode_any W_8da74 = Some (Store SZ8 (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da78 : bv 32 := @BV 32 0x0310000f%Z I.
Lemma F_8da78 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da78%Z I : word) = Some W_8da78.
Proof. vm_refl. Qed.
Lemma D_8da78 : decode_any W_8da78 = Some (Fence (@BV 4 0%Z I) (@BV 4 3%Z I) (@BV 4 1%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da7c : bv 32 := @BV 32 0x00040023%Z I.
Lemma F_8da7c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da7c%Z I : word) = Some W_8da7c.
Proof. vm_refl. Qed.
Lemma D_8da7c : decode_any W_8da7c = Some (Store SZ1 (@BV 5 8%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da80 : bv 32 := @BV 32 0x01813083%Z I.
Lemma F_8da80 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da80%Z I : word) = Some W_8da80.
Proof. vm_refl. Qed.
Lemma D_8da80 : decode_any W_8da80 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da84 : bv 32 := @BV 32 0x01013403%Z I.
Lemma F_8da84 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da84%Z I : word) = Some W_8da84.
Proof. vm_refl. Qed.
Lemma D_8da84 : decode_any W_8da84 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da88 : bv 32 := @BV 32 0x00813483%Z I.
Lemma F_8da88 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da88%Z I : word) = Some W_8da88.
Proof. vm_refl. Qed.
Lemma D_8da88 : decode_any W_8da88 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da8c : bv 32 := @BV 32 0x00013903%Z I.
Lemma F_8da8c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da8c%Z I : word) = Some W_8da8c.
Proof. vm_refl. Qed.
Lemma D_8da8c : decode_any W_8da8c = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da90 : bv 32 := @BV 32 0x02010113%Z I.
Lemma F_8da90 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da90%Z I : word) = Some W_8da90.
Proof. vm_refl. Qed.
Lemma D_8da90 : decode_any W_8da90 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8da94 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_8da94 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8da94%Z I : word) = Some W_8da94.
Proof. vm_refl. Qed.
Lemma D_8da94 : decode_any W_8da94 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_8cef4_8dab4.
Require Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Module BoAllocFBits.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation ZF n := (repeat (Z_to_bv 8 0) (Z.to_nat n)).

Open Scope Z_scope.
(* [comment removed for export] *)
Lemma bl2z_cons : forall (b : byte) bs, bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
  intros b bs. (lazymatch goal with |- ?G => let G' := eval cbn [bytes_le_to_Z] in G in change_no_check G' end). pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite <- Z.lxor_lor.
  - rewrite Z.add_nocarry_lxor; [reflexivity|].
    apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
  - apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Lemma lock_byte1 : forall (b0 b1 b2 b3 : byte) (v : word),
  bytes_le_to_Z [b0; b1; b2; b3] = bv_unsigned v ->
  v_andi (v_srlw (v_lw v) (Z_to_bv 64 8)) 255 = Z_to_bv 64 (bv_unsigned b1).
Proof.
  intros b0 b1 b2 b3 v Hv.
  pose proof (u8_range b0) as R0. pose proof (u8_range b1) as R1. pose proof (u8_range b2) as R2. pose proof (u8_range b3) as R3.
  pose proof (u64_range v) as Rv.
  rewrite !bl2z_cons in Hv. cbn [bytes_le_to_Z] in Hv.
  set (k := bv_unsigned b2 + bv_unsigned b3 * 256) in *.
  set (W := bv_unsigned v) in *.
  assert (HW : W = bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * k)) by lia.
  assert (Hk : 0 <= k < 2 ^ 16) by lia.
  (lazymatch goal with |- ?G => let G' := eval unfold v_andi, v_srlw, v_lw in G in change_no_check G' end). apply f_equal.
  (lazymatch goal with |- ?G => let G' := eval unfold bv_swrap, bv_wrap in G in change_no_check G' end). change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 64) with (2 ^ 64).
  rewrite (u_Z2bv 8) by lia. change (8 mod 32) with 8.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  fold W.
  rewrite !Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 64) with (2 ^ 64). change (255 mod 2 ^ 64) with 255.
  assert (E1 : ((W + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31) mod 2 ^ 64 mod 2 ^ 32 = W).
  { destruct (Z.lt_ge_cases W (2 ^ 31)) as [L|G].
    - rewrite (Z.mod_small (W + 2 ^ 31)) by lia. replace (W + 2 ^ 31 - 2 ^ 31) with W by lia.
      rewrite (Z.mod_small W) by lia. apply Z.mod_small. lia.
    - replace ((W + 2 ^ 31) mod 2 ^ 32) with (W + 2 ^ 31 - 2 ^ 32) by (Z.div_mod_to_equations; lia).
      replace ((W + 2 ^ 31 - 2 ^ 32 - 2 ^ 31) mod 2 ^ 64) with (2 ^ 64 - 2 ^ 32 + W) by (Z.div_mod_to_equations; lia).
      Z.div_mod_to_equations; lia. }
  rewrite E1. replace (W / 256) with (bv_unsigned b1 + 256 * k) by (Z.div_mod_to_equations; lia).
  rewrite (Z.mod_small (bv_unsigned b1 + 256 * k + 2 ^ 31)) by lia. replace (bv_unsigned b1 + 256 * k + 2 ^ 31 - 2 ^ 31) with (bv_unsigned b1 + 256 * k) by lia.
  rewrite (Z.mod_small (bv_unsigned b1 + 256 * k)) by lia.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
  Z.div_mod_to_equations. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma lock_byte1_00 : forall (b2 b3 : byte) (v : word),
  bytes_le_to_Z [Z_to_bv 8 0; Z_to_bv 8 0; b2; b3] = bv_unsigned v ->
  v_andi (v_srlw (v_lw v) (Z_to_bv 64 8)) 255 = Z_to_bv 64 0.
Proof.
  intros b2 b3 v Hv.
  pose proof (u8_range b2) as R2. pose proof (u8_range b3) as R3. pose proof (u64_range v) as Rv.
  rewrite !bl2z_cons in Hv. cbn [bytes_le_to_Z] in Hv.
  change (bv_unsigned (Z_to_bv 8 0)) with 0 in Hv.
  set (k := bv_unsigned b2 + bv_unsigned b3 * 256) in *.
  assert (HW : bv_unsigned v = k * 65536) by lia.
  assert (Hk : 0 <= k < 2 ^ 16) by lia.
  (lazymatch goal with |- ?G => let G' := eval unfold v_andi, v_srlw, v_lw in G in change_no_check G' end). apply f_equal.
  (lazymatch goal with |- ?G => let G' := eval unfold bv_swrap, bv_wrap in G in change_no_check G' end). change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 64) with (2 ^ 64).
  rewrite (u_Z2bv 8) by lia. change (8 mod 32) with 8.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  rewrite HW.
  (* [comment removed for export] *)
  rewrite !Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 64) with (2 ^ 64). change (255 mod 2 ^ 64) with 255.
  assert (E1 : ((k * 65536 + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31) mod 2 ^ 64 mod 2 ^ 32 = k * 65536).
  { destruct (Z.lt_ge_cases (k * 65536) (2 ^ 31)) as [L|G].
    - rewrite (Z.mod_small (k * 65536 + 2 ^ 31)) by lia. replace (k * 65536 + 2 ^ 31 - 2 ^ 31) with (k * 65536) by lia.
      rewrite (Z.mod_small (k * 65536)) by lia. apply Z.mod_small. lia.
    - replace ((k * 65536 + 2 ^ 31) mod 2 ^ 32) with (k * 65536 + 2 ^ 31 - 2 ^ 32) by (Z.div_mod_to_equations; lia).
      replace ((k * 65536 + 2 ^ 31 - 2 ^ 32 - 2 ^ 31) mod 2 ^ 64) with (2 ^ 64 - 2 ^ 32 + k * 65536) by (Z.div_mod_to_equations; lia).
      Z.div_mod_to_equations; lia. }
  rewrite E1. replace (k * 65536 / 256) with (k * 256) by (Z.div_mod_to_equations; lia).
  rewrite (Z.mod_small (k * 256 + 2 ^ 31)) by lia. replace (k * 256 + 2 ^ 31 - 2 ^ 31) with (k * 256) by lia.
  rewrite (Z.mod_small (k * 256)) by lia.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
  rewrite Z.mod_mul. reflexivity. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma rdn1_top : forall (m : word -> option byte) (a : word) (b : byte) bs,
  bv_unsigned a + Z.of_nat (length (b :: bs)) <= 2 ^ 64 ->
  rdn BSEGS (wbytes m a (b :: bs)) a 1 = Some [b].
Proof.
  intros m a b bs Hnw. (lazymatch goal with |- ?G => let G' := eval cbn [rdn] in G in change_no_check G' end). rewrite (wbytes_inside (b :: bs) m a a Hnw) by (cbn [length] in Hnw |- *; lia).
  rewrite Z.sub_diag. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rdn8_in_fill : forall (m : word -> option byte) (a : word) (n k : Z),
  (0 <= k)%Z -> (k + 8 <= n)%Z -> (bv_unsigned a + n < 2 ^ 64)%Z ->
  rdn BSEGS (wbytes m a (ZF n)) (Z_to_bv 64 (bv_unsigned a + k)) 8 = Some (LE8 (Z_to_bv 64 0)).
Proof.
  intros m a n k Hk Hkn Hnw. pose proof (u64_range a) as Ha.
  transitivity (rdn BSEGS (wbytes m (Z_to_bv 64 (bv_unsigned a + k)) (ZF 8)) (Z_to_bv 64 (bv_unsigned a + k)) 8).
  - apply rdn_ext; [unorm; change (Z.of_nat 8) with 8%Z; lia|]. intros x Hx. revert Hx; unorm; change (Z.of_nat 8) with 8%Z; intros Hx.
    rewrite (wbytes_inside (ZF n) m a x) by (rewrite repeat_length; rewrite Z2Nat.id by lia; lia).
    rewrite (wbytes_inside (ZF 8) m (Z_to_bv 64 (bv_unsigned a + k)) x).
    2:{ rewrite repeat_length. unorm. change (Z.of_nat (Z.to_nat 8)) with 8%Z. lia. }
    2:{ rewrite repeat_length. unorm. change (Z.of_nat (Z.to_nat 8)) with 8%Z. lia. }
    rewrite !nth_repeat. reflexivity.
  - change (LE8 (Z_to_bv 64 0)) with (ZF 8). replace 8%nat with (length (ZF 8)) at 3 by reflexivity.
    apply (rdn_wbytes_hit BSEGS (ZF 8)). rewrite repeat_length. unorm. change (Z.of_nat (Z.to_nat 8)) with 8%Z. lia.
Qed.
End BoAllocFBits.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRc3c.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac BoAllocFBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM1.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Ltac famo F D bbs vv Hr Hv :=
  chain_step; [reflexivity
    | eapply step_amoadd_d with (bs := bbs) (v := vv);
      [exact F | reflexivity | exact D
      | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia
      | rd_addr Hr | exact Hv | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; first [stk_ok | hyp_ok] ]
    | step_simpl]; vn.

(* [comment removed for export] *)
Definition fr_k5 (mem : word -> option byte) (S ra0 s0v s1v s2v s3v s4v : word) (T c cnt e : Z) (stw : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2408)) (LE8 ra0))
    (at_ S (-2416)) (LE8 s0v))
    (at_ S (-2424)) (LE8 s1v))
    (at_ S (-2432)) (LE8 s2v))
    (at_ S (-2440)) (LE8 s3v))
    (at_ S (-2448)) (LE8 s4v))
    (Z_to_bv 64 (T + 208 + 80 * c)) (LE4 (cnt + 1)))
    (Z_to_bv 64 (T + 208 + 80 * c + 16 + 4 * cnt)) (LE4 (e / 16)))
    (Z_to_bv 64 (T + 2784)) (LE8 stw).
#[local] Hint Unfold fr_k5 : asfr.

Section K5.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v s3v s4v : word) (T spb c e cnt mx : Z) (bst bcs : list byte).
  Variable regs : bvmap 5 word.
  #[local] Abbreviation pc_ := (T + 208 + 80 * c)%Z.
  Hypothesis H1 : getr regs 1 = ra0.
  Hypothesis H2 : getr regs 2 = at_ S (-2400).
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 (T + 208).
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 0x10ab58.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 c.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 (spb + c * 2 ^ 32 + e).
  Hypothesis H8 : getr regs 8 = s0v.   Hypothesis H9 : getr regs 9 = s1v.   Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v. Hypothesis H20 : getr regs 20 = s4v.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis HT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= bv_unsigned S - 3584) /\ T mod 16 = 0)%Z.
  Hypothesis Hspb : (0 <= spb /\ spb + 2 ^ 37 < 2 ^ 47)%Z.
  Hypothesis Hc : (1 <= c <= 30)%Z.
  Hypothesis He : (0 <= e < 2 ^ 32)%Z.
  Hypothesis Hcnt : (0 <= cnt < mx /\ mx <= 16)%Z.                             (* [comment removed for export] *)
  Hypothesis Hret : ret_ok ra0.
  Hypothesis Lbst : length bst = 8%nat.
  Hypothesis Lbcs : length bcs = 8%nat.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2448)) 48 = true.
  Hypothesis HokT : store_ok BSEGS mem (Z_to_bv 64 T) (Z.to_nat 4096) = true.
  Hypothesis Rmx : rdn BSEGS mem (Z_to_bv 64 (pc_ + 4)) 4 = Some (LE4 mx).
  Hypothesis Rcnt : rdn BSEGS mem (Z_to_bv 64 pc_) 4 = Some (LE4 cnt).
  Hypothesis Rcs : rdn BSEGS mem (Z_to_bv 64 (pc_ + 8)) 8 = Some bcs.
  Hypothesis Rst : rdn BSEGS mem (Z_to_bv 64 (T + 2784)) 8 = Some bst.
  Hypothesis Rspb : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 spb)).

  #[local] Abbreviation stw := (v_add (Z_to_bv 64 (bytes_le_to_Z bst)) (v_sub (Z_to_bv 64 0) (Z_to_bv 64 (bytes_le_to_Z bcs)))).

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma k5_facts : (cnt * 2 ^ 32 / 2 ^ 30 = 4 * cnt /\ (T + 2784) mod 8 = 0)%Z.
  Proof using Lbcs Lbst He HT bcs bst e s4v S rom. destruct HT as (_ & _ & T16). split; [| lia]. replace (cnt * 2 ^ 32)%Z with (4 * cnt * 2 ^ 30)%Z by lia. rewrite Z.div_mul by lia. reflexivity. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Lemma k5_run :
    exists r, msteps BSEGS (mkst regs (0x4eca8 : word) mem rom) (mkst r ra0 (fr_k5 mem S ra0 s0v s1v s2v s3v s4v T c cnt e stw) rom)
      /\ getr r 2 = at_ S (-2400) /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24
      /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Rspb Rst Rcs Rcnt Rmx HokT Hstk Lbcs Lbst Hret Hcnt He Hc Hspb HT HS H20 H19 H18 H9 H8 H13 H12 H11 H10 H2 H1 mx spb.
    pose proof (u64_range S) as HSr. destruct HT as (HT1 & HT2 & HT16). unfold hideW in HT2. destruct k5_facts as [Hc4 Hal8].
    pose proof (bytes_le_to_Z_bound bst) as Bst. rewrite Lbst in Bst. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bst.
    pose proof (bytes_le_to_Z_bound bcs) as Bcs. rewrite Lbcs in Bcs. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bcs.
    pose proof (bytes_le_to_Z_nonneg bst) as Bst'. pose proof (bytes_le_to_Z_nonneg bcs) as Bcs'.
    assert (Vst : bytes_le_to_Z bst = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bst))) by (rewrite u_Z2bv by lia; reflexivity).
    assert (Vcs : bytes_le_to_Z bcs = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bcs))) by (rewrite u_Z2bv by lia; reflexivity).
    assert (Vcnt : bytes_le_to_Z (LE4 cnt) = bv_unsigned (Z_to_bv 64 cnt)) by (apply bytes4_small; lia).
    assert (Vmx : bytes_le_to_Z (LE4 mx) = bv_unsigned (Z_to_bv 64 mx)) by (apply bytes4_small; lia).
    wd_eexists. split.
    - an F_4eca8 D_4eca8.                              (* [comment removed for export] *)
      fsd F_4ecac D_4ecac (at_ S (-2408)).             (* [comment removed for export] *)
      fsd F_4ecb0 D_4ecb0 (at_ S (-2416)).
      fsd F_4ecb4 D_4ecb4 (at_ S (-2424)).
      fsd F_4ecb8 D_4ecb8 (at_ S (-2432)).
      fsd F_4ecbc D_4ecbc (at_ S (-2440)).
      fsd F_4ecc0 D_4ecc0 (at_ S (-2448)).
      ab_ft F_4ecc4 D_4ecc4 ltac:(condz).              (* [comment removed for export] *)
      an F_4ecc8 D_4ecc8.                              (* [comment removed for export] *)
      ab_ft F_4eccc D_4eccc ltac:(condz).              (* [comment removed for export] *)
      an F_4ecd0 D_4ecd0.                              (* [comment removed for export] *)
      av F_4ecd4 D_4ecd4 (Z_to_bv 64 (80 * c)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_mul in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      av F_4ecd8 D_4ecd8 (Z_to_bv 64 pc_) ltac:(valz).  (* [comment removed for export] *)
      clw F_4ecdc D_4ecdc (LE4 mx) (Z_to_bv 64 mx) Rmx Vmx.       (* [comment removed for export] *)
      rewrite (v_lw_small mx) by lia.
      ab_ft F_4ece0 D_4ece0 ltac:(condz).              (* [comment removed for export] *)
      clw F_4ece4 D_4ece4 (LE4 cnt) (Z_to_bv 64 cnt) Rcnt Vcnt.   (* [comment removed for export] *)
      rewrite (v_lw_small cnt) by lia.
      ab_ft F_4ece8 D_4ece8 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4ecec D_4ecec (Z_to_bv 64 spb) Rspb.      (* [comment removed for export] *)
      av F_4ecf0 D_4ecf0 (Z_to_bv 64 (c * 2 ^ 32)) ltac:(apply cls_shl32; lia).   (* [comment removed for export] *)
      av F_4ecf4 D_4ecf4 (Z_to_bv 64 (spb + e)) ltac:(valz).      (* [comment removed for export] *)
      av F_4ecf8 D_4ecf8 (Z_to_bv 64 (cnt * 2 ^ 32)) ltac:(valz). (* [comment removed for export] *)
      av F_4ecfc D_4ecfc (Z_to_bv 64 (cnt + 1)) ltac:(valz).      (* [comment removed for export] *)
      av F_4ed00 D_4ed00 (Z_to_bv 64 e) ltac:(valz).   (* [comment removed for export] *)
      cld F_4ed04 D_4ed04 bcs (Z_to_bv 64 (bytes_le_to_Z bcs)) Rcs Vcs.   (* [comment removed for export] *)
      an F_4ed08 D_4ed08.                              (* [comment removed for export] *)
      av F_4ed0c D_4ed0c (Z_to_bv 64 (4 * cnt)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; unorm; rewrite <- Hc4; unorm; reflexivity).   (* [comment removed for export] *)
      av F_4ed10 D_4ed10 (Z_to_bv 64 (T + 2784)) ltac:(valz).     (* [comment removed for export] *)
      av F_4ed14 D_4ed14 (Z_to_bv 64 (pc_ + 4 * cnt)) ltac:(valz).   (* [comment removed for export] *)
      av F_4ed18 D_4ed18 (Z_to_bv 64 (e / 16)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; unorm; reflexivity).   (* [comment removed for export] *)
      fsw F_4ed1c D_4ed1c (Z_to_bv 64 pc_).            (* [comment removed for export] *)
      fsw F_4ed20 D_4ed20 (Z_to_bv 64 (pc_ + 16 + 4 * cnt)).   (* [comment removed for export] *)
      an F_4ed24 D_4ed24.                              (* [comment removed for export] *)
      famo F_4ed28 D_4ed28 bst (Z_to_bv 64 (bytes_le_to_Z bst)) Rst Vst.   (* [comment removed for export] *)
      fld F_4ed2c D_4ed2c ra0. fld F_4ed30 D_4ed30 s0v. fld F_4ed34 D_4ed34 s1v. fld F_4ed38 D_4ed38 s2v.
      fld F_4ed3c D_4ed3c s3v. fld F_4ed40 D_4ed40 s4v.
      an F_4ed44 D_4ed44.                              (* [comment removed for export] *)
      aret F_4ed48 D_4ed48 ra0.                        (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_k5 mem S ra0 s0v s1v s2v s3v s4v T c cnt e stw). wd_refl.
    - post.
  Qed.
End K5.
End FPGen.
End BoAllocFRc3c.
Module BoAllocFRcS1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac BoAllocFBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM1.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

(* [comment removed for export] *)
Fixpoint gbb_scan (p : Z) (l : list Z) (acc : Z) : Z :=
  match l with
  | [] => acc
  | h :: r => gbb_scan p r (if ((h <=? p) && (acc <? h))%bool then h else acc)
  end.

Section FPGen.
Context {fx : FPState}.

Ltac regneq := apply reg_neq_of_eqb; reflexivity.
Ltac pc4 := apply bv_eq; reflexivity.
(* [comment removed for export] *)
Ltac fsb F D aa bb :=
  chain_step; [reflexivity
    | eapply MmapSim.step_sb_at with (a := aa) (b := bb);
      [exact F | reflexivity | exact D
      | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; first [reflexivity | f_equal; lia | apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_addi, at_ in G in change_no_check G' end); wd_ulia]
      | gres; rwH; reflexivity
      | first [reflexivity | apply bv_eq; unorm; reflexivity]
      | first [stk_ok | hyp_ok] ]
    | step_simpl]; vn.

Lemma sok_seclock : forall m, store_ok BSEGS m (Z_to_bv 64 0x10ae00) 4 = true.
Proof using. intros m. apply store_ok_wseg. vm_compute. reflexivity. Qed.

Lemma v_andi_255_andS : forall x : word, v_andi x 255 = v_and x (Z_to_bv 64 255).
Proof using.
  intros x. pose proof (u64_range x). rewrite <- (Z_to_bv_bv_unsigned 64 x) at 1. rewrite v_andi_Z by lia.
  rewrite <- (Z_to_bv_bv_unsigned 64 x) at 2. rewrite v_and_Z by lia. reflexivity.
Qed.
Lemma lock_byte0S : forall (b0 b1 b2 b3 : byte) (v : word),
  bytes_le_to_Z [b0; b1; b2; b3] = bv_unsigned v -> v_andi (v_lw v) 255 = Z_to_bv 64 (bv_unsigned b0).
Proof using.
  intros b0 b1 b2 b3 v Hv. rewrite v_andi_255_andS.
  rewrite (and_mask_byte [b0; b1; b2; b3] v (Z_to_bv 64 255) 0 eq_refl Hv ltac:(lia) ltac:(reflexivity)).
  (lazymatch goal with |- ?G => let G' := eval cbn [nth Z.of_nat Z.mul] in G in change_no_check G' end). rewrite Z.mul_1_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma gbb_lock_4eb4c : forall regs mem rom (v : word) b0 b1 b2 b3,
  getr regs 13 = Z_to_bv 64 0x10ae00 -> getr regs 12 = Z_to_bv 64 255 -> getr regs 14 = Z_to_bv 64 1 ->
  rdn BSEGS mem (Z_to_bv 64 0x10ae00) 4%nat = Some [b0; b1; b2; b3] -> bytes_le_to_Z [b0; b1; b2; b3] = bv_unsigned v ->
  msteps BSEGS (mkst regs (0x4eb4c : word) mem rom)
    (mkst (regupd (regupd regs 15 (v_lw v)) 16 (Z_to_bv 64 0)) (0x4eb68 : word)
          (wbytes mem (Z_to_bv 64 0x10ae00) [Z_to_bv 8 1; b1; b2; b3]) rom).
Proof using.
  intros regs mem rom v b0 b1 b2 b3 H13 H12 H14 Hrd Hv.
  pose proof (xchg_byte_run BSEGS regs (0x4eb4c : word) (0x4eb50 : word) (0x4eb54 : word) (0x4eb58 : word)
                (0x4eb5c : word) (0x4eb60 : word) (0x4eb64 : word) (0x4eb68 : word) mem rom
                _ _ _ _ _ _ _ _ _ _ _ 15 13 16 14 12 _ [b0; b1; b2; b3] v 0%nat 1%Z
                F_4eb4c eq_refl D_4eb4c F_4eb50 eq_refl D_4eb50 F_4eb54 eq_refl D_4eb54 F_4eb58 eq_refl D_4eb58
                F_4eb5c eq_refl D_4eb5c F_4eb60 eq_refl D_4eb60 F_4eb64 eq_refl D_4eb64) as R.
  rewrite H13, H12, H14 in R. cbn [firstn skipn app] in R.
  apply R; clear R; first [regneq | pc4 | apply sok_seclock | unorm; reflexivity | lia | assumption].
Qed.

(* [comment removed for export] *)
Definition fr_gbb0 (mem : word -> option byte) (S ra0 s0v s1v s2v : word) (b1 b2 b3 : byte) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2456)) (LE8 ra0))
    (at_ S (-2464)) (LE8 s0v))
    (at_ S (-2472)) (LE8 s1v))
    (at_ S (-2480)) (LE8 s2v))
    (Z_to_bv 64 0x10ae00) [Z_to_bv 8 1; b1; b2; b3].
#[local] Hint Unfold fr_gbb0 : asfr.

(* [comment removed for export] *)
Definition gbb_keep (r r' : bvmap 5 word) : Prop :=
  getr r' 1 = getr r 1 /\ getr r' 2 = getr r 2 /\ getr r' 3 = getr r 3 /\ getr r' 4 = getr r 4 /\ getr r' 8 = getr r 8 /\ getr r' 9 = getr r 9
  /\ getr r' 10 = getr r 10 /\ getr r' 11 = getr r 11 /\ getr r' 14 = getr r 14
  /\ getr r' 18 = getr r 18 /\ getr r' 19 = getr r 19 /\ getr r' 20 = getr r 20 /\ getr r' 21 = getr r 21
  /\ getr r' 22 = getr r 22 /\ getr r' 23 = getr r 23 /\ getr r' 24 = getr r 24 /\ getr r' 25 = getr r 25 /\ getr r' 26 = getr r 26 /\ getr r' 27 = getr r 27.

Section GBB1.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v v : word) (b1 b2 b3 : byte) (len ptr : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra0.
  Hypothesis H2 : getr regs 2 = at_ S (-2448).
  Hypothesis H8 : getr regs 8 = s0v.
  Hypothesis H9 : getr regs 9 = s1v.
  Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x10ab98.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47 + 256)%Z.
  Hypothesis Hlen : (1 <= len <= 2 ^ 20)%Z.
  Hypothesis Hptr : (0 <= ptr /\ ptr + 8 * len < 2 ^ 47)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2480)) 32 = true.
  Hypothesis Rlock : rdn BSEGS mem (Z_to_bv 64 0x10ae00) 4 = Some [Z_to_bv 8 0; b1; b2; b3].
  Hypothesis HV : bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3] = bv_unsigned v.
  Hypothesis Rn : rdn BSEGS mem (Z_to_bv 64 (0x10ab98 + 56)) 8 = Some (LE8 (Z_to_bv 64 len)).
  Hypothesis Rptr : rdn BSEGS mem (Z_to_bv 64 (0x10ab98 + 8)) 8 = Some (LE8 (Z_to_bv 64 ptr)).

  Lemma gbb_head :
    exists r, msteps BSEGS (mkst regs (0x4eb28 : word) mem rom) (mkst r (0x4eb94 : word) (fr_gbb0 mem S ra0 s0v s1v s2v b1 b2 b3) rom)
      /\ getr r 2 = at_ S (-2480) /\ getr r 8 = Z_to_bv 64 0x10ae00 /\ getr r 10 = Z_to_bv 64 0x10ab98 /\ getr r 11 = getr regs 11
      /\ getr r 12 = Z_to_bv 64 ptr /\ getr r 13 = Z_to_bv 64 0 /\ getr r 14 = Z_to_bv 64 (ptr + 8 * len)
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Rptr Rn HV Rlock Hstk Hptr Hlen HS H10 H18 H9 H8 H2 H1 v.
    pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - an F_4eb28 D_4eb28.                              (* [comment removed for export] *)
      fsd F_4eb2c D_4eb2c (at_ S (-2456)).             (* [comment removed for export] *)
      fsd F_4eb30 D_4eb30 (at_ S (-2464)).             (* [comment removed for export] *)
      fsd F_4eb34 D_4eb34 (at_ S (-2472)).             (* [comment removed for export] *)
      fsd F_4eb38 D_4eb38 (at_ S (-2480)).             (* [comment removed for export] *)
      an F_4eb3c D_4eb3c.                              (* [comment removed for export] *)
      an F_4eb40 D_4eb40.                              (* [comment removed for export] *)
      an F_4eb44 D_4eb44.                              (* [comment removed for export] *)
      an F_4eb48 D_4eb48.                              (* [comment removed for export] *)
      eapply msteps_trans.
      { eapply (gbb_lock_4eb4c _ _ rom v (Z_to_bv 8 0) b1 b2 b3);
          [ gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | rd_addr Rlock
          | exact HV ]. }
      av F_4eb68 D_4eb68 (Z_to_bv 64 0) ltac:(rewrite (lock_byte0S (Z_to_bv 8 0) b1 b2 b3 _ HV); unorm; reflexivity).   (* [comment removed for export] *)
      ab_ft F_4eb6c D_4eb6c ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4eb70 D_4eb70 (Z_to_bv 64 len) Rn.        (* [comment removed for export] *)
      ab_ft F_4eb74 D_4eb74 ltac:(condz).              (* [comment removed for export] *)
      an F_4eb78 D_4eb78.                              (* [comment removed for export] *)
      cld8 F_4eb7c D_4eb7c (Z_to_bv 64 ptr) Rptr.      (* [comment removed for export] *)
      av F_4eb80 D_4eb80 (Z_to_bv 64 (8 * len)) ltac:(valz).          (* [comment removed for export] *)
      av F_4eb84 D_4eb84 (Z_to_bv 64 (ptr + 8 * len)) ltac:(valz).    (* [comment removed for export] *)
      an F_4eb88 D_4eb88.                              (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_gbb0 mem S ra0 s0v s1v s2v b1 b2 b3). wd_refl.
    - post.
  Qed.
End GBB1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma v_sub_modS : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 ((a - b) mod 2 ^ 64).
Proof using.
  intros a b Ha Hb. apply bv_eq. (lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end). rewrite !Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite (Z.mod_small a), (Z.mod_small b) by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma sub_mod_neg : forall p h, (0 <= p < h)%Z -> (h < 2 ^ 64)%Z -> ((p - h) mod 2 ^ 64 = p - h + 2 ^ 64)%Z.
Proof using. intros p h H1 H2. symmetry. apply (Z.mod_unique (p - h) (2 ^ 64) (-1) (p - h + 2 ^ 64)); lia. Qed.

(* [comment removed for export] *)
Lemma gbb_body : forall (regs : bvmap 5 word) (mem rom : word -> option byte) (p a acc h : Z),
  getr regs 12 = Z_to_bv 64 a -> getr regs 13 = Z_to_bv 64 acc -> getr regs 11 = Z_to_bv 64 p ->
  (0 <= acc <= p)%Z -> (p < 2 ^ 63)%Z -> (0 <= h < 2 ^ 63)%Z -> (0 <= a /\ a + 8 < 2 ^ 63)%Z ->
  rdn BSEGS mem (Z_to_bv 64 a) 8 = Some (LE8 (Z_to_bv 64 h)) ->
  exists r, msteps BSEGS (mkst regs (0x4eb94 : word) mem rom) (mkst r (0x4eb90 : word) mem rom)
    /\ gbb_keep regs r /\ getr r 12 = Z_to_bv 64 (a + 8)
    /\ getr r 13 = Z_to_bv 64 (if ((h <=? p) && (acc <? h))%bool then h else acc).
Proof using.
  intros regs mem rom p a acc h H12 H13 H11 Hacc Hp Hh Ha C0.
  destruct (Z_le_gt_dec h p) as [LE | GT].
  - destruct (Z_lt_le_dec acc h) as [LT | GE].
    + (* [comment removed for export] *)
      replace ((h <=? p) && (acc <? h))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      wd_eexists. split; [|split].
      * cld8 F_4eb94 D_4eb94 (Z_to_bv 64 h) C0.      (* [comment removed for export] *)
        av F_4eb98 D_4eb98 (Z_to_bv 64 (p - h)) ltac:(valz).      (* [comment removed for export] *)
        av F_4eb9c D_4eb9c (Z_to_bv 64 (p - acc)) ltac:(valz).    (* [comment removed for export] *)
        an F_4eba0 D_4eba0.                            (* [comment removed for export] *)
        ab_tk F_4eba4 D_4eba4 ltac:(condz).            (* [comment removed for export] *)
        ab_ft F_4ebb4 D_4ebb4 ltac:(condz).            (* [comment removed for export] *)
        an F_4ebb8 D_4ebb8.                            (* [comment removed for export] *)
        an F_4ebbc D_4ebbc.                            (* [comment removed for export] *)
        av F_4eb8c D_4eb8c (Z_to_bv 64 (a + 8)) ltac:(valz).   (* [comment removed for export] *)
        wd_refl.
      * (lazymatch goal with |- ?G => let G' := eval unfold gbb_keep in G in change_no_check G' end). post.
      * post.
    + (* [comment removed for export] *)
      replace ((h <=? p) && (acc <? h))%bool with false by (symmetry; apply andb_false_intro2; apply Z.ltb_ge; lia).
      wd_eexists. split; [|split].
      * cld8 F_4eb94 D_4eb94 (Z_to_bv 64 h) C0.
        av F_4eb98 D_4eb98 (Z_to_bv 64 (p - h)) ltac:(valz).
        av F_4eb9c D_4eb9c (Z_to_bv 64 (p - acc)) ltac:(valz).
        an F_4eba0 D_4eba0.
        ab_ft F_4eba4 D_4eba4 ltac:(condz).            (* [comment removed for export] *)
        an F_4eba8 D_4eba8.                            (* [comment removed for export] *)
        ab_ft F_4ebac D_4ebac ltac:(condz).            (* [comment removed for export] *)
        an F_4ebb0 D_4ebb0.                            (* [comment removed for export] *)
        an F_4ebb8 D_4ebb8.                            (* [comment removed for export] *)
        an F_4ebbc D_4ebbc.                            (* [comment removed for export] *)
        av F_4eb8c D_4eb8c (Z_to_bv 64 (a + 8)) ltac:(valz).
        wd_refl.
      * (lazymatch goal with |- ?G => let G' := eval unfold gbb_keep in G in change_no_check G' end). post.
      * post.
  - (* [comment removed for export] *)
    replace ((h <=? p) && (acc <? h))%bool with false by (symmetry; apply andb_false_intro1; apply Z.leb_gt; lia).
    wd_eexists. split; [|split].
    * cld8 F_4eb94 D_4eb94 (Z_to_bv 64 h) C0.
      av F_4eb98 D_4eb98 (Z_to_bv 64 (p - h + 2 ^ 64)) ltac:(rewrite v_sub_modS by lia; rewrite sub_mod_neg by lia; reflexivity).
      av F_4eb9c D_4eb9c (Z_to_bv 64 (p - acc)) ltac:(valz).
      an F_4eba0 D_4eba0.
      ab_ft F_4eba4 D_4eba4 ltac:(condz).              (* [comment removed for export] *)
      an F_4eba8 D_4eba8.                              (* [comment removed for export] *)
      ab_tk F_4ebac D_4ebac ltac:(condz).              (* [comment removed for export] *)
      av F_4eb8c D_4eb8c (Z_to_bv 64 (a + 8)) ltac:(valz).
      wd_refl.
    * (lazymatch goal with |- ?G => let G' := eval unfold gbb_keep in G in change_no_check G' end). post.
    * post.
Qed.

Lemma gbb_loop : forall (l : list Z) (regs : bvmap 5 word) (mem rom : word -> option byte) (p a acc : Z),
  l <> [] -> getr regs 12 = Z_to_bv 64 a -> getr regs 13 = Z_to_bv 64 acc -> getr regs 11 = Z_to_bv 64 p ->
  getr regs 14 = Z_to_bv 64 (a + 8 * Z.of_nat (length l)) ->
  (0 <= acc <= p)%Z -> (p < 2 ^ 63)%Z -> Forall (fun h => (0 <= h < 2 ^ 63)%Z) l -> (0 <= a /\ a + 8 * Z.of_nat (length l) < 2 ^ 63)%Z ->
  (forall i h, nth_error l i = Some h -> rdn BSEGS mem (Z_to_bv 64 (a + 8 * Z.of_nat i)) 8 = Some (LE8 (Z_to_bv 64 h))) ->
  exists r, msteps BSEGS (mkst regs (0x4eb94 : word) mem rom) (mkst r (0x4ebc0 : word) mem rom)
    /\ gbb_keep regs r /\ getr r 13 = Z_to_bv 64 (gbb_scan p l acc).
Proof using.
  induction l as [|h l IH]; intros regs mem rom p a acc NE H12 H13 H11 H14 Hacc Hp Hl Ha Hcells; [exfalso; exact (NE eq_refl)|].
  apply Forall_cons_iff in Hl as [Hh Hl]. cbn [length] in *.
  pose proof (Hcells 0%nat h eq_refl) as C0. replace (a + 8 * Z.of_nat 0)%Z with a in C0 by lia.
  destruct (gbb_body regs mem rom p a acc h H12 H13 H11 Hacc Hp Hh ltac:(lia) C0) as (r1 & RUN1 & KP1 & E12 & E13).
  set (acc' := if ((h <=? p) && (acc <? h))%bool then h else acc) in *.
  assert (Hacc' : (0 <= acc' <= p)%Z).
  { (lazymatch goal with |- ?G => let G' := eval unfold acc' in G in change_no_check G' end). destruct ((h <=? p) && (acc <? h))%bool eqn:EB; [|exact Hacc].
    apply andb_prop in EB as [EB1 EB2]. apply Z.leb_le in EB1. lia. }
  pose proof KP1 as (K1 & K2 & K3 & K4 & K8 & K9 & K10 & K11 & K14 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  destruct l as [|h' l'].
  - (* [comment removed for export] *)
    cbn [length] in *. (lazymatch goal with |- ?G => let G' := eval cbn [gbb_scan] in G in change_no_check G' end). fold acc'.
    assert (X : exists r2, msteps BSEGS (mkst r1 (0x4eb90 : word) mem rom) (mkst r2 (0x4ebc0 : word) mem rom) /\ r2 = r1).
    { wd_eexists. split; [| reflexivity].
      ab_tk F_4eb90 D_4eb90 ltac:(condz).   (* [comment removed for export] *)
      wd_refl. }
    destruct X as (r2 & RUN2 & ->).
    exists r1. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|]. split; [exact KP1 | exact E13].
  - cbn [length] in *.
    assert (X : exists r2, msteps BSEGS (mkst r1 (0x4eb90 : word) mem rom) (mkst r2 (0x4eb94 : word) mem rom) /\ r2 = r1).
    { wd_eexists. split; [| reflexivity].
      ab_ft F_4eb90 D_4eb90 ltac:(condz).   (* [comment removed for export] *)
      wd_refl. }
    destruct X as (r2 & RUN2 & ->).
    destruct (IH r1 mem rom p (a + 8)%Z acc' ltac:(discriminate) E12 E13 ltac:(rewrite K11; exact H11)) as (r3 & RUN3 & KP3 & E3).
    + rewrite K14, H14. f_equal. (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). lia.
    + exact Hacc'.
    + exact Hp.
    + exact Hl.
    + (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). lia.
    + intros i hi Hi. replace (a + 8 + 8 * Z.of_nat i)%Z with (a + 8 * Z.of_nat (Datatypes.S i))%Z by lia. exact (Hcells (Datatypes.S i) hi Hi).
    + exists r3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]]|].
      split; [| (lazymatch goal with |- ?G => let G' := eval cbn [gbb_scan] in G in change_no_check G' end); fold acc'; exact E3].
      destruct KP3 as (L1 & L2 & L3 & L4 & L8 & L9 & L10 & L11 & L14 & L18 & L19 & L20 & L21 & L22 & L23 & L24 & L25 & L26 & L27).
      (lazymatch goal with |- ?G => let G' := eval unfold gbb_keep in G in change_no_check G' end). repeat split; etransitivity; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fr_gbb1 (mem : word -> option byte) : word -> option byte := wbytes mem (Z_to_bv 64 0x10ae00) [Z_to_bv 8 0].
#[local] Hint Unfold fr_gbb1 : asfr.

Section GBB3.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v : word) (p h msz : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ S (-2480).
  Hypothesis H8 : getr regs 8 = Z_to_bv 64 0x10ae00.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x10ab98.
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 p.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 h.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47 + 256)%Z.
  Hypothesis Hh : (AIMGHI <= h /\ h mod 4096 = 0 /\ 4096 <= msz /\ h + msz <= bv_unsigned S - 3584 /\ h <= p < h + msz)%Z.
  Hypothesis Hret : ret_ok ra0.
  Hypothesis Rmb : rdn BSEGS mem (Z_to_bv 64 h) 8 = Some (LE8 (Z_to_bv 64 h)).
  Hypothesis Rms : rdn BSEGS mem (Z_to_bv 64 (h + 8)) 8 = Some (LE8 (Z_to_bv 64 msz)).
  Hypothesis Rpg : rdn BSEGS mem (Z_to_bv 64 0x10ab98) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis Cra : rdn BSEGS mem (at_ S (-2456)) 8 = Some (LE8 ra0).
  Hypothesis Cs0 : rdn BSEGS mem (at_ S (-2464)) 8 = Some (LE8 s0v).
  Hypothesis Cs1 : rdn BSEGS mem (at_ S (-2472)) 8 = Some (LE8 s1v).
  Hypothesis Cs2 : rdn BSEGS mem (at_ S (-2480)) 8 = Some (LE8 s2v).

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma pg_and0 : v_and (Z_to_bv 64 4095) (Z_to_bv 64 h) = Z_to_bv 64 0.
  Proof using Hh HS msz p s2v S rom.
    destruct Hh as (G1 & G2 & _).
    assert (Hb : (0 <= h < 2 ^ 64)%Z) by (destruct HS; destruct Hh as (_ & _ & ? & ? & _); pose proof (u64_range S); lia).
    rewrite v_and_Z by lia. f_equal. change 4095%Z with (Z.ones 12). rewrite Z.land_comm, Z.land_ones by lia.
    change (2 ^ 12)%Z with 4096%Z. exact G2.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Lemma gbb_tail :
    exists r, msteps BSEGS (mkst regs (0x4ebc0 : word) mem rom) (mkst r ra0 (fr_gbb1 mem) rom)
      /\ getr r 2 = at_ S (-2448) /\ getr r 10 = Z_to_bv 64 (h + 4096)
      /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Cs2 Cs1 Cs0 Cra Rpg Rms Rmb Hret Hh HS H13 H11 H10 H8 H2 msz p.
    pose proof (u64_range S) as HSr. destruct Hh as (G1 & G2 & G3 & G4 & G5).
    pose proof (sok_seclock mem) as Hoklk.
    wd_eexists. split.
    - ab_ft F_4ebc0 D_4ebc0 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4ebc4 D_4ebc4 (Z_to_bv 64 h) Rmb.         (* [comment removed for export] *)
      ab_ft F_4ebc8 D_4ebc8 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4ebcc D_4ebcc (Z_to_bv 64 msz) Rms.       (* [comment removed for export] *)
      av F_4ebd0 D_4ebd0 (Z_to_bv 64 (h + msz)) ltac:(valz).   (* [comment removed for export] *)
      ab_ft F_4ebd4 D_4ebd4 ltac:(condz).              (* [comment removed for export] *)
      ab_ft F_4ebd8 D_4ebd8 ltac:(condz).              (* [comment removed for export] *)
      ab_ft F_4ebdc D_4ebdc ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4ebe0 D_4ebe0 (Z_to_bv 64 4096) Rpg.      (* [comment removed for export] *)
      an F_4ebe4 D_4ebe4.                              (* [comment removed for export] *)
      an F_4ebe8 D_4ebe8. rewrite pg_and0.             (* [comment removed for export] *)
      ab_ft F_4ebec D_4ebec ltac:(condz).              (* [comment removed for export] *)
      av F_4ebf0 D_4ebf0 (Z_to_bv 64 (h + 4096)) ltac:(valz).   (* [comment removed for export] *)
      an F_4ebf4 D_4ebf4.                              (* [comment removed for export] *)
      afence F_4ec1c D_4ec1c.                          (* [comment removed for export] *)
      fsb F_4ec20 D_4ec20 (Z_to_bv 64 0x10ae00) (Z_to_bv 8 0).   (* [comment removed for export] *)
      cld8 F_4ec24 D_4ec24 ra0 Cra.                    (* [comment removed for export] *)
      cld8 F_4ec28 D_4ec28 s0v Cs0. cld8 F_4ec2c D_4ec2c s1v Cs1. cld8 F_4ec30 D_4ec30 s2v Cs2.
      an F_4ec34 D_4ec34.                              (* [comment removed for export] *)
      aret F_4ec38 D_4ec38 ra0.                        (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_gbb1 mem). wd_refl.
    - post.
  Qed.
End GBB3.
End FPGen.
End BoAllocFRcS1.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoDepotStore.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupAux.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac Bo_code_8cef4_8dab4.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

Lemma sa_shl44 : forall t, (0 <= t < 2 ^ 32)%Z -> v_slli (Z_to_bv 64 t) 44 = Z_to_bv 64 ((t mod 2 ^ 20) * 2 ^ 44).
Proof using.
  intros t Ht. (lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end). rewrite Z.shiftl_mul_pow2 by lia. rewrite (u_Z2bv t) by lia. apply bv_eq.
  pose proof (Z.mod_pos_bound t (2 ^ 20) ltac:(lia)) as Hm. rewrite !Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap, bv_modulus in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_N] in G in change_no_check G' end).
  replace (t * 2 ^ 44)%Z with ((t mod 2 ^ 20) * 2 ^ 44 + (t / 2 ^ 20) * 2 ^ Z.pos 64)%Z by (pose proof (Z.div_mod t (2 ^ 20) ltac:(lia)); lia).
  apply Z_mod_plus_full.
Qed.
Lemma sa_shr41 : forall r, (0 <= r < 2 ^ 20)%Z -> v_srli (Z_to_bv 64 (r * 2 ^ 44)) 41 = Z_to_bv 64 (8 * r).
Proof using.
  intros r Hr. (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end). rewrite Z.shiftr_div_pow2 by lia. rewrite (u_Z2bv (r * 2 ^ 44)) by lia. f_equal.
  replace (r * 2 ^ 44)%Z with (8 * r * 2 ^ 41)%Z by lia. apply Z.div_mul. lia.
Qed.

Definition sa_mem (M : word -> option byte) (sp ra s0v S idxp : word) (tot cnt : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes M (at_ sp (-8)) (LE8 ra)) (at_ sp (-16)) (LE8 s0v)) S (LE8 (v_add (Z_to_bv 64 tot) (Z_to_bv 64 cnt)))) idxp (LE8 (Z_to_bv 64 tot)).

Section ALLOC.
  Variables (M rom : word -> option byte) (sp ra s0v S idxp packp blkd : word) (tot cnt : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H8 : getr regs 8 = s0v.
  Hypothesis H10 : getr regs 10 = S.
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 cnt.
  Hypothesis H12 : getr regs 12 = idxp.
  Hypothesis H13 : getr regs 13 = packp.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hcnt : (1 <= cnt <= 256)%Z.
  Hypothesis Htot : (0 <= tot < 2 ^ 32)%Z.
  Hypothesis Hsame : (tot / 2 ^ 20 = (tot + cnt - 1) / 2 ^ 20)%Z.                 (* [comment removed for export] *)
  Hypothesis HS : (U S mod 8 = 0 /\ U S + 2 ^ 20 <= 2 ^ 32 /\ (U S + 2 ^ 20 <= U sp - 16 \/ U sp <= U S))%Z.
  Hypothesis Hidx : ((U idxp + 8 <= U sp - 16 \/ U sp <= U idxp) /\ (U idxp + 8 <= U S \/ U S + 2 ^ 20 <= U idxp) /\ U idxp + 8 < 2 ^ 64)%Z.
  Hypothesis Rtot : rdn BSEGS M S 8 = Some (LE8 (Z_to_bv 64 tot)).
  Hypothesis SOKS : store_ok BSEGS M S 8 = true.
  Hypothesis SOKi : store_ok BSEGS M idxp 8 = true.
  Hypothesis Hstk : store_ok BSEGS M (at_ sp (-16)) 16 = true.
  Hypothesis Rblk : rdn BSEGS M (Z_to_bv 64 (U S + 16 * (tot / 2 ^ 20) + 16)) 8 = Some (LE8 blkd).
  Hypothesis Hblk : (U blkd <> 0 /\ U blkd + 2 ^ 23 < 2 ^ 64)%Z.

  Lemma sa_fast :
    exists r, msteps BSEGS (mkst regs (0x8d018 : word) M rom) (mkst r ra (sa_mem M sp ra s0v S idxp tot cnt) rom)
      /\ getr r 10 = Z_to_bv 64 (U blkd + 8 * (tot mod 2 ^ 20)) /\ getr r 2 = sp /\ getr r 1 = ra /\ getr r 8 = s0v
      /\ regs_agree (fun i : reg => In i [1; 2; 5; 6; 8; 10; 11; 12; 14; 15]) regs r.
  Proof using Hblk Rblk Hstk SOKi SOKS Rtot Hidx HS Hsame Htot Hcnt Hret Hsp H12 H11 H10 H8 H2 H1.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range S) as HSr. pose proof (u64_range idxp) as Hir. pose proof (u64_range blkd) as Hbr.
    destruct Hsp as [S1 S2]. destruct HS as (S8 & S32 & SF). destruct Hidx as (I1 & I2 & I3). destruct Hblk as [BK0 BK1].
    assert (Q20 : (0 <= tot / 2 ^ 20 < 2 ^ 12)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (M20 : (0 <= tot mod 2 ^ 20 < 2 ^ 20)%Z) by (apply Z.mod_pos_bound; lia).
    set (MF := wbytes (wbytes M (at_ sp (-8)) (LE8 ra)) (at_ sp (-16)) (LE8 s0v)).
    assert (OUTF : forall x : word, (U x < U sp - 16 \/ U sp <= U x)%Z -> MF x = M x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MF in G in change_no_check G' end). rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity. }
    assert (GRF : mem_grows M MF) by ((lazymatch goal with |- ?G => let G' := eval unfold MF in G in change_no_check G' end); do 2 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    assert (RtotF : rdn BSEGS MF S 8 = Some (LE8 (Z_to_bv 64 tot))).
    { rewrite <- Rtot. apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. cbn in Hx. apply OUTF. lia. }
    assert (OUTA : forall x : word, (U x < U sp - 16 \/ U sp <= U x)%Z -> (U x < U S \/ U S + 8 <= U x)%Z -> (U x < U idxp \/ U idxp + 8 <= U x)%Z ->
              sa_mem M sp ra s0v S idxp tot cnt x = M x).
    { intros x X1 X2 X3. (lazymatch goal with |- ?G => let G' := eval unfold sa_mem in G in change_no_check G' end). fold MF.
      rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. apply OUTF. exact X1. }
    assert (RblkA : rdn BSEGS (sa_mem M sp ra s0v S idxp tot cnt) (Z_to_bv 64 (U S + 16 * (tot / 2 ^ 20) + 16)) 8 = Some (LE8 blkd)).
    { rewrite <- Rblk. apply rdn_ext; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply OUTA; lia. }
    assert (SLA : forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, s0v)]%Z -> rdn BSEGS (sa_mem M sp ra s0v S idxp tot cnt) (at_ sp k) 8 = Some (LE8 v)).
    { intros k v Hin. assert (K : (-16 <= k <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      (lazymatch goal with |- ?G => let G' := eval unfold sa_mem in G in change_no_check G' end). fold MF.
      rewrite !rdn_wbytes_out; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia.
      (lazymatch goal with |- ?G => let G' := eval unfold MF in G in change_no_check G' end). cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin. }
    wd_eexists. split.
    - an F_8d018 D_8d018.                              (* [comment removed for export] *)
      fsd F_8d01c D_8d01c (at_ sp (-8)).               (* [comment removed for export] *)
      fsd F_8d020 D_8d020 (at_ sp (-16)).              (* [comment removed for export] *)
      change (wbytes (wbytes M _ _) _ _) with MF.
      an F_8d024 D_8d024.                              (* [comment removed for export] *)
      an F_8d028 D_8d028.                              (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_amoadd_d with (bs := LE8 (Z_to_bv 64 tot)) (v := Z_to_bv 64 tot);
          [exact F_8d02c | reflexivity | exact D_8d02c
          | gres; rwH; exact S8
          | gres; rwH; exact RtotF
          | apply bytes_le_to_Z_8
          | gres; rwH; eapply store_ok_mono; [exact GRF | exact SOKS]]
        | step_simpl]; vn.                             (* [comment removed for export] *)
      gres. rwH.
      av F_8d030 D_8d030 (Z_to_bv 64 (cnt - 1)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      av F_8d034 D_8d034 (Z_to_bv 64 (tot / 2 ^ 20)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; rewrite (u_Z2bv tot) by lia; reflexivity).   (* [comment removed for export] *)
      av F_8d038 D_8d038 (Z_to_bv 64 (tot + cnt - 1)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      av F_8d03c D_8d03c (Z_to_bv 64 ((tot + cnt - 1) / 2 ^ 20)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; rewrite (u_Z2bv (tot + cnt - 1)) by lia; reflexivity).   (* [comment removed for export] *)
      ab_ft F_8d040 D_8d040 ltac:(rwH; rewrite Hsame; (lazymatch goal with |- ?G => let G' := eval unfold c_eq in G in change_no_check G' end); rewrite bv_eqb_refl; reflexivity).   (* [comment removed for export] *)
      av F_8d044 D_8d044 (Z_to_bv 64 0) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; rewrite (u_Z2bv tot) by lia; rewrite Z.div_small by lia; reflexivity).   (* [comment removed for export] *)
      ab_tk F_8d048 D_8d048 ltac:(condz).              (* [comment removed for export] *)
      fsd F_8d060 D_8d060 idxp.                        (* [comment removed for export] *)
      change (wbytes (wbytes MF S _) idxp _) with (sa_mem M sp ra s0v S idxp tot cnt).
      av F_8d064 D_8d064 (Z_to_bv 64 (16 * (tot / 2 ^ 20))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); rewrite Z.shiftl_mul_pow2 by lia; rewrite (u_Z2bv (tot / 2 ^ 20)) by lia; f_equal; lia).   (* [comment removed for export] *)
      av F_8d068 D_8d068 (Z_to_bv 64 (U S + 16 * (tot / 2 ^ 20))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite (u_Z2bv (16 * (tot / 2 ^ 20))) by lia; reflexivity).   (* [comment removed for export] *)
      cld8 F_8d06c D_8d06c blkd RblkA.                 (* [comment removed for export] *)
      ab_ft F_8d070 D_8d070 ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, bv_eqb in G in change_no_check G' end); apply Z.eqb_neq; unorm; exact BK0).   (* [comment removed for export] *)
      an F_8d074 D_8d074. rewrite (sa_shl44 tot Htot).  (* [comment removed for export] *)
      an F_8d078 D_8d078. rewrite (sa_shr41 (tot mod 2 ^ 20) M20).   (* [comment removed for export] *)
      av F_8d07c D_8d07c (Z_to_bv 64 (U blkd + 8 * (tot mod 2 ^ 20))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite (u_Z2bv (8 * (tot mod 2 ^ 20))) by lia; reflexivity).   (* [comment removed for export] *)
      cld8 F_8d080 D_8d080 ra (SLA (-8)%Z ra ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).     (* [comment removed for export] *)
      cld8 F_8d084 D_8d084 s0v (SLA (-16)%Z s0v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).  (* [comment removed for export] *)
      an F_8d088 D_8d088.                              (* [comment removed for export] *)
      aret F_8d08c D_8d08c ra.                         (* [comment removed for export] *)
      wd_refl.
    - post. all: try ra_solve.
  Qed.
End ALLOC.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Abbreviation LE4 v := (word_to_le_bytes 4 v).

Lemma w32_wrap64 : forall z, bv_wrap 32 (bv_wrap 64 z) = bv_wrap 32 z.
Proof using.
  intros z. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 32) with (2 ^ 32)%Z. change (bv_modulus 64) with (2 ^ 32 * 2 ^ 32)%Z.
  rewrite Z.rem_mul_r by lia.
  replace (z mod 2 ^ 32 + 2 ^ 32 * (z / 2 ^ 32 mod 2 ^ 32))%Z with (z mod 2 ^ 32 + (z / 2 ^ 32 mod 2 ^ 32) * 2 ^ 32)%Z by lia.
  rewrite Z_mod_plus_full. apply Z.mod_mod. lia.
Qed.
Lemma w32_swrap : forall z, bv_wrap 32 (bv_swrap 32 z) = bv_wrap 32 z.
Proof using.
  intros z. (lazymatch goal with |- ?G => let G' := eval unfold bv_swrap, bv_wrap in G in change_no_check G' end). change (bv_half_modulus 32) with (2 ^ 31)%Z. change (bv_modulus 32) with (2 ^ 32)%Z.
  rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.
Lemma u_lw_w32 : forall v : word, bv_wrap 32 (U (v_lw v)) = bv_wrap 32 (U v).
Proof using. intros v. (lazymatch goal with |- ?G => let G' := eval unfold v_lw in G in change_no_check G' end). rewrite Z_to_bv_unsigned, w32_wrap64, w32_swrap. reflexivity. Qed.
Lemma u_addiw_w32 : forall (x : word) i, bv_wrap 32 (U (v_addiw x i)) = bv_wrap 32 (U x + i).
Proof using. intros x i. (lazymatch goal with |- ?G => let G' := eval unfold v_addiw in G in change_no_check G' end). rewrite Z_to_bv_unsigned, w32_wrap64, w32_swrap. reflexivity. Qed.
Lemma le4_congr : forall v1 v2 : word, bv_wrap 32 (U v1) = bv_wrap 32 (U v2) -> LE4 v1 = LE4 v2.
Proof using.
  intros v1 v2 E. (lazymatch goal with |- ?G => let G' := eval unfold word_to_le_bytes in G in change_no_check G' end).
  rewrite <- (Z_to_le_bytes_wrap 4 32 (U v1)), <- (Z_to_le_bytes_wrap 4 32 (U v2)) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia). f_equal. exact E.
Qed.
(* [comment removed for export] *)
Definition st_id (tot : Z) : word := v_addiw (v_lw (Z_to_bv 64 tot)) 1.
Lemma st_id_le4 : forall t, (0 <= t)%Z -> (t + 1 < 2 ^ 32)%Z -> LE4 (st_id t) = LE4 (Z_to_bv 64 (t + 1)).
Proof using.
  intros t T0 T1. apply le4_congr. (lazymatch goal with |- ?G => let G' := eval unfold st_id in G in change_no_check G' end). rewrite u_addiw_w32.
  unfold bv_wrap at 1. rewrite <- Zplus_mod_idemp_l. change (U (v_lw (Z_to_bv 64 t)) mod bv_modulus 32)%Z with (bv_wrap 32 (U (v_lw (Z_to_bv 64 t)))).
  rewrite u_lw_w32. rewrite (u_Z2bv t) by lia. rewrite (u_Z2bv (t + 1)) by lia. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma st_zext : forall a, (0 <= a < 2 ^ 32)%Z -> v_srli (v_slli (v_lw (Z_to_bv 64 a)) 32) 32 = Z_to_bv 64 a.
Proof using.
  intros a Ha.
  assert (E : v_slli (v_lw (Z_to_bv 64 a)) 32 = Z_to_bv 64 (a * 2 ^ 32)).
  { (lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end). rewrite Z.shiftl_mul_pow2 by lia. destruct (Z.lt_ge_cases a (2 ^ 31)) as [Hl|Hg].
    - rewrite Mh32.LibMaskBits.u_lw_lo by lia. reflexivity.
    - rewrite Mh32.LibMaskBits.u_lw_hi by lia. apply bv_eq. rewrite !Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 64) with (2 ^ 64)%Z.
      replace ((a + 2 ^ 32 * (2 ^ 32 - 1)) * 2 ^ 32)%Z with (a * 2 ^ 32 + (2 ^ 32 - 1) * 2 ^ 64)%Z by lia. apply Z_mod_plus_full. }
  rewrite E. (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end). rewrite Z.shiftr_div_pow2 by lia. rewrite (u_Z2bv (a * 2 ^ 32)) by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.
Lemma st_seqz : forall x, (0 <= x < 2 ^ 64)%Z ->
  v_sltiu (v_xor (Z_to_bv 64 x) (Z_to_bv 64 1048576)) 1 = Z_to_bv 64 (if (x =? 1048576)%Z then 1 else 0).
Proof using.
  intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold v_sltiu, v_xor in G in change_no_check G' end). rewrite (u_Z2bv x) by lia. rewrite (u_Z2bv 1048576) by lia.
  pose proof (Z_lxor_range x 1048576 Hx ltac:(lia)) as HR. rewrite (u_Z2bv (Z.lxor x 1048576)) by lia.
  change (bv_wrap 64 1) with 1%Z.
  destruct (Z.eqb_spec x 1048576) as [->|Hne]; [reflexivity|].
  destruct (Z.ltb_spec (Z.lxor x 1048576) 1) as [Hlt|Hge]; [|reflexivity].
  exfalso. apply Hne. apply Z.lxor_eq. lia.
Qed.
Lemma land_m16 : forall x, (0 <= x < 2 ^ 64)%Z -> Z.land x (2 ^ 64 - 16) = (x - x mod 16)%Z.
Proof using.
  intros x Hx. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec.
  assert (Em : (2 ^ 64 - 16 = Z.shiftl (2 ^ 60 - 1) 4)%Z) by reflexivity. rewrite Em.
  assert (Ex : (x - x mod 16 = Z.shiftl (x / 2 ^ 4) 4)%Z).
  { rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4)%Z with 16%Z. pose proof (Z.div_mod x 16 ltac:(lia)). lia. }
  rewrite Ex. destruct (Z.lt_ge_cases k 4) as [Hl|Hg].
  - rewrite !Z.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite !Z.shiftl_spec_high by lia. destruct (Z.lt_ge_cases k 64) as [Hl2|Hg2].
    + assert (Ht : Z.testbit (2 ^ 60 - 1) (k - 4) = true) by (replace (2 ^ 60 - 1)%Z with (Z.ones 60) by reflexivity; apply Z.ones_spec_low; lia).
      rewrite Ht, andb_true_r. rewrite Z.div_pow2_bits by lia. f_equal. lia.
    + rewrite (Mh32.LibMaskBits.testbit_high 64 x k) by lia.
      rewrite (Mh32.LibMaskBits.testbit_high 60 (x / 2 ^ 4) (k - 4)); [reflexivity | lia | | lia].
      change (2 ^ 4)%Z with 16%Z. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Lemma st_andi16 : forall t, (0 <= t < 2 ^ 32)%Z -> v_andi (Z_to_bv 64 (t / 2 ^ 16)) (-16) = Z_to_bv 64 (16 * (t / 2 ^ 20)).
Proof using.
  intros t Ht. (lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end).
  assert (Q : (0 <= t / 2 ^ 16 < 2 ^ 16)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (u_Z2bv (t / 2 ^ 16)) by lia. change (bv_wrap 64 (-16)) with (2 ^ 64 - 16)%Z. rewrite land_m16 by lia. f_equal.
  replace (t / 2 ^ 20)%Z with (t / 2 ^ 16 / 16)%Z by (rewrite Z.div_div by lia; reflexivity).
  pose proof (Z.div_mod (t / 2 ^ 16) 16 ltac:(lia)). lia.
Qed.

Definition st_frame (M : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
    (at_ sp (-8)) (LE8 ra)) (at_ sp (-16)) (LE8 s0v)) (at_ sp (-24)) (LE8 s1v)) (at_ sp (-32)) (LE8 s2v))
    (at_ sp (-40)) (LE8 s3v)) (at_ sp (-48)) (LE8 s4v)) (at_ sp (-56)) (LE8 s5v).
Definition st_m1 (M : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v packp : word) : word -> option byte :=
  wbytes (wbytes (st_frame M sp ra s0v s1v s2v s3v s4v s5v) (at_ sp (-64)) (LE8 (Z_to_bv 64 0))) packp (LE8 (Z_to_bv 64 0)).

Lemma st_frame_outside : forall M sp ra s0v s1v s2v s3v s4v s5v (x : word), (64 <= U sp)%Z ->
  (U x < U sp - 56 \/ U sp <= U x)%Z -> st_frame M sp ra s0v s1v s2v s3v s4v s5v x = M x.
Proof using.
  intros M sp ra s0v s1v s2v s3v s4v s5v x Hsp Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold st_frame in G in change_no_check G' end).
  rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity.
Qed.
Lemma st_frame_grows : forall M sp ra s0v s1v s2v s3v s4v s5v, mem_grows M (st_frame M sp ra s0v s1v s2v s3v s4v s5v).
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold st_frame in G in change_no_check G' end). do 7 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
Lemma st_m1_outside : forall M sp ra s0v s1v s2v s3v s4v s5v packp (x : word), (64 <= U sp)%Z -> (U packp + 8 < 2 ^ 64)%Z ->
  (U x < U sp - 64 \/ U sp <= U x)%Z -> (U x < U packp \/ U packp + 8 <= U x)%Z -> st_m1 M sp ra s0v s1v s2v s3v s4v s5v packp x = M x.
Proof using.
  intros M sp ra s0v s1v s2v s3v s4v s5v packp x Hsp Hp Hx Hxp. pose proof (u64_range sp). pose proof (u64_range packp). (lazymatch goal with |- ?G => let G' := eval unfold st_m1 in G in change_no_check G' end).
  rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia.
  apply st_frame_outside; lia.
Qed.
Lemma st_m1_grows : forall M sp ra s0v s1v s2v s3v s4v s5v packp, mem_grows M (st_m1 M sp ra s0v s1v s2v s3v s4v s5v packp).
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold st_m1 in G in change_no_check G' end). do 2 (eapply mem_grows_trans; [|apply wbytes_grows]). apply st_frame_grows. Qed.

Section STPRE.
  Variables (M rom : word -> option byte) (sp ra S args packp s0v s1v s2v s3v s4v s5v : word) (sz tag : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H8 : getr regs 8 = s0v.
  Hypothesis H9 : getr regs 9 = s1v.
  Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v.
  Hypothesis H20 : getr regs 20 = s4v.
  Hypothesis H21 : getr regs 21 = s5v.
  Hypothesis H10 : getr regs 10 = S.
  Hypothesis H11 : getr regs 11 = args.
  Hypothesis H12 : getr regs 12 = packp.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hargs : ((U sp <= U args \/ U args + 16 <= U sp - 64) /\ U args + 16 < 2 ^ 64)%Z.
  Hypothesis Hpack : ((U sp <= U packp \/ U packp + 8 <= U sp - 64) /\ U packp + 8 < 2 ^ 64)%Z.
  Hypothesis Hsz : (1 <= sz < 255)%Z.
  Hypothesis Htag : (0 <= tag < 256)%Z.
  Hypothesis Rsz : rdn BSEGS M (at_ args 8) 4 = Some (LE4 (Z_to_bv 64 sz)).
  Hypothesis Rtag : rdn BSEGS M (at_ args 12) 4 = Some (LE4 (Z_to_bv 64 tag)).
  Hypothesis Hstk : store_ok BSEGS M (at_ sp (-64)) 64 = true.
  Hypothesis SOKp : store_ok BSEGS M packp 8 = true.

  Lemma st_pre :
    exists r, msteps BSEGS (mkst regs (0x8cef4 : word) M rom) (mkst r (0x8d018 : word) (st_m1 M sp ra s0v s1v s2v s3v s4v s5v packp) rom)
      /\ getr r 1 = (0x8cf6c : word) /\ getr r 2 = at_ sp (-64)
      /\ getr r 10 = S /\ getr r 11 = Z_to_bv 64 (sz + 1) /\ getr r 12 = at_ sp (-64) /\ getr r 13 = packp
      /\ getr r 8 = packp /\ getr r 9 = S /\ getr r 18 = Z_to_bv 64 (sz + 1) /\ getr r 19 = args /\ getr r 20 = Z_to_bv 64 sz /\ getr r 21 = Z_to_bv 64 tag
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 9; 10; 11; 12; 13; 18; 19; 20; 21]) regs r.
  Proof using SOKp Hstk Rtag Rsz Htag Hsz Hpack Hargs Hsp H12 H11 H10 H21 H20 H19 H18 H9 H8 H2 H1.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range args) as Har. pose proof (u64_range packp) as Hpr.
    destruct Hsp as [S1 S2]. destruct Hargs as [A1 A2]. destruct Hpack as [P1 P2].
    set (MF := st_frame M sp ra s0v s1v s2v s3v s4v s5v).
    assert (GRF : mem_grows M MF) by apply st_frame_grows.
    assert (RszF : rdn BSEGS MF (at_ args 8) 4 = Some (LE4 (Z_to_bv 64 sz))).
    { rewrite <- Rsz. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply st_frame_outside; lia. }
    assert (RtagF : rdn BSEGS MF (at_ args 12) 4 = Some (LE4 (Z_to_bv 64 tag))).
    { rewrite <- Rtag. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply st_frame_outside; lia. }
    assert (Vsz : v_lw (Z_to_bv 64 sz) = Z_to_bv 64 sz) by (apply SumsLib.StartupAux.v_lw_small; wd_ulia).
    assert (Vtag : v_lw (Z_to_bv 64 tag) = Z_to_bv 64 tag) by (apply SumsLib.StartupAux.v_lw_small; wd_ulia).
    assert (B4s : bytes_le_to_Z (LE4 (Z_to_bv 64 sz)) = U (Z_to_bv 64 sz)) by (apply SumsLib.StartupAux.bytes_le_to_Z_4_small; wd_ulia).
    assert (B4t : bytes_le_to_Z (LE4 (Z_to_bv 64 tag)) = U (Z_to_bv 64 tag)) by (apply SumsLib.StartupAux.bytes_le_to_Z_4_small; wd_ulia).
    assert (ORNZ : U (v_or (Z_to_bv 64 sz) (Z_to_bv 64 tag)) <> 0%Z).
    { (lazymatch goal with |- ?G => let G' := eval unfold v_or in G in change_no_check G' end). rewrite (u_Z2bv sz), (u_Z2bv tag) by lia.
      pose proof (Z_lor_range sz tag ltac:(lia) ltac:(lia)) as LB.
      rewrite u_Z2bv by lia. intro E0. apply Z.lor_eq_0_iff in E0. lia. }
    wd_eexists. split.
    - an F_8cef4 D_8cef4.                              (* [comment removed for export] *)
      fsd F_8cef8 D_8cef8 (at_ sp (-8)).               (* [comment removed for export] *)
      fsd F_8cefc D_8cefc (at_ sp (-16)).              (* [comment removed for export] *)
      fsd F_8cf00 D_8cf00 (at_ sp (-24)).              (* [comment removed for export] *)
      fsd F_8cf04 D_8cf04 (at_ sp (-32)).              (* [comment removed for export] *)
      fsd F_8cf08 D_8cf08 (at_ sp (-40)).              (* [comment removed for export] *)
      fsd F_8cf0c D_8cf0c (at_ sp (-48)).              (* [comment removed for export] *)
      fsd F_8cf10 D_8cf10 (at_ sp (-56)).              (* [comment removed for export] *)
      change (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M _ _) _ _) _ _) _ _) _ _) _ _) _ _) with MF.
      an F_8cf14 D_8cf14.                              (* [comment removed for export] *)
      clw F_8cf18 D_8cf18 (LE4 (Z_to_bv 64 sz)) (Z_to_bv 64 sz) RszF B4s.     (* [comment removed for export] *)
      rewrite ?Vsz.
      clw F_8cf1c D_8cf1c (LE4 (Z_to_bv 64 tag)) (Z_to_bv 64 tag) RtagF B4t.  (* [comment removed for export] *)
      rewrite ?Vtag.
      an F_8cf20 D_8cf20.                              (* [comment removed for export] *)
      ab_tk F_8cf24 D_8cf24 ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, bv_eqb in G in change_no_check G' end); apply Z.eqb_neq; unorm; exact ORNZ).   (* [comment removed for export] *)
      an F_8cf30 D_8cf30.                              (* [comment removed for export] *)
      an F_8cf34 D_8cf34.                              (* [comment removed for export] *)
      ab_ft F_8cf38 D_8cf38 ltac:(condz).              (* [comment removed for export] *)
      an F_8cf3c D_8cf3c.                              (* [comment removed for export] *)
      an F_8cf40 D_8cf40.                              (* [comment removed for export] *)
      ab_tk F_8cf44 D_8cf44 ltac:(condz).              (* [comment removed for export] *)
      fsd F_8cf4c D_8cf4c (at_ sp (-64)).              (* [comment removed for export] *)
      fsd F_8cf50 D_8cf50 packp.                       (* [comment removed for export] *)
      change (wbytes (wbytes MF _ _) packp _) with (st_m1 M sp ra s0v s1v s2v s3v s4v s5v packp).
      av F_8cf54 D_8cf54 (Z_to_bv 64 (sz + 1)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      an F_8cf58 D_8cf58.                              (* [comment removed for export] *)
      an F_8cf5c D_8cf5c.                              (* [comment removed for export] *)
      an F_8cf60 D_8cf60.                              (* [comment removed for export] *)
      an F_8cf64 D_8cf64.                              (* [comment removed for export] *)
      an F_8cf68 D_8cf68.                              (* [comment removed for export] *)
      wd_refl.
    - post. all: try ra_solve. all: try (apply bv_eq; reflexivity).
  Qed.
End STPRE.

Lemma st_slliw8 : forall tag, (0 <= tag < 256)%Z -> v_slliw (Z_to_bv 64 tag) 8 = Z_to_bv 64 (tag * 2 ^ 8).
Proof using.
  intros tag Htag. (lazymatch goal with |- ?G => let G' := eval unfold v_slliw in G in change_no_check G' end). rewrite Z.shiftl_mul_pow2 by lia. rewrite (u_Z2bv tag) by lia.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31)%Z; lia). reflexivity.
Qed.
Definition st_hdr (sz tag : Z) : word := Z_to_bv 64 (tag * 2 ^ 8 + sz).

Section STMID.
  Variables (M2 rom : word -> option byte) (args tr dst : word) (sz tag : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H10 : getr regs 10 = dst.
  Hypothesis H19 : getr regs 19 = args.
  Hypothesis H20 : getr regs 20 = Z_to_bv 64 sz.
  Hypothesis H21 : getr regs 21 = Z_to_bv 64 tag.
  Hypothesis Hsz : (1 <= sz < 255)%Z.
  Hypothesis Htag : (0 <= tag < 256)%Z.
  Hypothesis Hdst : (U dst <> 0 /\ U dst + 8 < 2 ^ 64)%Z.
  Hypothesis Rtr : rdn BSEGS M2 args 8 = Some (LE8 tr).
  Hypothesis SOKd : store_ok BSEGS M2 dst 8 = true.

  Lemma st_mid :
    exists r, msteps BSEGS (mkst regs (0x8cf6c : word) M2 rom) (mkst r (0x8092c : word) (wbytes M2 dst (LE8 (st_hdr sz tag))) rom)
      /\ getr r 1 = (0x8cf8c : word) /\ getr r 10 = at_ dst 8 /\ getr r 11 = tr /\ getr r 12 = Z_to_bv 64 (8 * sz)
      /\ regs_agree (fun i : reg => In i [1; 10; 11; 12]) regs r.
  Proof using SOKd Rtr Hdst Htag Hsz H21 H20 H19 H10 args.
    pose proof (u64_range dst) as Hdr. pose proof (u64_range args) as Har. destruct Hdst as [D0 D1].
    wd_eexists. split.
    - ab_ft F_8cf6c D_8cf6c ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, bv_eqb in G in change_no_check G' end); apply Z.eqb_neq; unorm; exact D0).   (* [comment removed for export] *)
      an F_8cf70 D_8cf70. rewrite (st_slliw8 tag Htag).   (* [comment removed for export] *)
      cld8 F_8cf74 D_8cf74 tr Rtr.                     (* [comment removed for export] *)
      an F_8cf78 D_8cf78.                              (* [comment removed for export] *)
      rewrite (v_or_shl (Z_to_bv 64 sz) tag 8) by (wd_ulia). rewrite (u_Z2bv sz) by lia. change (Z_to_bv 64 (tag * 2 ^ 8 + sz)) with (st_hdr sz tag).
      fsd F_8cf7c D_8cf7c dst.                         (* [comment removed for export] *)
      an F_8cf80 D_8cf80.                              (* [comment removed for export] *)
      av F_8cf84 D_8cf84 (Z_to_bv 64 (8 * sz)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); rewrite Z.shiftl_mul_pow2 by lia; rewrite (u_Z2bv sz) by lia; f_equal; lia).   (* [comment removed for export] *)
      an F_8cf88 D_8cf88.                              (* [comment removed for export] *)
      wd_refl.
    - post. all: try ra_solve. all: try (apply bv_eq; reflexivity).
  Qed.
End STMID.

Definition st_cell (S : word) (tot : Z) : word := Z_to_bv 64 (U S + 16 * (tot / 2 ^ 20) + 24).
Definition st_full (sov cnt : Z) : Z := if (cnt + sov =? 1048576)%Z then 1%Z else 0%Z.
Definition st_m5 (M4 : word -> option byte) (S packp : word) (tot cnt sov pk : Z) : word -> option byte :=
  wbytes (wbytes M4 (st_cell S tot) (LE4 (v_add (Z_to_bv 64 sov) (Z_to_bv 64 cnt)))) packp (LE8 (Z_to_bv 64 (pk + st_full sov cnt))).

Section STPOST.
  Variables (M4 rom : word -> option byte) (sp ra S packp s0v s1v s2v s3v s4v s5v : word) (tot cnt sov pk : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ sp (-64).
  Hypothesis H8 : getr regs 8 = packp.
  Hypothesis H9 : getr regs 9 = S.
  Hypothesis H18 : getr regs 18 = Z_to_bv 64 cnt.
  Hypothesis Hsp : (2 ^ 32 + 64 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hcnt : (1 <= cnt <= 256)%Z.
  Hypothesis Htot : (0 <= tot < 2 ^ 32)%Z.
  Hypothesis Hsov : (0 <= sov < 2 ^ 32)%Z.
  Hypothesis Hpk : (0 <= pk < 2 ^ 32)%Z.
  Hypothesis HS : (U S mod 4 = 0 /\ U S + 2 ^ 20 <= 2 ^ 32)%Z.
  Hypothesis Hpack : ((U sp <= U packp \/ U packp + 8 <= U sp - 64) /\ 2 ^ 32 <= U packp /\ U packp + 8 < 2 ^ 64)%Z.
  Hypothesis Ridx : rdn BSEGS M4 (at_ sp (-64)) 8 = Some (LE8 (Z_to_bv 64 tot)).
  Hypothesis Rso : rdn BSEGS M4 (st_cell S tot) 4 = Some (LE4 (Z_to_bv 64 sov)).
  Hypothesis SOKso : store_ok BSEGS M4 (st_cell S tot) 4 = true.
  Hypothesis Rpk : rdn BSEGS M4 packp 8 = Some (LE8 (Z_to_bv 64 pk)).
  Hypothesis SOKp : store_ok BSEGS M4 packp 8 = true.
  Hypothesis SL : forall (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v); (-48, s4v); (-56, s5v)]%Z -> rdn BSEGS M4 (at_ sp k) 8 = Some (LE8 v).

  Lemma st_post :
    exists r, msteps BSEGS (mkst regs (0x8cf8c : word) M4 rom) (mkst r ra (st_m5 M4 S packp tot cnt sov pk) rom)
      /\ getr r 10 = st_id tot /\ getr r 2 = sp /\ getr r 1 = ra
      /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v /\ getr r 21 = s5v
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 9; 10; 11; 12; 18; 19; 20; 21]) regs r.
  Proof using SL SOKp Rpk SOKso Rso Ridx Hpack HS Hpk Hsov Htot Hcnt Hret Hsp H18 H9 H8 H2.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range S) as HSr. pose proof (u64_range packp) as Hpr.
    destruct Hsp as [S1 S2]. destruct HS as [S4 S32]. destruct Hpack as (P1 & P32 & P2).
    assert (Q20 : (0 <= tot / 2 ^ 20 < 2 ^ 12)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (Q16 : (0 <= tot / 2 ^ 16 < 2 ^ 16)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (Ucell : U (st_cell S tot) = (U S + 16 * (tot / 2 ^ 20) + 24)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold st_cell in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    assert (ALN : (U (st_cell S tot) mod 4 = 0)%Z).
    { rewrite Ucell. replace (U S + 16 * (tot / 2 ^ 20) + 24)%Z with (U S + (4 * (tot / 2 ^ 20) + 6) * 4)%Z by lia. rewrite Z_mod_plus_full. exact S4. }
    set (MA := wbytes M4 (st_cell S tot) (LE4 (v_add (Z_to_bv 64 sov) (Z_to_bv 64 cnt)))).
    assert (OUTA : forall x : word, (U x < U (st_cell S tot) \/ U (st_cell S tot) + 4 <= U x)%Z -> MA x = M4 x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MA in G in change_no_check G' end). rewrite wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity. }
    assert (GRA : mem_grows M4 MA) by ((lazymatch goal with |- ?G => let G' := eval unfold MA in G in change_no_check G' end); apply wbytes_grows).
    assert (RpkA : rdn BSEGS MA packp 8 = Some (LE8 (Z_to_bv 64 pk))).
    { rewrite <- Rpk. apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. cbn in Hx. apply OUTA. rewrite Ucell. lia. }
    assert (RidxA : rdn BSEGS MA (at_ sp (-64)) 4 = Some (LE4 (Z_to_bv 64 tot))).
    { apply (SumsLib.StartupAux.rdn_low_bytes BSEGS MA (at_ sp (-64)) (Z_to_bv 64 tot) 4 ltac:(lia)).
      rewrite <- Ridx. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply OUTA. rewrite Ucell. lia. }
    assert (B4so : bytes_le_to_Z (LE4 (Z_to_bv 64 sov)) = U (Z_to_bv 64 sov)) by (apply SumsLib.StartupAux.bytes_le_to_Z_4_small; wd_ulia).
    assert (B4t : bytes_le_to_Z (LE4 (Z_to_bv 64 tot)) = U (Z_to_bv 64 tot)) by (apply SumsLib.StartupAux.bytes_le_to_Z_4_small; wd_ulia).
    assert (FUL : (0 <= st_full sov cnt <= 1)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold st_full in G in change_no_check G' end); destruct (cnt + sov =? 1048576)%Z; lia).
    assert (OUT5 : forall x : word, (U x < U (st_cell S tot) \/ U (st_cell S tot) + 4 <= U x)%Z -> (U x < U packp \/ U packp + 8 <= U x)%Z ->
              st_m5 M4 S packp tot cnt sov pk x = M4 x).
    { intros x X1 X2. (lazymatch goal with |- ?G => let G' := eval unfold st_m5 in G in change_no_check G' end). fold MA. rewrite wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. apply OUTA. exact X1. }
    assert (SLF : forall (k : Z) (v : word),
              In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v); (-48, s4v); (-56, s5v)]%Z ->
              rdn BSEGS (st_m5 M4 S packp tot cnt sov pk) (at_ sp k) 8 = Some (LE8 v)).
    { intros k v Hin.
      assert (K : (-56 <= k <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite <- (SL k v Hin). apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|].
      intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply OUT5; rewrite ?Ucell; lia. }
    wd_eexists. split.
    - cld8 F_8cf8c D_8cf8c (Z_to_bv 64 tot) Ridx.      (* [comment removed for export] *)
      av F_8cf90 D_8cf90 (Z_to_bv 64 (tot / 2 ^ 16)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; rewrite (u_Z2bv tot) by lia; reflexivity).   (* [comment removed for export] *)
      av F_8cf94 D_8cf94 (Z_to_bv 64 (16 * (tot / 2 ^ 20))) ltac:(apply st_andi16; lia).   (* [comment removed for export] *)
      av F_8cf98 D_8cf98 (Z_to_bv 64 (U S + 16 * (tot / 2 ^ 20))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite (u_Z2bv (16 * (tot / 2 ^ 20))) by lia; reflexivity).   (* [comment removed for export] *)
      av F_8cf9c D_8cf9c (st_cell S tot) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_addi, st_cell in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_amoadd_w with (bs := LE4 (Z_to_bv 64 sov)) (v := Z_to_bv 64 sov);
          [exact F_8cfa0 | reflexivity | exact D_8cfa0
          | gres; rwH; exact ALN
          | gres; rwH; exact Rso
          | exact B4so
          | gres; rwH; exact SOKso]
        | step_simpl]; vn.                             (* [comment removed for export] *)
      gres. rwH. change (wbytes M4 (st_cell S tot) _) with MA.
      an F_8cfa4 D_8cfa4.                              (* [comment removed for export] *)
      an F_8cfa8 D_8cfa8.                              (* [comment removed for export] *)
      an F_8cfac D_8cfac. rewrite (st_zext sov Hsov).  (* [comment removed for export] *)
      av F_8cfb0 D_8cfb0 (Z_to_bv 64 (cnt + sov)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite (u_Z2bv cnt), (u_Z2bv sov) by lia; reflexivity).   (* [comment removed for export] *)
      cld8 F_8cfb4 D_8cfb4 (Z_to_bv 64 pk) RpkA.       (* [comment removed for export] *)
      an F_8cfb8 D_8cfb8.                              (* [comment removed for export] *)
      clw F_8cfbc D_8cfbc (LE4 (Z_to_bv 64 tot)) (Z_to_bv 64 tot) RidxA B4t.   (* [comment removed for export] *)
      av F_8cfc0 D_8cfc0 (Z_to_bv 64 (st_full sov cnt)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold st_full in G in change_no_check G' end); apply st_seqz; lia).   (* [comment removed for export] *)
      av F_8cfc4 D_8cfc4 (Z_to_bv 64 (pk + st_full sov cnt)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite (u_Z2bv pk), (u_Z2bv (st_full sov cnt)) by lia; reflexivity).   (* [comment removed for export] *)
      fsd F_8cfc8 D_8cfc8 packp.                       (* [comment removed for export] *)
      change (wbytes MA packp _) with (st_m5 M4 S packp tot cnt sov pk).
      an F_8cfcc D_8cfcc.                              (* [comment removed for export] *)
      cld8 F_8cfd0 D_8cfd0 ra (SLF (-8)%Z ra ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      cld8 F_8cfd4 D_8cfd4 s0v (SLF (-16)%Z s0v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      cld8 F_8cfd8 D_8cfd8 s1v (SLF (-24)%Z s1v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      cld8 F_8cfdc D_8cfdc s2v (SLF (-32)%Z s2v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      cld8 F_8cfe0 D_8cfe0 s3v (SLF (-40)%Z s3v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      cld8 F_8cfe4 D_8cfe4 s4v (SLF (-48)%Z s4v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      cld8 F_8cfe8 D_8cfe8 s5v (SLF (-56)%Z s5v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      an F_8cfec D_8cfec.                              (* [comment removed for export] *)
      aret F_8cff0 D_8cff0 ra.                         (* [comment removed for export] *)
      wd_refl.
    - post. all: try ra_solve.
  Qed.
End STPOST.

End FPGen.
End BoDepotStore.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AsAinvDefs3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM1. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac BoAllocFBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM1.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Lemma v_sub_mod : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 ((a - b) mod 2 ^ 64).
Proof using.
  intros a b Ha Hb. apply bv_eq. (lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end). rewrite !Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite (Z.mod_small a), (Z.mod_small b) by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma v_mul_mod : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> v_mul (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 ((a * b) mod 2 ^ 64).
Proof using.
  intros a b Ha Hb. apply bv_eq. (lazymatch goal with |- ?G => let G' := eval unfold v_mul in G in change_no_check G' end). rewrite !Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite (Z.mod_small a), (Z.mod_small b) by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Definition fr_mro (mem : word -> option byte) (S ra0 s0v s1v s2v s3v s4v s5v s6v s7v : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2648)) (LE8 ra0))
    (at_ S (-2656)) (LE8 s0v))
    (at_ S (-2664)) (LE8 s1v))
    (at_ S (-2672)) (LE8 s2v))
    (at_ S (-2680)) (LE8 s3v))
    (at_ S (-2688)) (LE8 s4v))
    (at_ S (-2696)) (LE8 s5v))
    (at_ S (-2704)) (LE8 s6v))
    (at_ S (-2712)) (LE8 s7v).
#[local] Hint Unfold fr_mro : asfr.

Section MRO.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v s3v s4v s5v s6v s7v mapv : word) (rib c nfn pgp : Z) (b80 b88 : list byte).
  Variable regs : bvmap 5 word.
  #[local] Abbreviation cs := (csize c).
  #[local] Abbreviation z80 := (bytes_le_to_Z b80).
  #[local] Abbreviation z88 := (bytes_le_to_Z b88).
  Hypothesis H1 : getr regs 1 = ra0.
  Hypothesis H2 : getr regs 2 = at_ S (-2640).
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x10ab58.
  Hypothesis H11 : getr regs 11 = mapv.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 c.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 0.
  Hypothesis H8 : getr regs 8 = s0v.    Hypothesis H9 : getr regs 9 = s1v.    Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v.  Hypothesis H20 : getr regs 20 = s4v.  Hypothesis H21 : getr regs 21 = s5v.
  Hypothesis H22 : getr regs 22 = s6v.  Hypothesis H23 : getr regs 23 = s7v.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hc : (1 <= c <= 30)%Z.
  Hypothesis Hrib : (AIMGHI <= rib /\ rib + 4096 <= bv_unsigned S - 3584)%Z.
  Hypothesis Hnfn : (0 <= nfn < 2 ^ 32)%Z.
  Hypothesis Lb80 : length b80 = 8%nat.
  Hypothesis Lb88 : length b88 = 8%nat.
  Hypothesis Hpgp : (AIMGLO <= pgp /\ pgp + 8 <= AIMGHI)%Z.
  Hypothesis Hret : ret_ok ra0.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2720)) 80 = true.
  Hypothesis Rrib : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 48)) 8 = Some (LE8 (Z_to_bv 64 rib)).
  Hypothesis Rgpg : rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 pgp)).
  Hypothesis Rpg : rdn BSEGS mem (Z_to_bv 64 pgp) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis Rnf : rdn BSEGS mem (Z_to_bv 64 (rib + 128 * c + 16)) 8 = Some (LE8 (Z_to_bv 64 nfn)).
  Hypothesis R80 : rdn BSEGS mem (Z_to_bv 64 (rib + 128 * c + 80)) 8 = Some b80.
  Hypothesis R88 : rdn BSEGS mem (Z_to_bv 64 (rib + 128 * c + 88)) 8 = Some b88.
  Hypothesis Rint : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 40)) 4 = Some (LE4 0xffffffff).

  #[local] Abbreviation M0 := (fr_mro mem S ra0 s0v s1v s2v s3v s4v s5v s6v s7v).

  Ltac mro_pro :=
      an F_4f688 D_4f688;                              (* [comment removed for export] *)
      fsd F_4f68c D_4f68c (at_ S (-2648));             (* [comment removed for export] *)
      fsd F_4f690 D_4f690 (at_ S (-2656));
      fsd F_4f694 D_4f694 (at_ S (-2664));
      fsd F_4f698 D_4f698 (at_ S (-2672));
      fsd F_4f69c D_4f69c (at_ S (-2680));
      fsd F_4f6a0 D_4f6a0 (at_ S (-2688));
      fsd F_4f6a4 D_4f6a4 (at_ S (-2696));
      fsd F_4f6a8 D_4f6a8 (at_ S (-2704));
      fsd F_4f6ac D_4f6ac (at_ S (-2712));
      an F_4f6b0 D_4f6b0;                              (* [comment removed for export] *)
      an F_4f6b4 D_4f6b4;                              (* [comment removed for export] *)
      an F_4f6b8 D_4f6b8;                              (* [comment removed for export] *)
      an F_4f6bc D_4f6bc;                              (* [comment removed for export] *)
      cld8 F_4f6c0 D_4f6c0 (Z_to_bv 64 rib) Rrib;      (* [comment removed for export] *)
      an F_4f6c4 D_4f6c4;                              (* [comment removed for export] *)
      av F_4f6c8 D_4f6c8 (Z_to_bv 64 (128 * c)) ltac:(apply cls_shl7; lia);   (* [comment removed for export] *)
      ab_ft F_4f6cc D_4f6cc ltac:(condz);              (* [comment removed for export] *)
      an F_4f6d0 D_4f6d0.                              (* [comment removed for export] *)
  Ltac mro_small :=
      ab_ft F_4f6d4 D_4f6d4 ltac:(condz);              (* [comment removed for export] *)
      av F_4f6d8 D_4f6d8 (Z_to_bv 64 cs) ltac:(apply csize_small; lia);   (* [comment removed for export] *)
      an F_4f6dc D_4f6dc.                              (* [comment removed for export] *)
  Ltac mro_big :=
      ab_tk F_4f6d4 D_4f6d4 ltac:(condz);              (* [comment removed for export] *)
      an F_4f6e0 D_4f6e0;                              (* [comment removed for export] *)
      an F_4f6e4 D_4f6e4;                              (* [comment removed for export] *)
      an F_4f6e8 D_4f6e8;                              (* [comment removed for export] *)
      an F_4f6ec D_4f6ec;                              (* [comment removed for export] *)
      an F_4f6f0 D_4f6f0;                              (* [comment removed for export] *)
      an F_4f6f4 D_4f6f4;                              (* [comment removed for export] *)
      an F_4f6f8 D_4f6f8;                              (* [comment removed for export] *)
      an F_4f6fc D_4f6fc;                              (* [comment removed for export] *)
      av F_4f700 D_4f700 (Z_to_bv 64 cs) ltac:(apply (csize_big c); lia).   (* [comment removed for export] *)
  Ltac mro_mid CSP :=
      an F_4f704 D_4f704;                              (* [comment removed for export] *)
      cld8 F_4f708 D_4f708 (Z_to_bv 64 pgp) Rgpg;      (* [comment removed for export] *)
      cld8 F_4f70c D_4f70c (Z_to_bv 64 4096) Rpg;      (* [comment removed for export] *)
      av F_4f710 D_4f710 (Z_to_bv 64 (rib + 128 * c)) ltac:(valz);   (* [comment removed for export] *)
      ab_ft F_4f714 D_4f714 ltac:(condz);              (* [comment removed for export] *)
      cld8 F_4f718 D_4f718 (Z_to_bv 64 nfn) Rnf;       (* [comment removed for export] *)
      av F_4f71c D_4f71c (Z_to_bv 64 (nfn * cs)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_mul in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
  Ltac mro_epi :=
      fld F_4f830 D_4f830 ra0; fld F_4f834 D_4f834 s0v; fld F_4f838 D_4f838 s1v; fld F_4f83c D_4f83c s2v; fld F_4f840 D_4f840 s3v;
      fld F_4f844 D_4f844 s4v; fld F_4f848 D_4f848 s5v; fld F_4f84c D_4f84c s6v; fld F_4f850 D_4f850 s7v;
      an F_4f854 D_4f854;                              (* [comment removed for export] *)
      aret F_4f858 D_4f858 ra0.                        (* [comment removed for export] *)

  Definition mro_post (r : bvmap 5 word) : Prop :=
    getr r 2 = at_ S (-2640) /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v
    /\ getr r 21 = s5v /\ getr r 22 = s6v /\ getr r 23 = s7v
    /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25
    /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.

  Lemma mro_run : exists r, msteps BSEGS (mkst regs (0x4f688 : word) mem rom) (mkst r ra0 M0 rom) /\ mro_post r.
  Proof using Rint R88 R80 Rnf Rpg Rgpg Rrib Hstk Hret Hpgp Lb88 Lb80 Hnfn Hrib Hc HS H23 H22 H21 H20 H19 H18 H9 H8 H13 H12 H11 H10 H2 H1 b88 b80 pgp nfn c rib mapv.
    (lazymatch goal with |- ?G => let G' := eval unfold mro_post in G in change_no_check G' end). pose proof (u64_range S) as HSr. pose proof (csize_pos c Hc) as (CSP & _).
    assert (Hz80 : (0 <= z80 < 2 ^ 64)%Z) by (pose proof (bytes_le_to_Z_bound b80) as B; rewrite Lb80 in B; change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in B; pose proof (bytes_le_to_Z_nonneg b80); lia).
    assert (Hz88 : (0 <= z88 < 2 ^ 64)%Z) by (pose proof (bytes_le_to_Z_bound b88) as B; rewrite Lb88 in B; change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in B; pose proof (bytes_le_to_Z_nonneg b88); lia).
    assert (V80 : z80 = bv_unsigned (Z_to_bv 64 z80)) by (rewrite u_Z2bv by lia; reflexivity).
    assert (V88 : z88 = bv_unsigned (Z_to_bv 64 z88)) by (rewrite u_Z2bv by lia; reflexivity).
    set (P2 := (((z80 - z88) mod 2 ^ 64) * cs mod 2 ^ 64)%Z).
    assert (HP2 : (0 <= P2 < 2 ^ 64)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold P2 in G in change_no_check G' end); apply Z.mod_pos_bound; lia).
    assert (HP1 : (0 <= nfn * cs < 2 ^ 48)%Z) by nia.
    assert (ARMS : forall r0 : bvmap 5 word,
              getr r0 2 = at_ S (-2720) -> getr r0 10 = Z_to_bv 64 4096 -> getr r0 11 = Z_to_bv 64 (nfn * cs) -> getr r0 18 = Z_to_bv 64 cs ->
              getr r0 19 = Z_to_bv 64 0x10ab58 -> getr r0 21 = Z_to_bv 64 0 -> getr r0 22 = Z_to_bv 64 (rib + 128 * c) ->
              getr r0 3 = getr regs 3 -> getr r0 4 = getr regs 4 -> getr r0 24 = getr regs 24 -> getr r0 25 = getr regs 25 ->
              getr r0 26 = getr regs 26 -> getr r0 27 = getr regs 27 ->
              exists r, msteps BSEGS (mkst r0 (0x4f720 : word) M0 rom) (mkst r ra0 M0 rom) /\
                getr r 2 = at_ S (-2640) /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v
                /\ getr r 21 = s5v /\ getr r 22 = s6v /\ getr r 23 = s7v
                /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25
                /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27).
    { intros r0 G2 G10 G11 G18 G19 G21 G22 G3 G4 G24 G25 G26 G27.
      destruct (Z_lt_dec (nfn * cs) 4096) as [L1 | L1].
      - (* [comment removed for export] *)
        wd_eexists. split.
        + ab_ft F_4f720 D_4f720 ltac:(condz).   (* [comment removed for export] *)
          an F_4f724 D_4f724.                          (* [comment removed for export] *)
          mro_epi. wd_refl.
        + rewrite <- G3, <- G4, <- G24, <- G25, <- G26, <- G27. post.
      - destruct (Z_lt_dec P2 4096) as [L2 | L2].
        + (* [comment removed for export] *)
          wd_eexists. split.
          * ab_tk F_4f720 D_4f720 ltac:(condz).
            cld F_4f73c D_4f73c b80 (Z_to_bv 64 z80) R80 V80.   (* [comment removed for export] *)
            cld F_4f740 D_4f740 b88 (Z_to_bv 64 z88) R88 V88.   (* [comment removed for export] *)
            av F_4f744 D_4f744 (Z_to_bv 64 ((z80 - z88) mod 2 ^ 64)) ltac:(apply v_sub_mod; lia).   (* [comment removed for export] *)
            av F_4f748 D_4f748 (Z_to_bv 64 P2) ltac:((lazymatch goal with |- ?G => let G' := eval unfold P2 in G in change_no_check G' end); apply v_mul_mod; [apply Z.mod_pos_bound; lia | lia]).   (* [comment removed for export] *)
            ab_tk F_4f74c D_4f74c ltac:(condz).   (* [comment removed for export] *)
            mro_epi. wd_refl.
          * rewrite <- G3, <- G4, <- G24, <- G25, <- G26, <- G27. post.
        + (* [comment removed for export] *)
          assert (Vint : bytes_le_to_Z (LE4 0xffffffff) = bv_unsigned (Z_to_bv 64 0xffffffff)) by (apply bytes4_small; lia).
          wd_eexists. split.
          * ab_tk F_4f720 D_4f720 ltac:(condz).
            cld F_4f73c D_4f73c b80 (Z_to_bv 64 z80) R80 V80.
            cld F_4f740 D_4f740 b88 (Z_to_bv 64 z88) R88 V88.
            av F_4f744 D_4f744 (Z_to_bv 64 ((z80 - z88) mod 2 ^ 64)) ltac:(apply v_sub_mod; lia).
            av F_4f748 D_4f748 (Z_to_bv 64 P2) ltac:((lazymatch goal with |- ?G => let G' := eval unfold P2 in G in change_no_check G' end); apply v_mul_mod; [apply Z.mod_pos_bound; lia | lia]).
            ab_ft F_4f74c D_4f74c ltac:(condz).   (* [comment removed for export] *)
            ab_ft F_4f750 D_4f750 ltac:(condz).   (* [comment removed for export] *)
            clw F_4f754 D_4f754 (LE4 0xffffffff) (Z_to_bv 64 0xffffffff) Rint Vint.   (* [comment removed for export] *)
            ab_tk F_4f758 D_4f758 ltac:(vm_compute; reflexivity).   (* [comment removed for export] *)
            mro_epi. wd_refl.
          * rewrite <- G3, <- G4, <- G24, <- G25, <- G26, <- G27. post. }
    destruct (Z_le_gt_dec c 16) as [Hsm | Hbg].
    - assert (PRE : exists r0, msteps BSEGS (mkst regs (0x4f688 : word) mem rom) (mkst r0 (0x4f720 : word) M0 rom)
                      /\ getr r0 2 = at_ S (-2720) /\ getr r0 10 = Z_to_bv 64 4096 /\ getr r0 11 = Z_to_bv 64 (nfn * cs) /\ getr r0 18 = Z_to_bv 64 cs
                      /\ getr r0 19 = Z_to_bv 64 0x10ab58 /\ getr r0 21 = Z_to_bv 64 0 /\ getr r0 22 = Z_to_bv 64 (rib + 128 * c)
                      /\ getr r0 3 = getr regs 3 /\ getr r0 4 = getr regs 4 /\ getr r0 24 = getr regs 24 /\ getr r0 25 = getr regs 25
                      /\ getr r0 26 = getr regs 26 /\ getr r0 27 = getr regs 27).
      { wd_eexists. split; [mro_pro; mro_small; mro_mid CSP; change (wbytes _ _ _) with M0; wd_refl | post]. }
      destruct PRE as (r0 & RUN0 & G2 & G10 & G11 & G18 & G19 & G21 & G22 & G3 & G4 & G24 & G25 & G26 & G27).
      destruct (ARMS r0 G2 G10 G11 G18 G19 G21 G22 G3 G4 G24 G25 G26 G27) as (r & RUN1 & POST).
      exists r. split; [eapply msteps_trans; [exact RUN0 | exact RUN1] | exact POST].
    - assert (PRE : exists r0, msteps BSEGS (mkst regs (0x4f688 : word) mem rom) (mkst r0 (0x4f720 : word) M0 rom)
                      /\ getr r0 2 = at_ S (-2720) /\ getr r0 10 = Z_to_bv 64 4096 /\ getr r0 11 = Z_to_bv 64 (nfn * cs) /\ getr r0 18 = Z_to_bv 64 cs
                      /\ getr r0 19 = Z_to_bv 64 0x10ab58 /\ getr r0 21 = Z_to_bv 64 0 /\ getr r0 22 = Z_to_bv 64 (rib + 128 * c)
                      /\ getr r0 3 = getr regs 3 /\ getr r0 4 = getr regs 4 /\ getr r0 24 = getr regs 24 /\ getr r0 25 = getr regs 25
                      /\ getr r0 26 = getr regs 26 /\ getr r0 27 = getr regs 27).
      { wd_eexists. split; [mro_pro; mro_big; mro_mid CSP; change (wbytes _ _ _) with M0; wd_refl | post]. }
      destruct PRE as (r0 & RUN0 & G2 & G10 & G11 & G18 & G19 & G21 & G22 & G3 & G4 & G24 & G25 & G26 & G27).
      destruct (ARMS r0 G2 G10 G11 G18 G19 G21 G22 G3 G4 G24 G25 G26 G27) as (r & RUN1 & POST).
      exists r. split; [eapply msteps_trans; [exact RUN0 | exact RUN1] | exact POST].
  Qed.
End MRO.
End FPGen.
