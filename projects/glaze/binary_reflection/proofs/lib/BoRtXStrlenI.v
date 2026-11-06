(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.InstrEnc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Bo_code_56520_5665c.
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
























End Bo_code_56520_5665c.
Module Bo_code_58228_58364.
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
Definition W_58228 : bv 32 := @BV 32 0x000ae597%Z I.
Lemma F_58228 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x58228%Z I : word) = Some W_58228.
Proof. vm_refl. Qed.
Lemma D_58228 : decode_any W_58228 = Some (Auipc (@BV 5 11%Z I) (@BV 20 174%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5822c : bv 32 := @BV 32 0xcf05b583%Z I.
Lemma F_5822c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5822c%Z I : word) = Some W_5822c.
Proof. vm_refl. Qed.
Lemma D_5822c : decode_any W_5822c = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 3312%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_58248 : bv 32 := @BV 32 0x000ae697%Z I.
Lemma F_58248 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x58248%Z I : word) = Some W_58248.
Proof. vm_refl. Qed.
Lemma D_58248 : decode_any W_58248 = Some (Auipc (@BV 5 13%Z I) (@BV 20 174%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5824c : bv 32 := @BV 32 0xcd86b683%Z I.
Lemma F_5824c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5824c%Z I : word) = Some W_5824c.
Proof. vm_refl. Qed.
Lemma D_5824c : decode_any W_5824c = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 3288%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_58250 : bv 32 := @BV 32 0x000ae717%Z I.
Lemma F_58250 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x58250%Z I : word) = Some W_58250.
Proof. vm_refl. Qed.
Lemma D_58250 : decode_any W_58250 = Some (Auipc (@BV 5 14%Z I) (@BV 20 174%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_58254 : bv 32 := @BV 32 0xcd873703%Z I.
Lemma F_58254 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x58254%Z I : word) = Some W_58254.
Proof. vm_refl. Qed.
Lemma D_58254 : decode_any W_58254 = Some (Load SZ8 true (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 12 3288%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5826c : bv 32 := @BV 32 0x000ae717%Z I.
Lemma F_5826c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5826c%Z I : word) = Some W_5826c.
Proof. vm_refl. Qed.
Lemma D_5826c : decode_any W_5826c = Some (Auipc (@BV 5 14%Z I) (@BV 20 174%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_58270 : bv 32 := @BV 32 0xcc473703%Z I.
Lemma F_58270 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x58270%Z I : word) = Some W_58270.
Proof. vm_refl. Qed.
Lemma D_58270 : decode_any W_58270 = Some (Load SZ8 true (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 12 3268%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_58228_58364.
Module Bo_code_79bf8_79d34.
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
























End Bo_code_79bf8_79d34.
Module Bo_code_70a08_70d4c.
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
Definition W_70a34 : bv 32 := @BV 32 0x00095517%Z I.
Lemma F_70a34 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x70a34%Z I : word) = Some W_70a34.
Proof. vm_refl. Qed.
Lemma D_70a34 : decode_any W_70a34 = Some (Auipc (@BV 5 10%Z I) (@BV 20 149%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70a38 : bv 32 := @BV 32 0x4e453a83%Z I.
Lemma F_70a38 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x70a38%Z I : word) = Some W_70a38.
Proof. vm_refl. Qed.
Lemma D_70a38 : decode_any W_70a38 = Some (Load SZ8 true (@BV 5 21%Z I) (@BV 5 10%Z I) (@BV 12 1252%Z I), 4%Z).
Proof. vm_refl. Qed.













(* [comment removed for export] *)
Definition W_70a54 : bv 32 := @BV 32 0x00095697%Z I.
Lemma F_70a54 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x70a54%Z I : word) = Some W_70a54.
Proof. vm_refl. Qed.
Lemma D_70a54 : decode_any W_70a54 = Some (Auipc (@BV 5 13%Z I) (@BV 20 149%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70a58 : bv 32 := @BV 32 0x4cc6b683%Z I.
Lemma F_70a58 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x70a58%Z I : word) = Some W_70a58.
Proof. vm_refl. Qed.
Lemma D_70a58 : decode_any W_70a58 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 1228%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70a5c : bv 32 := @BV 32 0x00095717%Z I.
Lemma F_70a5c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x70a5c%Z I : word) = Some W_70a5c.
Proof. vm_refl. Qed.
Lemma D_70a5c : decode_any W_70a5c = Some (Auipc (@BV 5 14%Z I) (@BV 20 149%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70a60 : bv 32 := @BV 32 0x4cc73703%Z I.
Lemma F_70a60 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x70a60%Z I : word) = Some W_70a60.
Proof. vm_refl. Qed.
Lemma D_70a60 : decode_any W_70a60 = Some (Load SZ8 true (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 12 1228%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70a78 : bv 32 := @BV 32 0x00095717%Z I.
Lemma F_70a78 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x70a78%Z I : word) = Some W_70a78.
Proof. vm_refl. Qed.
Lemma D_70a78 : decode_any W_70a78 = Some (Auipc (@BV 5 14%Z I) (@BV 20 149%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70a7c : bv 32 := @BV 32 0x4b873703%Z I.
Lemma F_70a7c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x70a7c%Z I : word) = Some W_70a7c.
Proof. vm_refl. Qed.
Lemma D_70a7c : decode_any W_70a7c = Some (Load SZ8 true (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 12 1208%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70a9c : bv 32 := @BV 32 0x00095617%Z I.
Lemma F_70a9c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x70a9c%Z I : word) = Some W_70a9c.
Proof. vm_refl. Qed.
Lemma D_70a9c : decode_any W_70a9c = Some (Auipc (@BV 5 12%Z I) (@BV 20 149%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70aa0 : bv 32 := @BV 32 0x48463603%Z I.
Lemma F_70aa0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x70aa0%Z I : word) = Some W_70aa0.
Proof. vm_refl. Qed.
Lemma D_70aa0 : decode_any W_70aa0 = Some (Load SZ8 true (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 1156%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70aa4 : bv 32 := @BV 32 0x00095697%Z I.
Lemma F_70aa4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x70aa4%Z I : word) = Some W_70aa4.
Proof. vm_refl. Qed.
Lemma D_70aa4 : decode_any W_70aa4 = Some (Auipc (@BV 5 13%Z I) (@BV 20 149%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70aa8 : bv 32 := @BV 32 0x4846b683%Z I.
Lemma F_70aa8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x70aa8%Z I : word) = Some W_70aa8.
Proof. vm_refl. Qed.
Lemma D_70aa8 : decode_any W_70aa8 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 1156%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70ac0 : bv 32 := @BV 32 0x00095697%Z I.
Lemma F_70ac0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x70ac0%Z I : word) = Some W_70ac0.
Proof. vm_refl. Qed.
Lemma D_70ac0 : decode_any W_70ac0 = Some (Auipc (@BV 5 13%Z I) (@BV 20 149%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70ac4 : bv 32 := @BV 32 0x4706b683%Z I.
Lemma F_70ac4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x70ac4%Z I : word) = Some W_70ac4.
Proof. vm_refl. Qed.
Lemma D_70ac4 : decode_any W_70ac4 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 1136%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_70a08_70d4c.
Module Bo_code_5ce30_5d514.
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
Definition W_5d2fc : bv 32 := @BV 32 0xfbf48593%Z I.
Lemma F_5d2fc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5d2fc%Z I : word) = Some W_5d2fc.
Proof. vm_refl. Qed.
Lemma D_5d2fc : decode_any W_5d2fc = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 12 4031%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d300 : bv 32 := @BV 32 0xfbf00613%Z I.
Lemma F_5d300 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5d300%Z I : word) = Some W_5d300.
Proof. vm_refl. Qed.
Lemma D_5d300 : decode_any W_5d300 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 4031%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d304 : bv 32 := @BV 32 0x0eb67863%Z I.
Lemma F_5d304 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5d304%Z I : word) = Some W_5d304.
Proof. vm_refl. Qed.
Lemma D_5d304 : decode_any W_5d304 = Some (Branch BC_GEU (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 13 240%Z I), 4%Z).
Proof. vm_refl. Qed.










(* [comment removed for export] *)
Definition W_5d3f4 : bv 32 := @BV 32 0x02049e63%Z I.
Lemma F_5d3f4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5d3f4%Z I : word) = Some W_5d3f4.
Proof. vm_refl. Qed.
Lemma D_5d3f4 : decode_any W_5d3f4 = Some (Branch BC_NE (@BV 5 9%Z I) (@BV 5 0%Z I) (@BV 13 60%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d430 : bv 32 := @BV 32 0x00050b13%Z I.
Lemma F_5d430 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5d430%Z I : word) = Some W_5d430.
Proof. vm_refl. Qed.
Lemma D_5d430 : decode_any W_5d430 = Some (OpImm ALU_ADD (@BV 5 22%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d434 : bv 32 := @BV 32 0x00090513%Z I.
Lemma F_5d434 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5d434%Z I : word) = Some W_5d434.
Proof. vm_refl. Qed.
Lemma D_5d434 : decode_any W_5d434 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d438 : bv 32 := @BV 32 0x00048593%Z I.
Lemma F_5d438 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5d438%Z I : word) = Some W_5d438.
Proof. vm_refl. Qed.
Lemma D_5d438 : decode_any W_5d438 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d43c : bv 32 := @BV 32 0x5cc130ef%Z I.
Lemma F_5d43c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5d43c%Z I : word) = Some W_5d43c.
Proof. vm_refl. Qed.
Lemma D_5d43c : decode_any W_5d43c = Some (Jal (@BV 5 1%Z I) (@BV 21 79308%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d440 : bv 32 := @BV 32 0x00050913%Z I.
Lemma F_5d440 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5d440%Z I : word) = Some W_5d440.
Proof. vm_refl. Qed.
Lemma D_5d440 : decode_any W_5d440 = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d444 : bv 32 := @BV 32 0x000b0513%Z I.
Lemma F_5d444 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5d444%Z I : word) = Some W_5d444.
Proof. vm_refl. Qed.
Lemma D_5d444 : decode_any W_5d444 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 22%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d448 : bv 32 := @BV 32 0xee090ee3%Z I.
Lemma F_5d448 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5d448%Z I : word) = Some W_5d448.
Proof. vm_refl. Qed.
Lemma D_5d448 : decode_any W_5d448 = Some (Branch BC_EQ (@BV 5 18%Z I) (@BV 5 0%Z I) (@BV 13 7932%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_5ce30_5d514.
Module Bo_code_5e7a4_5e804.
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
Definition W_5e7ac : bv 32 := @BV 32 0xfbf48593%Z I.
Lemma F_5e7ac : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5e7ac%Z I : word) = Some W_5e7ac.
Proof. vm_refl. Qed.
Lemma D_5e7ac : decode_any W_5e7ac = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 12 4031%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e7b0 : bv 32 := @BV 32 0xfbf00613%Z I.
Lemma F_5e7b0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5e7b0%Z I : word) = Some W_5e7b0.
Proof. vm_refl. Qed.
Lemma D_5e7b0 : decode_any W_5e7b0 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 4031%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e7b4 : bv 32 := @BV 32 0x12b67663%Z I.
Lemma F_5e7b4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5e7b4%Z I : word) = Some W_5e7b4.
Proof. vm_refl. Qed.
Lemma D_5e7b4 : decode_any W_5e7b4 = Some (Branch BC_GEU (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 13 300%Z I), 4%Z).
Proof. vm_refl. Qed.









End Bo_code_5e7a4_5e804.
Module Bo_code_5e8e0_5e938.
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
Definition W_5e8e0 : bv 32 := @BV 32 0x02049e63%Z I.
Lemma F_5e8e0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5e8e0%Z I : word) = Some W_5e8e0.
Proof. vm_refl. Qed.
Lemma D_5e8e0 : decode_any W_5e8e0 = Some (Branch BC_NE (@BV 5 9%Z I) (@BV 5 0%Z I) (@BV 13 60%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e91c : bv 32 := @BV 32 0x00050a93%Z I.
Lemma F_5e91c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5e91c%Z I : word) = Some W_5e91c.
Proof. vm_refl. Qed.
Lemma D_5e91c : decode_any W_5e91c = Some (OpImm ALU_ADD (@BV 5 21%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e920 : bv 32 := @BV 32 0x00090513%Z I.
Lemma F_5e920 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5e920%Z I : word) = Some W_5e920.
Proof. vm_refl. Qed.
Lemma D_5e920 : decode_any W_5e920 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e924 : bv 32 := @BV 32 0x00048593%Z I.
Lemma F_5e924 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5e924%Z I : word) = Some W_5e924.
Proof. vm_refl. Qed.
Lemma D_5e924 : decode_any W_5e924 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e928 : bv 32 := @BV 32 0x0e0120ef%Z I.
Lemma F_5e928 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5e928%Z I : word) = Some W_5e928.
Proof. vm_refl. Qed.
Lemma D_5e928 : decode_any W_5e928 = Some (Jal (@BV 5 1%Z I) (@BV 21 73952%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e92c : bv 32 := @BV 32 0x00050913%Z I.
Lemma F_5e92c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5e92c%Z I : word) = Some W_5e92c.
Proof. vm_refl. Qed.
Lemma D_5e92c : decode_any W_5e92c = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e930 : bv 32 := @BV 32 0x000a8513%Z I.
Lemma F_5e930 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5e930%Z I : word) = Some W_5e930.
Proof. vm_refl. Qed.
Lemma D_5e930 : decode_any W_5e930 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 21%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e934 : bv 32 := @BV 32 0xec0900e3%Z I.
Lemma F_5e934 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5e934%Z I : word) = Some W_5e934.
Proof. vm_refl. Qed.
Lemma D_5e934 : decode_any W_5e934 = Some (Branch BC_EQ (@BV 5 18%Z I) (@BV 5 0%Z I) (@BV 13 7872%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_5e8e0_5e938.
Module Bo_code_5fd64_5fe74.
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
Definition W_5fe1c : bv 32 := @BV 32 0xfbfb8513%Z I.
Lemma F_5fe1c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5fe1c%Z I : word) = Some W_5fe1c.
Proof. vm_refl. Qed.
Lemma D_5fe1c : decode_any W_5fe1c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 23%Z I) (@BV 12 4031%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe20 : bv 32 := @BV 32 0xfbf00593%Z I.
Lemma F_5fe20 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5fe20%Z I : word) = Some W_5fe20.
Proof. vm_refl. Qed.
Lemma D_5fe20 : decode_any W_5fe20 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 4031%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe24 : bv 32 := @BV 32 0x2ca5f063%Z I.
Lemma F_5fe24 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5fe24%Z I : word) = Some W_5fe24.
Proof. vm_refl. Qed.
Lemma D_5fe24 : decode_any W_5fe24 = Some (Branch BC_GEU (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 13 704%Z I), 4%Z).
Proof. vm_refl. Qed.









End Bo_code_5fd64_5fe74.
Module Bo_code_5fe94_5fea8.
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
Definition W_5fe98 : bv 32 := @BV 32 0x000b0513%Z I.
Lemma F_5fe98 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5fe98%Z I : word) = Some W_5fe98.
Proof. vm_refl. Qed.
Lemma D_5fe98 : decode_any W_5fe98 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 22%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe9c : bv 32 := @BV 32 0x000b8593%Z I.
Lemma F_5fe9c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5fe9c%Z I : word) = Some W_5fe9c.
Proof. vm_refl. Qed.
Lemma D_5fe9c : decode_any W_5fe9c = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 23%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fea0 : bv 32 := @BV 32 0x369100ef%Z I.
Lemma F_5fea0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5fea0%Z I : word) = Some W_5fea0.
Proof. vm_refl. Qed.
Lemma D_5fea0 : decode_any W_5fea0 = Some (Jal (@BV 5 1%Z I) (@BV 21 68456%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fea4 : bv 32 := @BV 32 0xec0506e3%Z I.
Lemma F_5fea4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5fea4%Z I : word) = Some W_5fea4.
Proof. vm_refl. Qed.
Lemma D_5fea4 : decode_any W_5fea4 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 7884%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_5fe94_5fea8.
Module Bo_code_600e4_600e8.
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
Definition W_600e4 : bv 32 := @BV 32 0xda0b9ae3%Z I.
Lemma F_600e4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x600e4%Z I : word) = Some W_600e4.
Proof. vm_refl. Qed.
Lemma D_600e4 : decode_any W_600e4 = Some (Branch BC_NE (@BV 5 23%Z I) (@BV 5 0%Z I) (@BV 13 7604%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_600e4_600e8.
Module Bo_code_fc5e4_fc674.
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
Definition W_fc620 : bv 32 := @BV 32 0xfff14597%Z I.
Lemma F_fc620 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfc614%Z I : word) = Some W_fc620.
Proof. vm_refl. Qed.
Lemma D_fc620 : decode_any W_fc620 = Some (Auipc (@BV 5 11%Z I) (@BV 20 1048340%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fc624 : bv 32 := @BV 32 0xfff14717%Z I.
Lemma F_fc624 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfc618%Z I : word) = Some W_fc624.
Proof. vm_refl. Qed.
Lemma D_fc624 : decode_any W_fc624 = Some (Auipc (@BV 5 14%Z I) (@BV 20 1048340%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fc628 : bv 32 := @BV 32 0xdec5b683%Z I.
Lemma F_fc628 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfc61c%Z I : word) = Some W_fc628.
Proof. vm_refl. Qed.
Lemma D_fc628 : decode_any W_fc628 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 11%Z I) (@BV 12 3564%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fc62c : bv 32 := @BV 32 0xdc873703%Z I.
Lemma F_fc62c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfc620%Z I : word) = Some W_fc62c.
Proof. vm_refl. Qed.
Lemma D_fc62c : decode_any W_fc62c = Some (Load SZ8 true (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 12 3528%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_fc5e4_fc674.
Module Bo_code_5cfec_5d280.
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
Definition W_5d028 : bv 32 := @BV 32 0x000ab597%Z I.
Lemma F_5d028 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5d028%Z I : word) = Some W_5d028.
Proof. vm_refl. Qed.
Lemma D_5d028 : decode_any W_5d028 = Some (Auipc (@BV 5 11%Z I) (@BV 20 171%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d02c : bv 32 := @BV 32 0xcb05b583%Z I.
Lemma F_5d02c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5d02c%Z I : word) = Some W_5d02c.
Proof. vm_refl. Qed.
Lemma D_5d02c : decode_any W_5d02c = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 3248%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d040 : bv 32 := @BV 32 0x000a9597%Z I.
Lemma F_5d040 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5d040%Z I : word) = Some W_5d040.
Proof. vm_refl. Qed.
Lemma D_5d040 : decode_any W_5d040 = Some (Auipc (@BV 5 11%Z I) (@BV 20 169%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d044 : bv 32 := @BV 32 0xec85b983%Z I.
Lemma F_5d044 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5d044%Z I : word) = Some W_5d044.
Proof. vm_refl. Qed.
Lemma D_5d044 : decode_any W_5d044 = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 11%Z I) (@BV 12 3784%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d06c : bv 32 := @BV 32 0x000a9597%Z I.
Lemma F_5d06c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5d06c%Z I : word) = Some W_5d06c.
Proof. vm_refl. Qed.
Lemma D_5d06c : decode_any W_5d06c = Some (Auipc (@BV 5 11%Z I) (@BV 20 169%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d070 : bv 32 := @BV 32 0xeac5b583%Z I.
Lemma F_5d070 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5d070%Z I : word) = Some W_5d070.
Proof. vm_refl. Qed.
Lemma D_5d070 : decode_any W_5d070 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 3756%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0a0 : bv 32 := @BV 32 0x0c071e63%Z I.
Lemma F_5d0a0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5d0a0%Z I : word) = Some W_5d0a0.
Proof. vm_refl. Qed.
Lemma D_5d0a0 : decode_any W_5d0a0 = Some (Branch BC_NE (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 13 220%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d1b0 : bv 32 := @BV 32 0x0c050463%Z I.
Lemma F_5d1b0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5d1b0%Z I : word) = Some W_5d1b0.
Proof. vm_refl. Qed.
Lemma D_5d1b0 : decode_any W_5d1b0 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 200%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_5cfec_5d280.
Module Bo_code_7662c_766cc.
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
Definition W_7662c : bv 32 := @BV 32 0xff010113%Z I.
Lemma F_7662c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7662c%Z I : word) = Some W_7662c.
Proof. vm_refl. Qed.
Lemma D_7662c : decode_any W_7662c = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4080%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76630 : bv 32 := @BV 32 0x00113423%Z I.
Lemma F_76630 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x76630%Z I : word) = Some W_76630.
Proof. vm_refl. Qed.
Lemma D_76630 : decode_any W_76630 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76634 : bv 32 := @BV 32 0x00813023%Z I.
Lemma F_76634 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x76634%Z I : word) = Some W_76634.
Proof. vm_refl. Qed.
Lemma D_76634 : decode_any W_76634 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76638 : bv 32 := @BV 32 0x00099517%Z I.
Lemma F_76638 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x76638%Z I : word) = Some W_76638.
Proof. vm_refl. Qed.
Lemma D_76638 : decode_any W_76638 = Some (Auipc (@BV 5 10%Z I) (@BV 20 153%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7663c : bv 32 := @BV 32 0x86050413%Z I.
Lemma F_7663c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7663c%Z I : word) = Some W_7663c.
Proof. vm_refl. Qed.
Lemma D_7663c : decode_any W_7663c = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 10%Z I) (@BV 12 2144%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76640 : bv 32 := @BV 32 0x00040583%Z I.
Lemma F_76640 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x76640%Z I : word) = Some W_76640.
Proof. vm_refl. Qed.
Lemma D_76640 : decode_any W_76640 = Some (Load SZ1 true (@BV 5 11%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76644 : bv 32 := @BV 32 0x00100513%Z I.
Lemma F_76644 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x76644%Z I : word) = Some W_76644.
Proof. vm_refl. Qed.
Lemma D_76644 : decode_any W_76644 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76648 : bv 32 := @BV 32 0x0230000f%Z I.
Lemma F_76648 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x76648%Z I : word) = Some W_76648.
Proof. vm_refl. Qed.
Lemma D_76648 : decode_any W_76648 = Some (Fence (@BV 4 0%Z I) (@BV 4 2%Z I) (@BV 4 3%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7664c : bv 32 := @BV 32 0x00a59a63%Z I.
Lemma F_7664c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7664c%Z I : word) = Some W_7664c.
Proof. vm_refl. Qed.
Lemma D_7664c : decode_any W_7664c = Some (Branch BC_NE (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 13 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76650 : bv 32 := @BV 32 0x00813083%Z I.
Lemma F_76650 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x76650%Z I : word) = Some W_76650.
Proof. vm_refl. Qed.
Lemma D_76650 : decode_any W_76650 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76654 : bv 32 := @BV 32 0x00013403%Z I.
Lemma F_76654 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x76654%Z I : word) = Some W_76654.
Proof. vm_refl. Qed.
Lemma D_76654 : decode_any W_76654 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76658 : bv 32 := @BV 32 0x01010113%Z I.
Lemma F_76658 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x76658%Z I : word) = Some W_76658.
Proof. vm_refl. Qed.
Lemma D_76658 : decode_any W_76658 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7665c : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_7665c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7665c%Z I : word) = Some W_7665c.
Proof. vm_refl. Qed.
Lemma D_7665c : decode_any W_7665c = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_7662c_766cc.
Require Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoRtM2SI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI.BoRtLeafI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S Bo_code_56520_5665c Bo_code_58228_58364 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI.Bo_code_7006c_706b8 Bo_code_79bf8_79d34.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Definition both_m2s_tab_55a68 : m2s_tab :=
  {| mt_base := 0x56520; mt_g_shoff := 0x105f18; mt_p_shoff := 0x10e1b8; mt_g_midbeg := 0x105f20; mt_p_midbeg := 0x10eea8;
     mt_g_midend := 0x105f28; mt_p_midend := 0x10eeb0; mt_g_hiend := 0x105f30; mt_p_hiend := 0x10eea0 |}.
Definition both_m2s_tab_57770 : m2s_tab :=
  {| mt_base := 0x58228; mt_g_shoff := 0x105f18; mt_p_shoff := 0x10e1b8; mt_g_midbeg := 0x105f20; mt_p_midbeg := 0x10eea8;
     mt_g_midend := 0x105f28; mt_p_midend := 0x10eeb0; mt_g_hiend := 0x105f30; mt_p_hiend := 0x10eea0 |}.
Definition both_m2s_tab_6dffc : m2s_tab :=
  {| mt_base := 0x6eab4; mt_g_shoff := 0x105f18; mt_p_shoff := 0x10e1b8; mt_g_midbeg := 0x105f20; mt_p_midbeg := 0x10eea8;
     mt_g_midend := 0x105f28; mt_p_midend := 0x10eeb0; mt_g_hiend := 0x105f30; mt_p_hiend := 0x10eea0 |}.
Definition both_m2s_tab_6fac4 : m2s_tab :=
  {| mt_base := 0x7057c; mt_g_shoff := 0x105f18; mt_p_shoff := 0x10e1b8; mt_g_midbeg := 0x105f20; mt_p_midbeg := 0x10eea8;
     mt_g_midend := 0x105f28; mt_p_midend := 0x10eeb0; mt_g_hiend := 0x105f30; mt_p_hiend := 0x10eea0 |}.
Definition both_m2s_tab_79140 : m2s_tab :=
  {| mt_base := 0x79bf8; mt_g_shoff := 0x105f18; mt_p_shoff := 0x10e1b8; mt_g_midbeg := 0x105f20; mt_p_midbeg := 0x10eea8;
     mt_g_midend := 0x105f28; mt_p_midend := 0x10eeb0; mt_g_hiend := 0x105f30; mt_p_hiend := 0x10eea0 |}.

Ltac tabred := (lazymatch goal with |- ?G => let G' := eval cbn [mt_base mt_g_shoff mt_p_shoff mt_g_midbeg mt_p_midbeg mt_g_midend mt_p_midend mt_g_hiend mt_p_hiend
                    both_m2s_tab_55a68 both_m2s_tab_57770 both_m2s_tab_6dffc both_m2s_tab_6fac4 both_m2s_tab_79140] in G in change_no_check G' end).

Section FPGen1.
Context {fx : FPState}.


Lemma both_m2s_tab_ok_57770 : m2s_tab_ok BSEGS both_m2s_tab_57770.
Proof using.
  split; tabred.
  - (lazymatch goal with |- ?G => let G' := eval unfold m2s_words in G in change_no_check G' end). code_ato_vm.
  - gload_tac F_58228 D_58228 F_5822c D_5822c.
  - gload_tac F_58248 D_58248 F_5824c D_5824c.
  - gload_tac F_58250 D_58250 F_58254 D_58254.
  - gload_tac F_5826c D_5826c F_58270 D_58270.
Qed.

Lemma both_m2s_tab_ok_6dffc : m2s_tab_ok BSEGS both_m2s_tab_6dffc.
Proof using.
  split; tabred.
  - (lazymatch goal with |- ?G => let G' := eval unfold m2s_words in G in change_no_check G' end). code_ato_vm.
  - gload_tac F_6eab4 D_6eab4 F_6eab8 D_6eab8.
  - gload_tac F_6ead4 D_6ead4 F_6ead8 D_6ead8.
  - gload_tac F_6eadc D_6eadc F_6eae0 D_6eae0.
  - gload_tac F_6eaf8 D_6eaf8 F_6eafc D_6eafc.
Qed.

Lemma both_m2s_tab_ok_6fac4 : m2s_tab_ok BSEGS both_m2s_tab_6fac4.
Proof using.
  split; tabred.
  - (lazymatch goal with |- ?G => let G' := eval unfold m2s_words in G in change_no_check G' end). code_ato_vm.
  - gload_tac F_7057c D_7057c F_70580 D_70580.
  - gload_tac F_7059c D_7059c F_705a0 D_705a0.
  - gload_tac F_705a4 D_705a4 F_705a8 D_705a8.
  - gload_tac F_705c0 D_705c0 F_705c4 D_705c4.
Qed.








End FPGen1.
End BoRtM2SI.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoRtRegionI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI.BoRtLeafI Bo_code_70a08_70d4c OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S BoRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Ltac tabred := (lazymatch goal with |- ?G => let G' := eval cbn [mt_base mt_g_shoff mt_p_shoff mt_g_midbeg mt_p_midbeg mt_g_midend mt_p_midend mt_g_hiend mt_p_hiend
                    rt_base rt_m2s both_m2s_tab_6fac4] in G in change_no_check G' end).

Section FPGen1.
Context {fx : FPState}.

Definition both_rip_tab : rip_tab := {| rt_base := 0x70a08; rt_m2s := both_m2s_tab_6fac4 |}.

Lemma both_rip_tab_ok : rip_tab_ok BSEGS both_rip_tab.
Proof using.
  split; (lazymatch goal with |- ?G => let G' := eval cbn [rt_base rt_m2s both_rip_tab] in G in change_no_check G' end); tabred.
  - (lazymatch goal with |- ?G => let G' := eval unfold rip_words in G in change_no_check G' end). code_ato_vm.
  - exact both_m2s_tab_ok_6fac4.
  - apply bv_eq. vm_compute. reflexivity.
  - replace (at_ (0x70a08 : word) 66768) with (0x80ed8 : word) by (apply bv_eq; vm_compute; reflexivity).
    exact both_mem_is_zero_code.
  - gload_tac F_70a34 D_70a34 F_70a38 D_70a38.
  - gload_tac F_70a54 D_70a54 F_70a58 D_70a58.
  - gload_tac F_70a5c D_70a5c F_70a60 D_70a60.
  - gload_tac F_70a78 D_70a78 F_70a7c D_70a7c.
  - gload_tac F_70a9c D_70a9c F_70aa0 D_70aa0.
  - gload_tac F_70aa4 D_70aa4 F_70aa8 D_70aa8.
  - gload_tac F_70ac0 D_70ac0 F_70ac4 D_70ac4.
  - imm_norm. lia.
Qed.

(* [comment removed for export] *)
Theorem both_region_clear : forall mem rom (beg size ra sp : word) (s0b s1b : byte) (midend : word) regs,
  ripH BSEGS both_rip_tab mem beg size ra sp s0b s1b midend ->
  getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = beg -> getr regs 11 = size ->
  exists r,
    msteps BSEGS (mkst regs (0x70a08 : word) mem rom)
                 (mkst r ra (rip_mem both_rip_tab mem sp ra (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                                     (getr regs 20) (getr regs 21) beg size) rom)
    /\ getr r 10 = Z_to_bv 64 0
    /\ regs_agree (fun r => In r rip_clob) regs r.
Proof using. exact (region_clear BSEGS both_rip_tab both_rip_tab_ok). Qed.
End FPGen1.
End BoRtRegionI.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoDrvQcSlow.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S BoRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion BoRtRegionI Bo_code_5ce30_5d514 Bo_code_5e7a4_5e804 Bo_code_5e8e0_5e938 Bo_code_5fd64_5fe74 Bo_code_5fe94_5fea8 Bo_code_600e4_600e8.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 z := (word_to_le_bytes 8 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Definition QSB : Z := 0x7fff8000.
Definition QKHIMEM : Z := 0x10007fff8000.
(* [comment removed for export] *)
Definition shok_sem (M : word -> option byte) (A N : Z) : Prop :=
  forall z, (A <= z < A + N)%Z -> exists b : byte, M (Z_to_bv 64 (QSB + z / 8)) = Some b /\ (U b = 0 \/ z mod 8 < U b <= 7)%Z.

Lemma div8_mul8_le : forall x, (0 <= x -> x / 8 * 8 <= x /\ x < x / 8 * 8 + 8)%Z.
Proof. intros x Hx. pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia. Qed.

(* [comment removed for export] *)
Lemma shok_granule0 : forall M A N g,
  shok_sem M A N -> (A <= 8 * g)%Z -> (8 * g + 8 <= A + N)%Z -> M (Z_to_bv 64 (QSB + g)) = Some (Z_to_bv 8 0).
Proof.
  intros M A N g HS H1 H2.
  destruct (HS (8 * g + 7)%Z ltac:(lia)) as (b & Hb & Hv).
  replace ((8 * g + 7) / 8)%Z with g in Hb by (apply Z.div_unique with (r := 7%Z); lia).
  rewrite Hb. f_equal. apply bv_eq.
  pose proof (bv_unsigned_in_range _ b) as Rb. change (bv_modulus 8) with 256%Z in Rb.
  replace ((8 * g + 7) mod 8)%Z with 7%Z in Hv by (apply Z.mod_unique with (q := g); lia).
  assert (Hu : U b = 0%Z) by lia.
  rewrite Z_to_bv_unsigned. change (bv_wrap 8 0) with 0%Z. exact Hu.
Qed.

Lemma rdn1_of_mem : forall (mem : word -> option byte) (a : word) (b : byte), mem a = Some b -> rdn BSEGS mem a 1 = Some [b].
Proof. intros mem a b H. cbn [rdn]. rewrite H. reflexivity. Qed.

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Lemma ripH_of_shok_gen : forall (mem : word -> option byte) (b ra : word) (A N n spz me : Z),
  (8 <= n <= 2 ^ 43)%Z -> (0 <= A <= U b)%Z -> (U b + n <= A + N)%Z -> shok_sem mem A N ->
  ((QKHIMEM <= U b /\ U b + n + 1 <= 2 ^ 47) \/ U b + n <= 0x7fff7fff)%Z ->
  rdn BSEGS mem (Z_to_bv 64 0x105f18) 8 = Some (LE8 0x10e1b8) -> rdn BSEGS mem (Z_to_bv 64 0x105f20) 8 = Some (LE8 0x10eea8) ->
  rdn BSEGS mem (Z_to_bv 64 0x105f28) 8 = Some (LE8 0x10eeb0) -> rdn BSEGS mem (Z_to_bv 64 0x105f30) 8 = Some (LE8 0x10eea0) ->
  rdn BSEGS mem (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 0x7fff8000) -> rdn BSEGS mem (Z_to_bv 64 0x10eea8) 8 = Some (LE8 0) ->
  rdn BSEGS mem (Z_to_bv 64 0x10eea0) 8 = Some (LE8 0x7fffffffffff) ->
  rdn BSEGS mem (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 me) ->
  (QKHIMEM + 80 <= spz)%Z -> (spz + 16 <= 2 ^ 47)%Z -> store_ok BSEGS mem (Z_to_bv 64 (spz - 80)) 80 = true ->
  ret_ok ra ->
  exists s0b s1b : byte, ripH BSEGS both_rip_tab mem b (Z_to_bv 64 n) ra (Z_to_bv 64 spz) s0b s1b (Z_to_bv 64 me).
Proof.
  intros mem b ra A N n spz me Hn HA HN HS Hrng C1 C2 C3 C4 C5 C6 C7 C8 Hsp1 Hsp2 Hstk Hra.
  pose proof (u64_range b) as Rb.
  assert (Un : U (Z_to_bv 64 n) = n) by (apply u64_lit; lia).
  assert (Usp : U (Z_to_bv 64 spz) = spz) by (apply u64_lit; unfold QKHIMEM in *; lia).
  destruct (HS (U b) ltac:(lia)) as (s0b & Hs0 & Hs0v).
  destruct (HS (U b + n - 1)%Z ltac:(lia)) as (s1b & Hs1 & Hs1v).
  exists s0b, s1b. split; cbn [rt_m2s rt_base both_rip_tab]; rewrite ?Un, ?Usp.
  - split; tabred; try assumption.
    + unfold m2s_cells. tabred. repeat (apply Forall_cons; [lia|]). apply Forall_nil.
    + unfold QKHIMEM in Hrng. lia.
    + unfold QKHIMEM in Hrng. lia.
  - unfold m2s_cells. tabred. unfold QKHIMEM in Hsp1. repeat (apply Forall_cons; [lia|]). apply Forall_nil.
  - lia.
  - unfold QKHIMEM in Hrng. lia.
  - lia.
  - apply rdn1_of_mem. unfold Sh. rewrite <- Hs0. f_equal. f_equal. unfold QSB. lia.
  - lia.
  - apply rdn1_of_mem. unfold Sh. rewrite <- Hs1. f_equal. f_equal. unfold QSB. lia.
  - lia.
  - intros a Ha. unfold Sh, up8, down8 in Ha.
    replace a with (Z_to_bv 64 (QSB + (U a - QSB))) by (rewrite <- (Z_to_bv_bv_unsigned _ a) at 2; f_equal; lia).
    apply rdn1_of_mem. apply (shok_granule0 mem A N (U a - QSB) HS).
    + pose proof (div8_mul8_le (U b + 7) ltac:(lia)) as [D1 D2]. unfold QSB in *.
      assert ((U b + 7) / 8 * 8 / 8 = (U b + 7) / 8)%Z by (apply Z.div_mul; lia). lia.
    + pose proof (div8_mul8_le (U b + n) ltac:(lia)) as [D1 D2]. unfold QSB in *.
      assert ((U b + n) / 8 * 8 / 8 = (U b + n) / 8)%Z by (apply Z.div_mul; lia). lia.
  - unfold QKHIMEM in Hsp1. lia.
  - replace (at_ (Z_to_bv 64 spz) (-80)) with (Z_to_bv 64 (spz - 80)); [exact Hstk|].
    apply bv_eq. rewrite at_u by (rewrite Usp; unfold QKHIMEM in Hsp1; lia). rewrite Usp. apply u64_lit. unfold QKHIMEM in Hsp1. lia.
  - exact Hra.
Qed.
Lemma ripH_of_shok : forall (mem : word -> option byte) (b ra : word) (A N n spz me : Z),
  (65 <= n <= 2 ^ 43)%Z -> (0 <= A <= U b)%Z -> (U b + n + 1 <= A + N)%Z -> (A + N <= 2 ^ 47)%Z -> shok_sem mem A N ->
  (QKHIMEM <= U b \/ U b + n <= 0x7fff7fff)%Z ->
  rdn BSEGS mem (Z_to_bv 64 0x105f18) 8 = Some (LE8 0x10e1b8) -> rdn BSEGS mem (Z_to_bv 64 0x105f20) 8 = Some (LE8 0x10eea8) ->
  rdn BSEGS mem (Z_to_bv 64 0x105f28) 8 = Some (LE8 0x10eeb0) -> rdn BSEGS mem (Z_to_bv 64 0x105f30) 8 = Some (LE8 0x10eea0) ->
  rdn BSEGS mem (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 0x7fff8000) -> rdn BSEGS mem (Z_to_bv 64 0x10eea8) 8 = Some (LE8 0) ->
  rdn BSEGS mem (Z_to_bv 64 0x10eea0) 8 = Some (LE8 0x7fffffffffff) ->
  rdn BSEGS mem (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 me) ->
  (QKHIMEM + 80 <= spz)%Z -> (spz + 16 <= 2 ^ 47)%Z -> store_ok BSEGS mem (Z_to_bv 64 (spz - 80)) 80 = true ->
  ret_ok ra ->
  exists s0b s1b : byte, ripH BSEGS both_rip_tab mem b (Z_to_bv 64 n) ra (Z_to_bv 64 spz) s0b s1b (Z_to_bv 64 me).
Proof.
  intros mem b ra A N n spz me Hn HA0 HAN H47 HS Hrng.
  apply (ripH_of_shok_gen mem b ra A N n spz me); try assumption; try lia.
Qed.

(* [comment removed for export] *)
Lemma rip_mem_post : forall (mem : word -> option byte) (sp ra s0 s1 s2 s3 s4 s5 beg size : word),
  (80 <= U sp)%Z ->
  (forall x : word, (U x < U sp - 80 \/ U sp <= U x)%Z -> rip_mem both_rip_tab mem sp ra s0 s1 s2 s3 s4 s5 beg size x = mem x)
  /\ mem_grows mem (rip_mem both_rip_tab mem sp ra s0 s1 s2 s3 s4 s5 beg size).
Proof.
  intros mem sp ra s0 s1 s2 s3 s4 s5 beg size Hsp. split.
  - intros x Hx. apply rip_mem_outside; assumption.
  - unfold rip_mem, ps_frame. destruct (Z.ltb _ _); repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.
Qed.

(* [comment removed for export] *)
Lemma qc_slow_strnlen : forall (regs : bvmap 5 word) (mem rom : word -> option byte) (b : word) (A N n spz : Z),
  getr regs 18 = b -> getr regs 9 = Z_to_bv 64 n -> getr regs 2 = Z_to_bv 64 spz ->
  (65 <= n <= 2 ^ 43)%Z -> (0 <= A <= U b)%Z -> (U b + n + 1 <= A + N)%Z -> (A + N <= 2 ^ 47)%Z -> shok_sem mem A N ->
  (QKHIMEM <= U b \/ U b + n <= 0x7fff7fff)%Z ->
  rdn BSEGS mem (Z_to_bv 64 0x105f18) 8 = Some (LE8 0x10e1b8) -> rdn BSEGS mem (Z_to_bv 64 0x105f20) 8 = Some (LE8 0x10eea8) ->
  rdn BSEGS mem (Z_to_bv 64 0x105f28) 8 = Some (LE8 0x10eeb0) -> rdn BSEGS mem (Z_to_bv 64 0x105f30) 8 = Some (LE8 0x10eea0) ->
  rdn BSEGS mem (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 0x7fff8000) -> rdn BSEGS mem (Z_to_bv 64 0x10eea8) 8 = Some (LE8 0) ->
  rdn BSEGS mem (Z_to_bv 64 0x10eea0) 8 = Some (LE8 0x7fffffffffff) ->
  (exists me : Z, rdn BSEGS mem (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 me)) ->
  (QKHIMEM + 80 <= spz)%Z -> (spz + 16 <= 2 ^ 47)%Z -> store_ok BSEGS mem (Z_to_bv 64 (spz - 80)) 80 = true ->
  exists r mem', msteps BSEGS (mkst regs (0x5d2fc : word) mem rom) (mkst r (0x5d344 : word) mem' rom)
    /\ regs_agree (fun x => In x [1; 5; 11; 12; 13; 14; 15; 16; 17; 18; 22]%list) regs r
    /\ (forall x : word, (U x < spz - 80 \/ spz <= U x)%Z -> mem' x = mem x) /\ mem_grows mem mem'.
Proof.
  intros regs mem rom b A N n spz Rb Rn Rsp Hn HA0 HAN H47 HS Hrng C1 C2 C3 C4 C5 C6 C7 [me C8] Hsp1 Hsp2 Hstk.
  assert (RA : ret_ok (Z_to_bv 64 0x5d440)) by (apply bv_eq; vm_compute; reflexivity).
  destruct (ripH_of_shok mem b (Z_to_bv 64 0x5d440) A N n spz me Hn HA0 HAN H47 HS Hrng C1 C2 C3 C4 C5 C6 C7 C8 Hsp1 Hsp2 Hstk RA) as (s0b & s1b & PH).
  set (r1 := regupd (regupd (regupd (regupd (regupd regs 11 (Z_to_bv 64 (n - 65))) 12 (Z_to_bv 64 (2 ^ 64 - 65))) 22 (getr regs 10)) 10 b) 11 (Z_to_bv 64 n)).
  set (r1' := regupd r1 1 (Z_to_bv 64 0x5d440)).
  destruct (both_region_clear mem rom b (Z_to_bv 64 n) (Z_to_bv 64 0x5d440) (Z_to_bv 64 spz) s0b s1b (Z_to_bv 64 me) r1' PH)
    as (r2 & RUN2 & A10 & AG2); [subst r1' r1; gres; reflexivity | subst r1' r1; gres; exact Rsp | subst r1' r1; gres; reflexivity | subst r1' r1; gres; reflexivity |].
  assert (Usp : U (Z_to_bv 64 spz) = spz) by (apply u64_lit; unfold QKHIMEM in Hsp1; lia).
  destruct (rip_mem_post mem (Z_to_bv 64 spz) (Z_to_bv 64 0x5d440) (getr r1' 8) (getr r1' 9) (getr r1' 18) (getr r1' 19) (getr r1' 20) (getr r1' 21) b (Z_to_bv 64 n)
              ltac:(rewrite Usp; unfold QKHIMEM in Hsp1; lia)) as [MO MG].
  rewrite Usp in MO.
  eexists. eexists. split; [|split; [|split; [exact MO | exact MG]]].
  - av F_5d2fc D_5d2fc (Z_to_bv 64 (n - 65)) ltac:(unfold v_addi; unorm; f_equal; lia).      (* [comment removed for export] *)
    av F_5d300 D_5d300 (Z_to_bv 64 (2 ^ 64 - 65)) ltac:(apply bv_eq; vm_compute; reflexivity).  (* [comment removed for export] *)
    ab_tk F_5d304 D_5d304 ltac:(condz).               (* [comment removed for export] *)
    ab_tk F_5d3f4 D_5d3f4 ltac:(condz).               (* [comment removed for export] *)
    an F_5d430 D_5d430.                               (* [comment removed for export] *)
    an F_5d434 D_5d434.                               (* [comment removed for export] *)
    an F_5d438 D_5d438.                               (* [comment removed for export] *)
    an F_5d43c D_5d43c.                               (* [comment removed for export] *)
    change (regupd _ 1 _) with r1'.
    eapply msteps_trans; [exact RUN2|]. lit_pc.
    an F_5d440 D_5d440.                               (* [comment removed for export] *)
    an F_5d444 D_5d444.                               (* [comment removed for export] *)
    ab_tk F_5d448 D_5d448 ltac:(condz).               (* [comment removed for export] *)
    apply mst_refl.
  - intros x Hx.
    assert (X : x <> 1 /\ x <> 5 /\ x <> 11 /\ x <> 12 /\ x <> 13 /\ x <> 14 /\ x <> 15 /\ x <> 16 /\ x <> 17 /\ x <> 18 /\ x <> 22)
      by (repeat split; intros ->; apply Hx; cbn; tauto).
    destruct X as (X1 & X5 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & X18 & X22).
    destruct (bv_eq_dec _ x 10) as [->|N10].
    + gres. rewrite (AG2 22) by notin. subst r1' r1. gres. reflexivity.
    + rewrite !getr_other by assumption.
      rewrite (AG2 x) by (unfold rip_clob; cbn [In]; intros Hc; repeat (destruct Hc as [<-|Hc]; [congruence|]); exact Hc).
      subst r1' r1. rewrite !getr_other by assumption. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma qc_slow_memchr : forall (regs : bvmap 5 word) (mem rom : word -> option byte) (b : word) (A N n spz : Z),
  getr regs 18 = b -> getr regs 9 = Z_to_bv 64 n -> getr regs 2 = Z_to_bv 64 spz ->
  (65 <= n <= 2 ^ 43)%Z -> (0 <= A <= U b)%Z -> (U b + n + 1 <= A + N)%Z -> (A + N <= 2 ^ 47)%Z -> shok_sem mem A N ->
  (QKHIMEM <= U b \/ U b + n <= 0x7fff7fff)%Z ->
  rdn BSEGS mem (Z_to_bv 64 0x105f18) 8 = Some (LE8 0x10e1b8) -> rdn BSEGS mem (Z_to_bv 64 0x105f20) 8 = Some (LE8 0x10eea8) ->
  rdn BSEGS mem (Z_to_bv 64 0x105f28) 8 = Some (LE8 0x10eeb0) -> rdn BSEGS mem (Z_to_bv 64 0x105f30) 8 = Some (LE8 0x10eea0) ->
  rdn BSEGS mem (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 0x7fff8000) -> rdn BSEGS mem (Z_to_bv 64 0x10eea8) 8 = Some (LE8 0) ->
  rdn BSEGS mem (Z_to_bv 64 0x10eea0) 8 = Some (LE8 0x7fffffffffff) ->
  (exists me : Z, rdn BSEGS mem (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 me)) ->
  (QKHIMEM + 80 <= spz)%Z -> (spz + 16 <= 2 ^ 47)%Z -> store_ok BSEGS mem (Z_to_bv 64 (spz - 80)) 80 = true ->
  exists r mem', msteps BSEGS (mkst regs (0x5e7ac : word) mem rom) (mkst r (0x5e7f4 : word) mem' rom)
    /\ regs_agree (fun x => In x [1; 5; 11; 12; 13; 14; 15; 16; 17; 18; 21]%list) regs r
    /\ (forall x : word, (U x < spz - 80 \/ spz <= U x)%Z -> mem' x = mem x) /\ mem_grows mem mem'.
Proof.
  intros regs mem rom b A N n spz Rb Rn Rsp Hn HA0 HAN H47 HS Hrng C1 C2 C3 C4 C5 C6 C7 [me C8] Hsp1 Hsp2 Hstk.
  assert (RA : ret_ok (Z_to_bv 64 0x5e92c)) by (apply bv_eq; vm_compute; reflexivity).
  destruct (ripH_of_shok mem b (Z_to_bv 64 0x5e92c) A N n spz me Hn HA0 HAN H47 HS Hrng C1 C2 C3 C4 C5 C6 C7 C8 Hsp1 Hsp2 Hstk RA) as (s0b & s1b & PH).
  set (r1 := regupd (regupd (regupd (regupd (regupd regs 11 (Z_to_bv 64 (n - 65))) 12 (Z_to_bv 64 (2 ^ 64 - 65))) 21 (getr regs 10)) 10 b) 11 (Z_to_bv 64 n)).
  set (r1' := regupd r1 1 (Z_to_bv 64 0x5e92c)).
  destruct (both_region_clear mem rom b (Z_to_bv 64 n) (Z_to_bv 64 0x5e92c) (Z_to_bv 64 spz) s0b s1b (Z_to_bv 64 me) r1' PH)
    as (r2 & RUN2 & A10 & AG2); [subst r1' r1; gres; reflexivity | subst r1' r1; gres; exact Rsp | subst r1' r1; gres; reflexivity | subst r1' r1; gres; reflexivity |].
  assert (Usp : U (Z_to_bv 64 spz) = spz) by (apply u64_lit; unfold QKHIMEM in Hsp1; lia).
  destruct (rip_mem_post mem (Z_to_bv 64 spz) (Z_to_bv 64 0x5e92c) (getr r1' 8) (getr r1' 9) (getr r1' 18) (getr r1' 19) (getr r1' 20) (getr r1' 21) b (Z_to_bv 64 n)
              ltac:(rewrite Usp; unfold QKHIMEM in Hsp1; lia)) as [MO MG].
  rewrite Usp in MO.
  eexists. eexists. split; [|split; [|split; [exact MO | exact MG]]].
  - av F_5e7ac D_5e7ac (Z_to_bv 64 (n - 65)) ltac:(unfold v_addi; unorm; f_equal; lia).      (* [comment removed for export] *)
    av F_5e7b0 D_5e7b0 (Z_to_bv 64 (2 ^ 64 - 65)) ltac:(apply bv_eq; vm_compute; reflexivity).  (* [comment removed for export] *)
    ab_tk F_5e7b4 D_5e7b4 ltac:(condz).               (* [comment removed for export] *)
    ab_tk F_5e8e0 D_5e8e0 ltac:(condz).               (* [comment removed for export] *)
    an F_5e91c D_5e91c.                               (* [comment removed for export] *)
    an F_5e920 D_5e920.                               (* [comment removed for export] *)
    an F_5e924 D_5e924.                               (* [comment removed for export] *)
    an F_5e928 D_5e928.                               (* [comment removed for export] *)
    change (regupd _ 1 _) with r1'.
    eapply msteps_trans; [exact RUN2|]. lit_pc.
    an F_5e92c D_5e92c.                               (* [comment removed for export] *)
    an F_5e930 D_5e930.                               (* [comment removed for export] *)
    ab_tk F_5e934 D_5e934 ltac:(condz).               (* [comment removed for export] *)
    apply mst_refl.
  - intros x Hx.
    assert (X : x <> 1 /\ x <> 5 /\ x <> 11 /\ x <> 12 /\ x <> 13 /\ x <> 14 /\ x <> 15 /\ x <> 16 /\ x <> 17 /\ x <> 18 /\ x <> 21)
      by (repeat split; intros ->; apply Hx; cbn; tauto).
    destruct X as (X1 & X5 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & X18 & X21).
    destruct (bv_eq_dec _ x 10) as [->|N10].
    + gres. rewrite (AG2 21) by notin. subst r1' r1. gres. reflexivity.
    + rewrite !getr_other by assumption.
      rewrite (AG2 x) by (unfold rip_clob; cbn [In]; intros Hc; repeat (destruct Hc as [<-|Hc]; [congruence|]); exact Hc).
      subst r1' r1. rewrite !getr_other by assumption. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma qc_slow_printf : forall (regs : bvmap 5 word) (mem rom : word -> option byte) (b : word) (A N n spz : Z),
  getr regs 22 = b -> getr regs 23 = Z_to_bv 64 n -> getr regs 2 = Z_to_bv 64 spz ->
  (65 <= n <= 2 ^ 43)%Z -> (0 <= A <= U b)%Z -> (U b + n + 1 <= A + N)%Z -> (A + N <= 2 ^ 47)%Z -> shok_sem mem A N ->
  (QKHIMEM <= U b \/ U b + n <= 0x7fff7fff)%Z ->
  rdn BSEGS mem (Z_to_bv 64 0x105f18) 8 = Some (LE8 0x10e1b8) -> rdn BSEGS mem (Z_to_bv 64 0x105f20) 8 = Some (LE8 0x10eea8) ->
  rdn BSEGS mem (Z_to_bv 64 0x105f28) 8 = Some (LE8 0x10eeb0) -> rdn BSEGS mem (Z_to_bv 64 0x105f30) 8 = Some (LE8 0x10eea0) ->
  rdn BSEGS mem (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 0x7fff8000) -> rdn BSEGS mem (Z_to_bv 64 0x10eea8) 8 = Some (LE8 0) ->
  rdn BSEGS mem (Z_to_bv 64 0x10eea0) 8 = Some (LE8 0x7fffffffffff) ->
  (exists me : Z, rdn BSEGS mem (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 me)) ->
  (QKHIMEM + 80 <= spz)%Z -> (spz + 16 <= 2 ^ 47)%Z -> store_ok BSEGS mem (Z_to_bv 64 (spz - 80)) 80 = true ->
  exists r mem', msteps BSEGS (mkst regs (0x5fe1c : word) mem rom) (mkst r (0x5fd70 : word) mem' rom)
    /\ regs_agree (fun x => In x [1; 5; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs r
    /\ (forall x : word, (U x < spz - 80 \/ spz <= U x)%Z -> mem' x = mem x) /\ mem_grows mem mem'.
Proof.
  intros regs mem rom b A N n spz Rb Rn Rsp Hn HA0 HAN H47 HS Hrng C1 C2 C3 C4 C5 C6 C7 [me C8] Hsp1 Hsp2 Hstk.
  assert (RA : ret_ok (Z_to_bv 64 0x5fea4)) by (apply bv_eq; vm_compute; reflexivity).
  destruct (ripH_of_shok mem b (Z_to_bv 64 0x5fea4) A N n spz me Hn HA0 HAN H47 HS Hrng C1 C2 C3 C4 C5 C6 C7 C8 Hsp1 Hsp2 Hstk RA) as (s0b & s1b & PH).
  set (r1 := regupd (regupd (regupd (regupd regs 10 (Z_to_bv 64 (n - 65))) 11 (Z_to_bv 64 (2 ^ 64 - 65))) 10 b) 11 (Z_to_bv 64 n)).
  set (r1' := regupd r1 1 (Z_to_bv 64 0x5fea4)).
  destruct (both_region_clear mem rom b (Z_to_bv 64 n) (Z_to_bv 64 0x5fea4) (Z_to_bv 64 spz) s0b s1b (Z_to_bv 64 me) r1' PH)
    as (r2 & RUN2 & A10 & AG2); [subst r1' r1; gres; reflexivity | subst r1' r1; gres; exact Rsp | subst r1' r1; gres; reflexivity | subst r1' r1; gres; reflexivity |].
  assert (Usp : U (Z_to_bv 64 spz) = spz) by (apply u64_lit; unfold QKHIMEM in Hsp1; lia).
  destruct (rip_mem_post mem (Z_to_bv 64 spz) (Z_to_bv 64 0x5fea4) (getr r1' 8) (getr r1' 9) (getr r1' 18) (getr r1' 19) (getr r1' 20) (getr r1' 21) b (Z_to_bv 64 n)
              ltac:(rewrite Usp; unfold QKHIMEM in Hsp1; lia)) as [MO MG].
  rewrite Usp in MO.
  eexists. eexists. split; [|split; [|split; [exact MO | exact MG]]].
  - av F_5fe1c D_5fe1c (Z_to_bv 64 (n - 65)) ltac:(unfold v_addi; unorm; f_equal; lia).      (* [comment removed for export] *)
    av F_5fe20 D_5fe20 (Z_to_bv 64 (2 ^ 64 - 65)) ltac:(apply bv_eq; vm_compute; reflexivity).  (* [comment removed for export] *)
    ab_tk F_5fe24 D_5fe24 ltac:(condz).               (* [comment removed for export] *)
    ab_tk F_600e4 D_600e4 ltac:(condz).               (* [comment removed for export] *)
    an F_5fe98 D_5fe98.                               (* [comment removed for export] *)
    an F_5fe9c D_5fe9c.                               (* [comment removed for export] *)
    an F_5fea0 D_5fea0.                               (* [comment removed for export] *)
    change (regupd _ 1 _) with r1'.
    eapply msteps_trans; [exact RUN2|]. lit_pc.
    ab_tk F_5fea4 D_5fea4 ltac:(condz).               (* [comment removed for export] *)
    apply mst_refl.
  - intros x Hx.
    assert (X : x <> 1 /\ x <> 5 /\ x <> 10 /\ x <> 11 /\ x <> 12 /\ x <> 13 /\ x <> 14 /\ x <> 15 /\ x <> 16 /\ x <> 17)
      by (repeat split; intros ->; apply Hx; cbn; tauto).
    destruct X as (X1 & X5 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17).
    rewrite (AG2 x) by (unfold rip_clob; cbn [In]; intros Hc; repeat (destruct Hc as [<-|Hc]; [congruence|]); exact Hc).
    subst r1' r1. rewrite !getr_other by assumption. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma region_call_clear : forall (regs : bvmap 5 word) (mem rom : word -> option byte) (b ra : word) (n spz : Z),
  getr regs 1 = ra -> ret_ok ra -> getr regs 10 = b -> getr regs 11 = Z_to_bv 64 n -> getr regs 2 = Z_to_bv 64 spz ->
  (8 <= n <= 2 ^ 43)%Z -> shok_sem mem (U b) n ->
  ((QKHIMEM <= U b /\ U b + n + 1 <= 2 ^ 47) \/ U b + n <= 0x7fff7fff)%Z ->
  rdn BSEGS mem (Z_to_bv 64 0x105f18) 8 = Some (LE8 0x10e1b8) -> rdn BSEGS mem (Z_to_bv 64 0x105f20) 8 = Some (LE8 0x10eea8) ->
  rdn BSEGS mem (Z_to_bv 64 0x105f28) 8 = Some (LE8 0x10eeb0) -> rdn BSEGS mem (Z_to_bv 64 0x105f30) 8 = Some (LE8 0x10eea0) ->
  rdn BSEGS mem (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 0x7fff8000) -> rdn BSEGS mem (Z_to_bv 64 0x10eea8) 8 = Some (LE8 0) ->
  rdn BSEGS mem (Z_to_bv 64 0x10eea0) 8 = Some (LE8 0x7fffffffffff) ->
  (exists me : Z, rdn BSEGS mem (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 me)) ->
  (QKHIMEM + 80 <= spz)%Z -> (spz + 16 <= 2 ^ 47)%Z -> store_ok BSEGS mem (Z_to_bv 64 (spz - 80)) 80 = true ->
  exists r mem', msteps BSEGS (mkst regs (0x70a08 : word) mem rom) (mkst r ra mem' rom)
    /\ getr r 10 = Z_to_bv 64 0 /\ regs_agree (fun x => In x rip_clob) regs r
    /\ (forall x : word, (U x < spz - 80 \/ spz <= U x)%Z -> mem' x = mem x) /\ mem_grows mem mem'.
Proof.
  intros regs mem rom b ra n spz R1 RA R10 R11 Rsp Hn HS Hrng C1 C2 C3 C4 C5 C6 C7 [me C8] Hsp1 Hsp2 Hstk.
  pose proof (u64_range b) as Rb.
  destruct (ripH_of_shok_gen mem b ra (U b) n n spz me Hn ltac:(lia) ltac:(lia) HS Hrng C1 C2 C3 C4 C5 C6 C7 C8 Hsp1 Hsp2 Hstk RA) as (s0b & s1b & PH).
  destruct (both_region_clear mem rom b (Z_to_bv 64 n) ra (Z_to_bv 64 spz) s0b s1b (Z_to_bv 64 me) regs PH R1 Rsp R10 R11) as (r2 & RUN2 & A10 & AG2).
  assert (Usp : U (Z_to_bv 64 spz) = spz) by (apply u64_lit; unfold QKHIMEM in Hsp1; lia).
  destruct (rip_mem_post mem (Z_to_bv 64 spz) ra (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) b (Z_to_bv 64 n)
              ltac:(rewrite Usp; unfold QKHIMEM in Hsp1; lia)) as [MO MG].
  rewrite Usp in MO.
  exists r2. eexists. split; [exact RUN2|]. split; [exact A10|]. split; [exact AG2|]. split; [exact MO | exact MG].
Qed.

End FPGen.
End BoDrvQcSlow.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemchr OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStrlen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoRtStrlenI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib Bo_code_fc5e4_fc674 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemchr OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStrlen.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Definition both_strlen_tab : strlen_tab := {| st_base := 0xfc5d8; st_cM := 0x10400; st_cH := 0x103e0 |}.

Section FPGen1.
Context {fx : FPState}.

Lemma both_sl_consts : sl_consts BSEGS (0xfc5d8 : word) 0x10400 0x103e0.
Proof using.
  (lazymatch goal with |- ?G => let G' := eval unfold sl_consts in G in change_no_check G' end). wd_eexists. wd_eexists. intros regs mem rom vM vH RM RH.
  replace (at_ (0xfc5d8 : word) 60) with (0xfc614 : word) by (apply bv_eq; vm_compute; reflexivity).
  (chain_step; [ reflexivity | eapply step_auipc; [exact F_fc620 | reflexivity | exact D_fc620] | step_simpl ]).
  gres; imm_norm; vals_lit.
  (chain_step; [ reflexivity | eapply step_auipc; [exact F_fc624 | reflexivity | exact D_fc624] | step_simpl ]).
  gres; imm_norm; vals_lit.
  (chain_step;
   [ reflexivity
   | eapply step_ld with (bs := word_to_le_bytes 8 vM) (v := vM);
     [exact F_fc628 | reflexivity | exact D_fc628 | | apply bytes_le_to_Z_8];
     gres; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_auipc, v_addi in G in change_no_check G' end); vals_lit; rdn_lit_exact RM
   | step_simpl ]).
  (chain_step;
   [ reflexivity
   | eapply step_ld with (bs := word_to_le_bytes 8 vH) (v := vH);
     [exact F_fc62c | reflexivity | exact D_fc62c | | apply bytes_le_to_Z_8];
     gres; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_auipc, v_addi in G in change_no_check G' end); vals_lit; rdn_lit_exact RH
   | step_simpl ]).
  close_refl.
Qed.

Lemma both_strlen_tab_ok : strlen_tab_ok BSEGS both_strlen_tab.
Proof using.
  split; (lazymatch goal with |- ?G => let G' := eval cbn [st_base st_cM st_cH both_strlen_tab] in G in change_no_check G' end).
  - (lazymatch goal with |- ?G => let G' := eval unfold mstrlen_words in G in change_no_check G' end). code_ato_vm.
  - exact both_sl_consts.
Qed.

End FPGen1.
End BoRtStrlenI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemchr OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI.BoRtLeafI Bo_code_5cfec_5d280 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT.Bo_code_7571c_75734 Bo_code_7662c_766cc OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S BoRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion BoRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemchr OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStrlen BoRtStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA.AsRtXStrlen.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Definition both_xstrlen_tab : xstrlen_tab :=
  {| xs_base := 0x5cfec; xs_rip := both_rip_tab; xs_sl := both_strlen_tab; xs_c_rsl := 0x107cd8;
     xs_g_cf := 0x105f08; xs_p_cf := 0x19fce8; xs_c_inited := 0x10ee98 |}.

Section FPGen1.
Context {fx : FPState}.

Ltac lit a v := replace (at_ (0x5cfec : word) a) with v by (apply bv_eq; vm_compute; reflexivity).

(* [comment removed for export] *)
Lemma both_inited_run : asan_inited_call BSEGS (0x7571c : word) 0x10ee98.
Proof using.
  intros regs mem rom ra Rd Hret H1.
  (chain_step; [ reflexivity | eapply step_auipc; [exact F_7571c | reflexivity | exact D_7571c] | step_simpl ]).
  gres; imm_norm; vals_lit.
  (chain_step;
   [ reflexivity
   | eapply step_lb; [exact F_75720 | reflexivity | exact D_75720 | ];
     gres; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_auipc, v_addi in G in change_no_check G' end); vals_lit; rdn_lit_exact Rd
   | step_simpl ]).
  gres. try rewrite (v_lb_small (Z_to_bv 8 1)) by (vm_compute; reflexivity).
  afence F_75724 D_75724.
  an F_75728 D_75728.                                   (* [comment removed for export] *)
  an F_7572c D_7572c.                                   (* [comment removed for export] *)
  aret F_75730 D_75730 ra.                              (* [comment removed for export] *)
  rewrite ?regupd_regupd_same.
  lazymatch goal with |- msteps _ (mkst (regupd _ 10 ?v) _ _ _) _ =>
    replace v with (Z_to_bv 64 1 : word) by (apply bv_eq; vm_compute; reflexivity) end.
  wd_refl.
Qed.

(* [comment removed for export] *)
Lemma try_asan_init_run : try_asan_init_call BSEGS (0x7662c : word) 0x10ee98.
Proof using.
  intros regs mem rom ra Rd Hret H1 Hc0 Hdisj H16 H64 Hstk.
  pose proof (u64_range (getr regs 2)) as Hspr.
  wd_eexists. split; [|split].
  - an F_7662c D_7662c.                                 (* [comment removed for export] *)
    chain_step; [reflexivity
      | eapply step_sd_at with (a := at_ (getr regs 2) (-8));
        [exact F_76630 | reflexivity | exact D_76630
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | eapply (store_ok_sub BSEGS mem (at_ (getr regs 2) (-16)) _ 16); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia] ]
      | step_simpl]; vn.                                (* [comment removed for export] *)
    chain_step; [reflexivity
      | eapply step_sd_at with (a := at_ (getr regs 2) (-16));
        [exact F_76634 | reflexivity | exact D_76634
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | eapply store_ok_mono; [apply wbytes_grows|];
          eapply (store_ok_sub BSEGS mem (at_ (getr regs 2) (-16)) _ 16); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia] ]
      | step_simpl]; vn.                                (* [comment removed for export] *)
    change (wbytes _ _ _) with (tai_mem mem (getr regs 2) ra (getr regs 8)).
    (chain_step; [ reflexivity | eapply step_auipc; [exact F_76638 | reflexivity | exact D_76638] | step_simpl ]).
    gres; imm_norm; vals_lit.
    an F_7663c D_7663c.                                 (* [comment removed for export] *)
    chain_step; [reflexivity
      | eapply step_lb; [exact F_76640 | reflexivity | exact D_76640 | ];
        gres; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_auipc, v_addi in G in change_no_check G' end); vals_lit;
        lazymatch goal with |- rdn _ _ ?a _ = _ =>
          replace a with (Z_to_bv 64 0x10ee98 : word) by (apply bv_eq; vm_compute; reflexivity) end;
        (lazymatch goal with |- ?G => let G' := eval unfold tai_mem in G in change_no_check G' end); rewrite !rdn_wbytes_out;
          first [ exact Rd
                | (wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); wd_ulia) ]
      | step_simpl]; vn.                                (* [comment removed for export] *)
    try rewrite (v_lb_small (Z_to_bv 8 1)) by (vm_compute; reflexivity).
    an F_76644 D_76644.                                 (* [comment removed for export] *)
    afence F_76648 D_76648.
    ab_ft F_7664c D_7664c ltac:(vals_lit; condz).      (* [comment removed for export] *)
    Ltac fld F D vv :=
      chain_step; [reflexivity
        | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
          [exact F | reflexivity | exact D
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold tai_mem in G in change_no_check G' end); rd8_chain
          | apply bytes_le_to_Z_8]
        | step_simpl]; vn.
    fld F_76650 D_76650 ra.                             (* [comment removed for export] *)
    fld F_76654 D_76654 (getr regs 8).                  (* [comment removed for export] *)
    an F_76658 D_76658.                                 (* [comment removed for export] *)
    aret F_7665c D_7665c ra.                            (* [comment removed for export] *)
    lazymatch goal with |- msteps _ (mkst _ _ _ _) (mkst _ ?p _ _) => idtac end.
    wd_refl.
  - gres. apply bv_eq. vm_compute. reflexivity.
  - intros x X10 X11. gres.
    destruct (decide (x = 2)) as [->|N2]; [gres; rwH; rewrite ?at_addi; zlit_at; first [reflexivity | symmetry; apply at_0 | apply bv_eq; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]] |].
    destruct (decide (x = 8)) as [->|N8]; [gres; reflexivity|].
    destruct (decide (x = 1)) as [->|N1]; [gres; symmetry; exact H1|].
    rewrite !getr_other by (first [exact N2 | exact N8 | exact N1 | exact X10 | exact X11 | (intros E; discriminate E)]). reflexivity.
Qed.

Lemma both_xstrlen_tab_ok : xstrlen_tab_ok BSEGS both_xstrlen_tab.
Proof using.
  split; (lazymatch goal with |- ?G => let G' := eval cbn [xs_base xs_rip xs_sl xs_c_rsl xs_g_cf xs_p_cf xs_c_inited both_xstrlen_tab rt_base rt_m2s both_rip_tab mt_g_shoff both_m2s_tab_6fac4 st_base both_strlen_tab] in G in change_no_check G' end).
  - (lazymatch goal with |- ?G => let G' := eval unfold xstrlen_words in G in change_no_check G' end). code_ato_vm.
  - exact both_rip_tab_ok.
  - apply bv_eq; vm_compute; reflexivity.
  - exact both_strlen_tab_ok.
  - apply ret_ok_even. vm_compute. reflexivity.
  - lit 100144%Z (0x7571c : word). exact both_inited_run.
  - lit 104000%Z (0x7662c : word). exact try_asan_init_run.
  - gload_tac F_5d028 D_5d028 F_5d02c D_5d02c.
  - gload_tac F_5d040 D_5d040 F_5d044 D_5d044.
  - lit 128%Z (0x5d06c : word). gload_tac F_5d06c D_5d06c F_5d070 D_5d070.
  - lit 180%Z (0x5d0a0 : word). lit 400%Z (0x5d17c : word). eapply (gbnez_of BSEGS _ _ _ _ _ F_5d0a0 eq_refl D_5d0a0). apply bv_eq; vm_compute; reflexivity.
  - lit 452%Z (0x5d1b0 : word). lit 652%Z (0x5d278 : word). eapply (gbeqz_of BSEGS _ _ _ _ _ F_5d1b0 eq_refl D_5d1b0). apply bv_eq; vm_compute; reflexivity.
  - imm_norm. split; [vm_compute; reflexivity | lia].
Qed.


End FPGen1.
