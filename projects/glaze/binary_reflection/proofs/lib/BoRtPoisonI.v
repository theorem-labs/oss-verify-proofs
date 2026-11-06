(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.InstrEnc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Bo_code_5ec80_5eef0.
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






End Bo_code_5ec80_5eef0.
Module Bo_code_70e54_70e84.
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
Definition W_70e54 : bv 32 := @BV 32 0x00095617%Z I.
Lemma F_70e54 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x70e54%Z I : word) = Some W_70e54.
Proof. vm_refl. Qed.
Lemma D_70e54 : decode_any W_70e54 = Some (Auipc (@BV 5 12%Z I) (@BV 20 149%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70e58 : bv 32 := @BV 32 0x0e463603%Z I.
Lemma F_70e58 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x70e58%Z I : word) = Some W_70e58.
Proof. vm_refl. Qed.
Lemma D_70e58 : decode_any W_70e58 = Some (Load SZ8 true (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 228%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70e64 : bv 32 := @BV 32 0x0f500593%Z I.
Lemma F_70e64 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x70e64%Z I : word) = Some W_70e64.
Proof. vm_refl. Qed.
Lemma D_70e64 : decode_any W_70e64 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 245%Z I), 4%Z).
Proof. vm_refl. Qed.









End Bo_code_70e54_70e84.
Module Bo_code_7006c_706b8.
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
Lemma F_70074 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x70074%Z I : word) = Some W_70074.
Proof. vm_refl. Qed.
Lemma D_70074 : decode_any W_70074 = Some (Fence (@BV 4 0%Z I) (@BV 4 2%Z I) (@BV 4 3%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70078 : bv 32 := @BV 32 0x00a03533%Z I.
Lemma F_70078 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x70078%Z I : word) = Some W_70078.
Proof. vm_refl. Qed.
Lemma D_70078 : decode_any W_70078 = Some (Op ALU_SLTU (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7007c : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_7007c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7007c%Z I : word) = Some W_7007c.
Proof. vm_refl. Qed.
Lemma D_7007c : decode_any W_7007c = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.




























(* [comment removed for export] *)
Definition W_700a4 : bv 32 := @BV 32 0x0009e697%Z I.
Lemma F_700a4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x700a4%Z I : word) = Some W_700a4.
Proof. vm_refl. Qed.
Lemma D_700a4 : decode_any W_700a4 = Some (Auipc (@BV 5 13%Z I) (@BV 20 158%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_700a8 : bv 32 := @BV 32 0x97868683%Z I.
Lemma F_700a8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x700a8%Z I : word) = Some W_700a8.
Proof. vm_refl. Qed.
Lemma D_700a8 : decode_any W_700a8 = Some (Load SZ1 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 2424%Z I), 4%Z).
Proof. vm_refl. Qed.













(* [comment removed for export] *)
Definition W_700bc : bv 32 := @BV 32 0x00096697%Z I.
Lemma F_700bc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x700bc%Z I : word) = Some W_700bc.
Proof. vm_refl. Qed.
Lemma D_700bc : decode_any W_700bc = Some (Auipc (@BV 5 13%Z I) (@BV 20 150%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_700c0 : bv 32 := @BV 32 0xe5c6b683%Z I.
Lemma F_700c0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x700c0%Z I : word) = Some W_700c0.
Proof. vm_refl. Qed.
Lemma D_700c0 : decode_any W_700c0 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 3676%Z I), 4%Z).
Proof. vm_refl. Qed.



















(* [comment removed for export] *)
Definition W_700dc : bv 32 := @BV 32 0x00096797%Z I.
Lemma F_700dc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x700dc%Z I : word) = Some W_700dc.
Proof. vm_refl. Qed.
Lemma D_700dc : decode_any W_700dc = Some (Auipc (@BV 5 15%Z I) (@BV 20 150%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_700e0 : bv 32 := @BV 32 0xe447b783%Z I.
Lemma F_700e0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x700e0%Z I : word) = Some W_700e0.
Proof. vm_refl. Qed.
Lemma D_700e0 : decode_any W_700e0 = Some (Load SZ8 true (@BV 5 15%Z I) (@BV 5 15%Z I) (@BV 12 3652%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_700e4 : bv 32 := @BV 32 0x00096817%Z I.
Lemma F_700e4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x700e4%Z I : word) = Some W_700e4.
Proof. vm_refl. Qed.
Lemma D_700e4 : decode_any W_700e4 = Some (Auipc (@BV 5 16%Z I) (@BV 20 150%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_700e8 : bv 32 := @BV 32 0xe4483803%Z I.
Lemma F_700e8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x700e8%Z I : word) = Some W_700e8.
Proof. vm_refl. Qed.
Lemma D_700e8 : decode_any W_700e8 = Some (Load SZ8 true (@BV 5 16%Z I) (@BV 5 16%Z I) (@BV 12 3652%Z I), 4%Z).
Proof. vm_refl. Qed.
















(* [comment removed for export] *)
Definition W_70100 : bv 32 := @BV 32 0x00096297%Z I.
Lemma F_70100 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x70100%Z I : word) = Some W_70100.
Proof. vm_refl. Qed.
Lemma D_70100 : decode_any W_70100 = Some (Auipc (@BV 5 5%Z I) (@BV 20 150%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70104 : bv 32 := @BV 32 0xe302b283%Z I.
Lemma F_70104 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x70104%Z I : word) = Some W_70104.
Proof. vm_refl. Qed.
Lemma D_70104 : decode_any W_70104 = Some (Load SZ8 true (@BV 5 5%Z I) (@BV 5 5%Z I) (@BV 12 3632%Z I), 4%Z).
Proof. vm_refl. Qed.


































(* [comment removed for export] *)
Definition W_702c4 : bv 32 := @BV 32 0x00096717%Z I.
Lemma F_702c4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x702c4%Z I : word) = Some W_702c4.
Proof. vm_refl. Qed.
Lemma D_702c4 : decode_any W_702c4 = Some (Auipc (@BV 5 14%Z I) (@BV 20 150%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_702c8 : bv 32 := @BV 32 0xc5c73703%Z I.
Lemma F_702c8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x702c8%Z I : word) = Some W_702c8.
Proof. vm_refl. Qed.
Lemma D_702c8 : decode_any W_702c8 = Some (Load SZ8 true (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 12 3164%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_702cc : bv 32 := @BV 32 0x00096797%Z I.
Lemma F_702cc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x702cc%Z I : word) = Some W_702cc.
Proof. vm_refl. Qed.
Lemma D_702cc : decode_any W_702cc = Some (Auipc (@BV 5 15%Z I) (@BV 20 150%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_702d0 : bv 32 := @BV 32 0xc5c7b783%Z I.
Lemma F_702d0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x702d0%Z I : word) = Some W_702d0.
Proof. vm_refl. Qed.
Lemma D_702d0 : decode_any W_702d0 = Some (Load SZ8 true (@BV 5 15%Z I) (@BV 5 15%Z I) (@BV 12 3164%Z I), 4%Z).
Proof. vm_refl. Qed.







(* [comment removed for export] *)
Definition W_702e8 : bv 32 := @BV 32 0x00096797%Z I.
Lemma F_702e8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x702e8%Z I : word) = Some W_702e8.
Proof. vm_refl. Qed.
Lemma D_702e8 : decode_any W_702e8 = Some (Auipc (@BV 5 15%Z I) (@BV 20 150%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_702ec : bv 32 := @BV 32 0xc487b783%Z I.
Lemma F_702ec : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x702ec%Z I : word) = Some W_702ec.
Proof. vm_refl. Qed.
Lemma D_702ec : decode_any W_702ec = Some (Load SZ8 true (@BV 5 15%Z I) (@BV 5 15%Z I) (@BV 12 3144%Z I), 4%Z).
Proof. vm_refl. Qed.













(* [comment removed for export] *)
Definition W_70304 : bv 32 := @BV 32 0x00096697%Z I.
Lemma F_70304 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x70304%Z I : word) = Some W_70304.
Proof. vm_refl. Qed.
Lemma D_70304 : decode_any W_70304 = Some (Auipc (@BV 5 13%Z I) (@BV 20 150%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70308 : bv 32 := @BV 32 0xc346b983%Z I.
Lemma F_70308 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x70308%Z I : word) = Some W_70308.
Proof. vm_refl. Qed.
Lemma D_70308 : decode_any W_70308 = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 13%Z I) (@BV 12 3124%Z I), 4%Z).
Proof. vm_refl. Qed.













(* [comment removed for export] *)
Definition W_7032c : bv 32 := @BV 32 0x00096597%Z I.
Lemma F_7032c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7032c%Z I : word) = Some W_7032c.
Proof. vm_refl. Qed.
Lemma D_7032c : decode_any W_7032c = Some (Auipc (@BV 5 11%Z I) (@BV 20 150%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70330 : bv 32 := @BV 32 0xbdc5b583%Z I.
Lemma F_70330 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x70330%Z I : word) = Some W_70330.
Proof. vm_refl. Qed.
Lemma D_70330 : decode_any W_70330 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 3036%Z I), 4%Z).
Proof. vm_refl. Qed.
































































(* [comment removed for export] *)
Definition W_7057c : bv 32 := @BV 32 0x00096597%Z I.
Lemma F_7057c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7057c%Z I : word) = Some W_7057c.
Proof. vm_refl. Qed.
Lemma D_7057c : decode_any W_7057c = Some (Auipc (@BV 5 11%Z I) (@BV 20 150%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70580 : bv 32 := @BV 32 0x99c5b583%Z I.
Lemma F_70580 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x70580%Z I : word) = Some W_70580.
Proof. vm_refl. Qed.
Lemma D_70580 : decode_any W_70580 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 2460%Z I), 4%Z).
Proof. vm_refl. Qed.



















(* [comment removed for export] *)
Definition W_7059c : bv 32 := @BV 32 0x00096697%Z I.
Lemma F_7059c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7059c%Z I : word) = Some W_7059c.
Proof. vm_refl. Qed.
Lemma D_7059c : decode_any W_7059c = Some (Auipc (@BV 5 13%Z I) (@BV 20 150%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_705a0 : bv 32 := @BV 32 0x9846b683%Z I.
Lemma F_705a0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x705a0%Z I : word) = Some W_705a0.
Proof. vm_refl. Qed.
Lemma D_705a0 : decode_any W_705a0 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 2436%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_705a4 : bv 32 := @BV 32 0x00096717%Z I.
Lemma F_705a4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x705a4%Z I : word) = Some W_705a4.
Proof. vm_refl. Qed.
Lemma D_705a4 : decode_any W_705a4 = Some (Auipc (@BV 5 14%Z I) (@BV 20 150%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_705a8 : bv 32 := @BV 32 0x98473703%Z I.
Lemma F_705a8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x705a8%Z I : word) = Some W_705a8.
Proof. vm_refl. Qed.
Lemma D_705a8 : decode_any W_705a8 = Some (Load SZ8 true (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 12 2436%Z I), 4%Z).
Proof. vm_refl. Qed.
















(* [comment removed for export] *)
Definition W_705c0 : bv 32 := @BV 32 0x00096717%Z I.
Lemma F_705c0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x705c0%Z I : word) = Some W_705c0.
Proof. vm_refl. Qed.
Lemma D_705c0 : decode_any W_705c0 = Some (Auipc (@BV 5 14%Z I) (@BV 20 150%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_705c4 : bv 32 := @BV 32 0x97073703%Z I.
Lemma F_705c4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x705c4%Z I : word) = Some W_705c4.
Proof. vm_refl. Qed.
Lemma D_705c4 : decode_any W_705c4 = Some (Load SZ8 true (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 12 2416%Z I), 4%Z).
Proof. vm_refl. Qed.








































































































































































End Bo_code_7006c_706b8.
Require Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtSetShadow OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtReadCheck.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoRtLeafI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct Bo_code_5ec80_5eef0 Bo_code_70e54_70e84.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemcpy.AsRtMuslMemcpyAL OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemcpy.AsRtMuslMemcpyMIS OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemcpy.AsRtMuslMemcpyC1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemcpy.AsRtMuslMemcpyC2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemcpy.AsRtMuslMemcpyC3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtSetShadow OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtReadCheck.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPGen3.
Context {fx : FPState}.

Definition both_imemset_entry : word := 0x809a8.

Lemma both_imemset_code :
  code_at AsanUbsan.M.loaded_segments both_imemset_entry 0 imemset_words.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold imemset_words in G in change_no_check G' end). code_at_vm. Qed.

Theorem both_imemset : forall mem0 (s c : word) n rom regs (ret : word),
  (0 <= n)%Z -> (bv_unsigned s + n < 2 ^ 64)%Z ->
  store_ok AsanUbsan.M.loaded_segments mem0 s (Z.to_nat n) = true ->
  (align15 n s = 0%Z -> n <> 0%Z -> (bv_unsigned c < 256)%Z) ->
  ret_ok ret -> getr regs 1 = ret ->
  getr regs 10 = s -> getr regs 11 = c -> getr regs 12 = Z_to_bv 64 n ->
  exists regs',
    msteps AsanUbsan.M.loaded_segments
           (mkst regs both_imemset_entry mem0 rom)
           (mkst regs' ret (wbytes mem0 s (repeat (Z_to_bv 8 (bv_unsigned c)) (Z.to_nat n))) rom)
    /\ regs_agree (fun r => In r imemset_clob) regs regs'.
Proof using.
  intros mem0 s c n rom regs ret Hn Hnw Hok HC256.
  rewrite <- (at_0 both_imemset_entry).
  apply (imemset_run _ _ mem0 s c n rom both_imemset_code Hn Hnw Hok HC256).
Qed.

End FPGen3.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPGen3.
Context {fx : FPState}.

Definition both_imemcpy_entry : word := 0x8092c.

Lemma both_imemcpy_code :
  code_at AsanUbsan.M.loaded_segments both_imemcpy_entry 0 imemcpy_words.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold imemcpy_words in G in change_no_check G' end). code_at_vm. Qed.

Theorem both_imemcpy : forall mem0 (dst src : word) n bs rom regs (ret : word),
  cpyH AsanUbsan.M.loaded_segments mem0 dst src n bs ->
  ret_ok ret -> getr regs 1 = ret ->
  getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
  exists regs',
    msteps AsanUbsan.M.loaded_segments
           (mkst regs both_imemcpy_entry mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
    /\ regs_agree (fun r => In r imemcpy_clob) regs regs'.
Proof using.
  intros mem0 dst src n bs rom regs ret HOK.
  rewrite <- (at_0 both_imemcpy_entry).
  apply (imemcpy_run _ _ mem0 dst src n bs rom both_imemcpy_code HOK).
Qed.

End FPGen3.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)

Section FPGen3.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition both_imemmove_entry : word := 0x80950.

Lemma both_imemmove_code :
  code_at AsanUbsan.M.loaded_segments both_imemmove_entry 0 imemmove_words.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold imemmove_words in G in change_no_check G' end). code_at_vm. Qed.


End FPGen3.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPGen3.
Context {fx : FPState}.

Definition both_mem_is_zero_entry : word := 0x80ed8.

Lemma both_mem_is_zero_code :
  code_at AsanUbsan.M.loaded_segments both_mem_is_zero_entry 0 memisz_words.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold memisz_words in G in change_no_check G' end). code_at_vm. Qed.

Theorem both_mem_is_zero : forall mem (beg sp : word) N rom regs (ret : word),
  (0 <= N <= 2 ^ 40)%Z ->
  (bv_unsigned beg + N + 8 <= 2 ^ 64)%Z ->
  (16 <= bv_unsigned sp)%Z ->
  store_ok AsanUbsan.M.loaded_segments mem (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = true ->
  (bv_unsigned beg + N <= bv_unsigned sp - 8 \/ bv_unsigned sp <= bv_unsigned beg)%Z ->
  (forall a : word, (bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N)%Z ->
     rdn AsanUbsan.M.loaded_segments mem a 1 = Some [Z_to_bv 8 0]) ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
  getr regs 10 = beg -> getr regs 11 = Z_to_bv 64 N ->
  exists regs',
    msteps AsanUbsan.M.loaded_segments
           (mkst regs both_mem_is_zero_entry mem rom)
           (mkst regs' ret (wbytes mem (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ret)) rom)
    /\ regs_agree (fun r => In r memisz_clob) regs regs'
    /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
Proof using.
  intros mem beg sp N rom regs ret.
  apply (mem_is_zero_summary _ _ mem beg sp N rom regs ret both_mem_is_zero_code).
Qed.

End FPGen3.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Section FPGen3.
Context {fx : FPState}.


Definition both_memset_entry : word := 0xfc38c.

Lemma both_memset_code :
  code_at AsanUbsan.M.loaded_segments both_memset_entry 0 mmemset_words.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold mmemset_words in G in change_no_check G' end). code_at_vm. Qed.

Theorem both_memset : forall (mem0 : word -> option byte) (d cv ret : word) (n : Z) (rom : word -> option byte) regs,
  (0 <= n)%Z -> (bv_unsigned d + n < 2 ^ 64)%Z ->
  store_ok AsanUbsan.M.loaded_segments mem0 d (Z.to_nat n) = true -> ret_ok ret ->
  getr regs 10 = d -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
  exists regs',
    msteps AsanUbsan.M.loaded_segments
           (mkst regs both_memset_entry mem0 rom)
           (mkst regs' ret (wbytes mem0 d (repeat (cbyte cv) (Z.to_nat n))) rom)
    /\ getr regs' 10 = d /\ ms_agree regs regs'.
Proof using.
  intros mem0 d cv ret n rom regs Hn Hnw Hok Hret.
  rewrite <- (at_0 both_memset_entry).
  apply (memset_summary _ _ both_memset_code mem0 d cv ret n rom Hn Hnw Hok Hret).
Qed.

End FPGen3.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Section FPGen2.
Context {fx : FPState}.


Definition both_memcpy_entry : word := 0xfbf88.

Lemma both_memcpy_code :
  code_at AsanUbsan.M.loaded_segments both_memcpy_entry 0 mmemcpy_words.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold mmemcpy_words in G in change_no_check G' end). code_at_vm. Qed.

Theorem both_memcpy : forall (mem0 : word -> option byte) (dst src : word) n bs (rom : word -> option byte) regs (ret : word),
  mcH AsanUbsan.M.loaded_segments mem0 dst src n bs ->
  ret_ok ret -> getr regs 1 = ret ->
  getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
  exists regs',
    msteps AsanUbsan.M.loaded_segments
           (mkst regs both_memcpy_entry mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
    /\ keeps regs regs'.
Proof using.
  intros mem0 dst src n bs rom regs ret HOK.
  rewrite <- (at_0 both_memcpy_entry).
  apply (mmemcpy_run _ _ both_memcpy_code mem0 dst src n bs rom HOK).
Qed.

End FPGen2.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).


(* [comment removed for export] *)

Section FPGen2.
Context {fx : FPState}.
#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Definition both_g_rms : Z := 0x105f38.
Definition both_p_rms : Z := 0x107e58.

Record both_setshH (mem : word -> option byte) (addr ra : word) (n : Z) : Prop := BOTH_SETSHH {
  ss_g_rms : rdn BSEGS mem (Z_to_bv 64 both_g_rms) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 both_p_rms));
  ss_rms : rdn BSEGS mem (Z_to_bv 64 both_p_rms) 8 = Some (word_to_le_bytes 8 both_memset_entry);
  ss_n : (0 <= n)%Z;
  ss_nw : (bv_unsigned addr + n < 2 ^ 64)%Z;
  ss_ok : store_ok BSEGS mem addr (Z.to_nat n) = true;
  ss_ret : ret_ok ra }.

Ltac both_setsh_inst base Fa Da Fl Dl Fli Dli :=
  intros mem rom addr ra n regs [R1 R2 Hn Hnw Hok Hret] H10 H11 H1;
  rewrite <- (at_0 base);
  eapply (setsh_run BSEGS base both_memset_entry both_g_rms both_p_rms); try eassumption;
  [ (lazymatch goal with |- ?G => let G' := eval unfold setsh_words in G in change_no_check G' end); code_ato_vm
  | exact both_memset_code
  | apply ret_ok_even; reflexivity
  | gload_tac Fa Da Fl Dl
  | intros rg mm rm; lit_pc;
    (chain_step; [reflexivity | eapply step_addi_at; [exact Fli | reflexivity | exact Dli | reflexivity | gres; reflexivity] | step_simpl]);
    close_refl
  | (lazymatch goal with |- ?G => let G' := eval unfold both_p_rms in G in change_no_check G' end); lia ].



(* [comment removed for export] *)
Ltac both_setsh_inst_fp base Fa Da Fl Dl Fli Dli :=
  intros mem rom addr ra n H regs [R1 R2 Hn Hnw Hok Hret] Hh1 Hh2 Hh3 H10 H11 H1;
  rewrite <- (at_0 base);
  eapply (setsh_run_fp BSEGS base both_memset_entry both_g_rms both_p_rms); try eassumption;
  [ (lazymatch goal with |- ?G => let G' := eval unfold setsh_words in G in change_no_check G' end); code_ato_vm
  | exact both_memset_code
  | apply ret_ok_even; reflexivity
  | gload_tac Fa Da Fl Dl
  | intros rg mm rm; lit_pc;
    (chain_step; [reflexivity | eapply step_addi_at; [exact Fli | reflexivity | exact Dli | reflexivity | gres; reflexivity] | step_simpl]);
    close_refl
  | (lazymatch goal with |- ?G => let G' := eval unfold both_p_rms in G in change_no_check G' end); lia
  | (lazymatch goal with |- ?G => let G' := eval unfold both_g_rms in G in change_no_check G' end); lia ].

Theorem both_set_shadow_f5_fp : forall mem rom (addr ra : word) (n : Z) (H : word -> bool) regs,
  both_setshH mem addr ra n ->
  hid_off H both_g_rms 8 -> hid_off H both_p_rms 8 -> hid_off H (bv_unsigned addr) n ->
  getr regs 10 = addr -> getr regs 11 = Z_to_bv 64 n -> getr regs 1 = ra ->
  exists r,
    msteps BSEGS (mkst regs (0x70e54 : word) (mrestrict H mem) rom)
                 (mkst r ra (mrestrict H (wbytes mem addr (repeat (cbyte (Z_to_bv 64 245)) (Z.to_nat n)))) rom)
    /\ getr r 10 = addr /\ regs_agree (fun r => In r setsh_clob) regs r.
Proof using. both_setsh_inst_fp (0x70e54 : word) F_70e54 D_70e54 F_70e58 D_70e58 F_70e64 D_70e64. Qed.


(* [comment removed for export] *)
End FPGen2.

(* [comment removed for export] *)
Section FPGen2.
Context {fx : FPState}.
#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 z := (word_to_le_bytes 8 (Z_to_bv 64 z)).




End FPGen2.
End BoRtLeafI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct BoRtLeafI OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF Bo_code_7006c_706b8 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Definition both_poison_tab : poison_tab :=
  {| pt_base := 0x70080; pt_mset := 0xfc38c;
     pt_g_shoff := 0x105f18; pt_p_shoff := 0x10e1b8; pt_g_midbeg := 0x105f20; pt_p_midbeg := 0x10eea8;
     pt_g_midend := 0x105f28; pt_p_midend := 0x10eeb0; pt_g_hiend := 0x105f30; pt_p_hiend := 0x10eea0;
     pt_g_rms := 0x105f38; pt_p_rms := 0x107e58; pt_g_cfl := 0x105f08; pt_p_cfl := 0x19fce8; pt_c_cpm := 0x10da1c |}.

Section FPGen1.
Context {fx : FPState}.

Lemma both_poison_tab_ok : poison_tab_ok BSEGS both_poison_tab.
Proof using.
  split; (lazymatch goal with |- ?G => let G' := eval cbn [pt_base pt_mset pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend
              pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm both_poison_tab] in G in change_no_check G' end).
  - (lazymatch goal with |- ?G => let G' := eval unfold poison_words in G in change_no_check G' end). code_ato_vm.
  - exact both_memset_code.
  - gload_tac F_700a4 D_700a4 F_700a8 D_700a8.
  - gload_tac F_700bc D_700bc F_700c0 D_700c0.
  - gload_tac F_700dc D_700dc F_700e0 D_700e0.
  - gload_tac F_700e4 D_700e4 F_700e8 D_700e8.
  - gload_tac F_70100 D_70100 F_70104 D_70104.
  - gload_tac F_702c4 D_702c4 F_702c8 D_702c8.
  - gload_tac F_702cc D_702cc F_702d0 D_702d0.
  - gload_tac F_702e8 D_702e8 F_702ec D_702ec.
  - gload_tac F_70304 D_70304 F_70308 D_70308.
  - gload_tac F_7032c D_7032c F_70330 D_70330.
Qed.

(* [comment removed for export] *)
Theorem both_poison_shadow :
  forall mem rom (addr size value ra sp : word) cpm midend thr regs,
  poisonH BSEGS both_poison_tab mem addr size value ra sp cpm midend thr ->
  getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = addr -> getr regs 11 = size -> getr regs 12 = value ->
  exists r,
    msteps BSEGS (mkst regs (0x70080 : word) mem rom)
                 (mkst r ra (wbytes (ps_frame mem sp ra (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                                              (getr regs 20) (getr regs 21))
                                    (Z_to_bv 64 (shad addr)) (repeat (cbyte value) (Z.to_nat (shlen size)))) rom)
    /\ regs_agree (fun r => In r poison_clob) regs r.
Proof using. exact (poison_shadow BSEGS both_poison_tab both_poison_tab_ok). Qed.

End FPGen1.
