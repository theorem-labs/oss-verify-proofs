(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.glaze.binary_reflection.images Require Import Plain.
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

(* [comment removed for export] *)
Definition W_2e1e0 : bv 32 := @BV 32 0xfffe2197%Z I.
Lemma F_2e1e0 : fetch_word Plain.M.loaded_segments (@BV 64 0x2e240%Z I : word) = Some W_2e1e0.
Proof. vm_refl. Qed.
Lemma D_2e1e0 : decode_any W_2e1e0 = Some (Auipc (@BV 5 3%Z I) (@BV 20 1048546%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e1e4 : bv 32 := @BV 32 0x5c018193%Z I.
Lemma F_2e1e4 : fetch_word Plain.M.loaded_segments (@BV 64 0x2e244%Z I : word) = Some W_2e1e4.
Proof. vm_refl. Qed.
Lemma D_2e1e4 : decode_any W_2e1e4 = Some (OpImm ALU_ADD (@BV 5 3%Z I) (@BV 5 3%Z I) (@BV 12 1472%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e1e8 : bv 32 := @BV 32 0x00010513%Z I.
Lemma F_2e1e8 : fetch_word Plain.M.loaded_segments (@BV 64 0x2e248%Z I : word) = Some W_2e1e8.
Proof. vm_refl. Qed.
Lemma D_2e1e8 : decode_any W_2e1e8 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e1ec : bv 32 := @BV 32 0xfffd2597%Z I.
Lemma F_2e1ec : fetch_word Plain.M.loaded_segments (@BV 64 0x2e24c%Z I : word) = Some W_2e1ec.
Proof. vm_refl. Qed.
Lemma D_2e1ec : decode_any W_2e1ec = Some (Auipc (@BV 5 11%Z I) (@BV 20 1048530%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e1f0 : bv 32 := @BV 32 0xdb458593%Z I.
Lemma F_2e1f0 : fetch_word Plain.M.loaded_segments (@BV 64 0x2e250%Z I : word) = Some W_2e1f0.
Proof. vm_refl. Qed.
Lemma D_2e1f0 : decode_any W_2e1f0 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 3508%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e1f4 : bv 32 := @BV 32 0xff017113%Z I.
Lemma F_2e1f4 : fetch_word Plain.M.loaded_segments (@BV 64 0x2e254%Z I : word) = Some W_2e1f4.
Proof. vm_refl. Qed.
Lemma D_2e1f4 : decode_any W_2e1f4 = Some (OpImm ALU_AND (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4080%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e1f8 : bv 32 := @BV 32 0x0040006f%Z I.
Lemma F_2e1f8 : fetch_word Plain.M.loaded_segments (@BV 64 0x2e258%Z I : word) = Some W_2e1f8.
Proof. vm_refl. Qed.
Lemma D_2e1f8 : decode_any W_2e1f8 = Some (Jal (@BV 5 0%Z I) (@BV 21 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e1fc : bv 32 := @BV 32 0x00052583%Z I.
Lemma F_2e1fc : fetch_word Plain.M.loaded_segments (@BV 64 0x2e25c%Z I : word) = Some W_2e1fc.
Proof. vm_refl. Qed.
Lemma D_2e1fc : decode_any W_2e1fc = Some (Load SZ4 true (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e200 : bv 32 := @BV 32 0x00046617%Z I.
Lemma F_2e200 : fetch_word Plain.M.loaded_segments (@BV 64 0x2e260%Z I : word) = Some W_2e200.
Proof. vm_refl. Qed.
Lemma D_2e200 : decode_any W_2e200 = Some (Auipc (@BV 5 12%Z I) (@BV 20 70%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e204 : bv 32 := @BV 32 0x00046697%Z I.
Lemma F_2e204 : fetch_word Plain.M.loaded_segments (@BV 64 0x2e264%Z I : word) = Some W_2e204.
Proof. vm_refl. Qed.
Lemma D_2e204 : decode_any W_2e204 = Some (Auipc (@BV 5 13%Z I) (@BV 20 70%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e208 : bv 32 := @BV 32 0x00046717%Z I.
Lemma F_2e208 : fetch_word Plain.M.loaded_segments (@BV 64 0x2e268%Z I : word) = Some W_2e208.
Proof. vm_refl. Qed.
Lemma D_2e208 : decode_any W_2e208 = Some (Auipc (@BV 5 14%Z I) (@BV 20 70%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e20c : bv 32 := @BV 32 0x36063783%Z I.
Lemma F_2e20c : fetch_word Plain.M.loaded_segments (@BV 64 0x2e26c%Z I : word) = Some W_2e20c.
Proof. vm_refl. Qed.
Lemma D_2e20c : decode_any W_2e20c = Some (Load SZ8 true (@BV 5 15%Z I) (@BV 5 12%Z I) (@BV 12 864%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e210 : bv 32 := @BV 32 0x3646b683%Z I.
Lemma F_2e210 : fetch_word Plain.M.loaded_segments (@BV 64 0x2e270%Z I : word) = Some W_2e210.
Proof. vm_refl. Qed.
Lemma D_2e210 : decode_any W_2e210 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 868%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e214 : bv 32 := @BV 32 0x36873703%Z I.
Lemma F_2e214 : fetch_word Plain.M.loaded_segments (@BV 64 0x2e274%Z I : word) = Some W_2e214.
Proof. vm_refl. Qed.
Lemma D_2e214 : decode_any W_2e214 = Some (Load SZ8 true (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 12 872%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e218 : bv 32 := @BV 32 0x00850613%Z I.
Lemma F_2e218 : fetch_word Plain.M.loaded_segments (@BV 64 0x2e278%Z I : word) = Some W_2e218.
Proof. vm_refl. Qed.
Lemma D_2e218 : decode_any W_2e218 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 10%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e21c : bv 32 := @BV 32 0x00078513%Z I.
Lemma F_2e21c : fetch_word Plain.M.loaded_segments (@BV 64 0x2e27c%Z I : word) = Some W_2e21c.
Proof. vm_refl. Qed.
Lemma D_2e21c : decode_any W_2e21c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 15%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e220 : bv 32 := @BV 32 0x00000793%Z I.
Lemma F_2e220 : fetch_word Plain.M.loaded_segments (@BV 64 0x2e280%Z I : word) = Some W_2e220.
Proof. vm_refl. Qed.
Lemma D_2e220 : decode_any W_2e220 = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e224 : bv 32 := @BV 32 0x6cd3206f%Z I.
Lemma F_2e224 : fetch_word Plain.M.loaded_segments (@BV 64 0x2e284%Z I : word) = Some W_2e224.
Proof. vm_refl. Qed.
Lemma D_2e224 : decode_any W_2e224 = Some (Jal (@BV 5 0%Z I) (@BV 21 208588%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e228 : bv 32 := @BV 32 0xff010113%Z I.
Lemma F_2e228 : fetch_word Plain.M.loaded_segments (@BV 64 0x2e288%Z I : word) = Some W_2e228.
Proof. vm_refl. Qed.
Lemma D_2e228 : decode_any W_2e228 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4080%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e22c : bv 32 := @BV 32 0x00113423%Z I.
Lemma F_2e22c : fetch_word Plain.M.loaded_segments (@BV 64 0x2e28c%Z I : word) = Some W_2e22c.
Proof. vm_refl. Qed.
Lemma D_2e22c : decode_any W_2e22c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e230 : bv 32 := @BV 32 0x00813023%Z I.
Lemma F_2e230 : fetch_word Plain.M.loaded_segments (@BV 64 0x2e290%Z I : word) = Some W_2e230.
Proof. vm_refl. Qed.
Lemma D_2e230 : decode_any W_2e230 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e234 : bv 32 := @BV 32 0x01010413%Z I.
Lemma F_2e234 : fetch_word Plain.M.loaded_segments (@BV 64 0x2e294%Z I : word) = Some W_2e234.
Proof. vm_refl. Qed.
Lemma D_2e234 : decode_any W_2e234 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e238 : bv 32 := @BV 32 0x00047517%Z I.
Lemma F_2e238 : fetch_word Plain.M.loaded_segments (@BV 64 0x2e298%Z I : word) = Some W_2e238.
Proof. vm_refl. Qed.
Lemma D_2e238 : decode_any W_2e238 = Some (Auipc (@BV 5 10%Z I) (@BV 20 71%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e23c : bv 32 := @BV 32 0x6c850513%Z I.
Lemma F_2e23c : fetch_word Plain.M.loaded_segments (@BV 64 0x2e29c%Z I : word) = Some W_2e23c.
Proof. vm_refl. Qed.
Lemma D_2e23c : decode_any W_2e23c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 1736%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e240 : bv 32 := @BV 32 0x00054503%Z I.
Lemma F_2e240 : fetch_word Plain.M.loaded_segments (@BV 64 0x2e2a0%Z I : word) = Some W_2e240.
Proof. vm_refl. Qed.
Lemma D_2e240 : decode_any W_2e240 = Some (Load SZ1 false (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e244 : bv 32 := @BV 32 0x00157513%Z I.
Lemma F_2e244 : fetch_word Plain.M.loaded_segments (@BV 64 0x2e2a4%Z I : word) = Some W_2e244.
Proof. vm_refl. Qed.
Lemma D_2e244 : decode_any W_2e244 = Some (OpImm ALU_AND (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e248 : bv 32 := @BV 32 0x00050663%Z I.
Lemma F_2e248 : fetch_word Plain.M.loaded_segments (@BV 64 0x2e2a8%Z I : word) = Some W_2e248.
Proof. vm_refl. Qed.
Lemma D_2e248 : decode_any W_2e248 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e254 : bv 32 := @BV 32 0x00047517%Z I.
Lemma F_2e254 : fetch_word Plain.M.loaded_segments (@BV 64 0x2e2b4%Z I : word) = Some W_2e254.
Proof. vm_refl. Qed.
Lemma D_2e254 : decode_any W_2e254 = Some (Auipc (@BV 5 10%Z I) (@BV 20 71%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e258 : bv 32 := @BV 32 0x6ac50593%Z I.
Lemma F_2e258 : fetch_word Plain.M.loaded_segments (@BV 64 0x2e2b8%Z I : word) = Some W_2e258.
Proof. vm_refl. Qed.
Lemma D_2e258 : decode_any W_2e258 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 1708%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e25c : bv 32 := @BV 32 0x00100513%Z I.
Lemma F_2e25c : fetch_word Plain.M.loaded_segments (@BV 64 0x2e2bc%Z I : word) = Some W_2e25c.
Proof. vm_refl. Qed.
Lemma D_2e25c : decode_any W_2e25c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e260 : bv 32 := @BV 32 0x00a58023%Z I.
Lemma F_2e260 : fetch_word Plain.M.loaded_segments (@BV 64 0x2e2c0%Z I : word) = Some W_2e260.
Proof. vm_refl. Qed.
Lemma D_2e260 : decode_any W_2e260 = Some (Store SZ1 (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e264 : bv 32 := @BV 32 0x00046517%Z I.
Lemma F_2e264 : fetch_word Plain.M.loaded_segments (@BV 64 0x2e2c4%Z I : word) = Some W_2e264.
Proof. vm_refl. Qed.
Lemma D_2e264 : decode_any W_2e264 = Some (Auipc (@BV 5 10%Z I) (@BV 20 70%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e268 : bv 32 := @BV 32 0x31453503%Z I.
Lemma F_2e268 : fetch_word Plain.M.loaded_segments (@BV 64 0x2e2c8%Z I : word) = Some W_2e268.
Proof. vm_refl. Qed.
Lemma D_2e268 : decode_any W_2e268 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 788%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e26c : bv 32 := @BV 32 0x02050063%Z I.
Lemma F_2e26c : fetch_word Plain.M.loaded_segments (@BV 64 0x2e2cc%Z I : word) = Some W_2e26c.
Proof. vm_refl. Qed.
Lemma D_2e26c : decode_any W_2e26c = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e28c : bv 32 := @BV 32 0x00813083%Z I.
Lemma F_2e28c : fetch_word Plain.M.loaded_segments (@BV 64 0x2e2ec%Z I : word) = Some W_2e28c.
Proof. vm_refl. Qed.
Lemma D_2e28c : decode_any W_2e28c = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e290 : bv 32 := @BV 32 0x00013403%Z I.
Lemma F_2e290 : fetch_word Plain.M.loaded_segments (@BV 64 0x2e2f0%Z I : word) = Some W_2e290.
Proof. vm_refl. Qed.
Lemma D_2e290 : decode_any W_2e290 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e294 : bv 32 := @BV 32 0x01010113%Z I.
Lemma F_2e294 : fetch_word Plain.M.loaded_segments (@BV 64 0x2e2f4%Z I : word) = Some W_2e294.
Proof. vm_refl. Qed.
Lemma D_2e294 : decode_any W_2e294 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e298 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_2e298 : fetch_word Plain.M.loaded_segments (@BV 64 0x2e2f8%Z I : word) = Some W_2e298.
Proof. vm_refl. Qed.
Lemma D_2e298 : decode_any W_2e298 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55ed0 : bv 32 := @BV 32 0x3f10b06f%Z I.
Lemma F_55ed0 : fetch_word Plain.M.loaded_segments (@BV 64 0x55f30%Z I : word) = Some W_55ed0.
Proof. vm_refl. Qed.
Lemma D_55ed0 : decode_any W_55ed0 = Some (Jal (@BV 5 0%Z I) (@BV 21 48112%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55ed4 : bv 32 := @BV 32 0xffdff06f%Z I.
Lemma F_55ed4 : fetch_word Plain.M.loaded_segments (@BV 64 0x55f34%Z I : word) = Some W_55ed4.
Proof. vm_refl. Qed.
Lemma D_55ed4 : decode_any W_55ed4 = Some (Jal (@BV 5 0%Z I) (@BV 21 2097148%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57930 : bv 32 := @BV 32 0xfb010113%Z I.
Lemma F_57930 : fetch_word Plain.M.loaded_segments (@BV 64 0x57990%Z I : word) = Some W_57930.
Proof. vm_refl. Qed.
Lemma D_57930 : decode_any W_57930 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4016%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57934 : bv 32 := @BV 32 0x04113423%Z I.
Lemma F_57934 : fetch_word Plain.M.loaded_segments (@BV 64 0x57994%Z I : word) = Some W_57934.
Proof. vm_refl. Qed.
Lemma D_57934 : decode_any W_57934 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 72%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57938 : bv 32 := @BV 32 0x04813023%Z I.
Lemma F_57938 : fetch_word Plain.M.loaded_segments (@BV 64 0x57998%Z I : word) = Some W_57938.
Proof. vm_refl. Qed.
Lemma D_57938 : decode_any W_57938 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5793c : bv 32 := @BV 32 0x02913c23%Z I.
Lemma F_5793c : fetch_word Plain.M.loaded_segments (@BV 64 0x5799c%Z I : word) = Some W_5793c.
Proof. vm_refl. Qed.
Lemma D_5793c : decode_any W_5793c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57940 : bv 32 := @BV 32 0x03213823%Z I.
Lemma F_57940 : fetch_word Plain.M.loaded_segments (@BV 64 0x579a0%Z I : word) = Some W_57940.
Proof. vm_refl. Qed.
Lemma D_57940 : decode_any W_57940 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57944 : bv 32 := @BV 32 0x03313423%Z I.
Lemma F_57944 : fetch_word Plain.M.loaded_segments (@BV 64 0x579a4%Z I : word) = Some W_57944.
Proof. vm_refl. Qed.
Lemma D_57944 : decode_any W_57944 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 19%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57948 : bv 32 := @BV 32 0x03413023%Z I.
Lemma F_57948 : fetch_word Plain.M.loaded_segments (@BV 64 0x579a8%Z I : word) = Some W_57948.
Proof. vm_refl. Qed.
Lemma D_57948 : decode_any W_57948 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 20%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5794c : bv 32 := @BV 32 0x01513c23%Z I.
Lemma F_5794c : fetch_word Plain.M.loaded_segments (@BV 64 0x579ac%Z I : word) = Some W_5794c.
Proof. vm_refl. Qed.
Lemma D_5794c : decode_any W_5794c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 21%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57950 : bv 32 := @BV 32 0x01613823%Z I.
Lemma F_57950 : fetch_word Plain.M.loaded_segments (@BV 64 0x579b0%Z I : word) = Some W_57950.
Proof. vm_refl. Qed.
Lemma D_57950 : decode_any W_57950 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 22%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57954 : bv 32 := @BV 32 0x01713423%Z I.
Lemma F_57954 : fetch_word Plain.M.loaded_segments (@BV 64 0x579b4%Z I : word) = Some W_57954.
Proof. vm_refl. Qed.
Lemma D_57954 : decode_any W_57954 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 23%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57958 : bv 32 := @BV 32 0x01813023%Z I.
Lemma F_57958 : fetch_word Plain.M.loaded_segments (@BV 64 0x579b8%Z I : word) = Some W_57958.
Proof. vm_refl. Qed.
Lemma D_57958 : decode_any W_57958 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 24%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5795c : bv 32 := @BV 32 0x00050413%Z I.
Lemma F_5795c : fetch_word Plain.M.loaded_segments (@BV 64 0x579bc%Z I : word) = Some W_5795c.
Proof. vm_refl. Qed.
Lemma D_5795c : decode_any W_5795c = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57960 : bv 32 := @BV 32 0x16058863%Z I.
Lemma F_57960 : fetch_word Plain.M.loaded_segments (@BV 64 0x579c0%Z I : word) = Some W_57960.
Proof. vm_refl. Qed.
Lemma D_57960 : decode_any W_57960 = Some (Branch BC_EQ (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 368%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57964 : bv 32 := @BV 32 0x00058493%Z I.
Lemma F_57964 : fetch_word Plain.M.loaded_segments (@BV 64 0x579c4%Z I : word) = Some W_57964.
Proof. vm_refl. Qed.
Lemma D_57964 : decode_any W_57964 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57968 : bv 32 := @BV 32 0x00044503%Z I.
Lemma F_57968 : fetch_word Plain.M.loaded_segments (@BV 64 0x579c8%Z I : word) = Some W_57968.
Proof. vm_refl. Qed.
Lemma D_57968 : decode_any W_57968 = Some (Load SZ1 false (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5796c : bv 32 := @BV 32 0x00043583%Z I.
Lemma F_5796c : fetch_word Plain.M.loaded_segments (@BV 64 0x579cc%Z I : word) = Some W_5796c.
Proof. vm_refl. Qed.
Lemma D_5796c : decode_any W_5796c = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57970 : bv 32 := @BV 32 0x00157513%Z I.
Lemma F_57970 : fetch_word Plain.M.loaded_segments (@BV 64 0x579d0%Z I : word) = Some W_57970.
Proof. vm_refl. Qed.
Lemma D_57970 : decode_any W_57970 = Some (OpImm ALU_AND (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57974 : bv 32 := @BV 32 0x02051663%Z I.
Lemma F_57974 : fetch_word Plain.M.loaded_segments (@BV 64 0x579d4%Z I : word) = Some W_57974.
Proof. vm_refl. Qed.
Lemma D_57974 : decode_any W_57974 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 44%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57978 : bv 32 := @BV 32 0x01600b93%Z I.
Lemma F_57978 : fetch_word Plain.M.loaded_segments (@BV 64 0x579d8%Z I : word) = Some W_57978.
Proof. vm_refl. Qed.
Lemma D_57978 : decode_any W_57978 = Some (OpImm ALU_ADD (@BV 5 23%Z I) (@BV 5 0%Z I) (@BV 12 22%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5797c : bv 32 := @BV 32 0x0015f513%Z I.
Lemma F_5797c : fetch_word Plain.M.loaded_segments (@BV 64 0x579dc%Z I : word) = Some W_5797c.
Proof. vm_refl. Qed.
Lemma D_5797c : decode_any W_5797c = Some (OpImm ALU_AND (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57980 : bv 32 := @BV 32 0x02051863%Z I.
Lemma F_57980 : fetch_word Plain.M.loaded_segments (@BV 64 0x579e0%Z I : word) = Some W_57980.
Proof. vm_refl. Qed.
Lemma D_57980 : decode_any W_57980 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57984 : bv 32 := @BV 32 0x03859593%Z I.
Lemma F_57984 : fetch_word Plain.M.loaded_segments (@BV 64 0x579e4%Z I : word) = Some W_57984.
Proof. vm_refl. Qed.
Lemma D_57984 : decode_any W_57984 = Some (ShiftImm ALU_SLL (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 6 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57988 : bv 32 := @BV 32 0x0395d913%Z I.
Lemma F_57988 : fetch_word Plain.M.loaded_segments (@BV 64 0x579e8%Z I : word) = Some W_57988.
Proof. vm_refl. Qed.
Lemma D_57988 : decode_any W_57988 = Some (ShiftImm ALU_SRL (@BV 5 18%Z I) (@BV 5 11%Z I) (@BV 6 57%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5798c : bv 32 := @BV 32 0x412b85b3%Z I.
Lemma F_5798c : fetch_word Plain.M.loaded_segments (@BV 64 0x579ec%Z I : word) = Some W_5798c.
Proof. vm_refl. Qed.
Lemma D_5798c : decode_any W_5798c = Some (Op ALU_SUB (@BV 5 11%Z I) (@BV 5 23%Z I) (@BV 5 18%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57990 : bv 32 := @BV 32 0x0295e663%Z I.
Lemma F_57990 : fetch_word Plain.M.loaded_segments (@BV 64 0x579f0%Z I : word) = Some W_57990.
Proof. vm_refl. Qed.
Lemma D_57990 : decode_any W_57990 = Some (Branch BC_LTU (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 13 44%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57994 : bv 32 := @BV 32 0x06050663%Z I.
Lemma F_57994 : fetch_word Plain.M.loaded_segments (@BV 64 0x579f4%Z I : word) = Some W_57994.
Proof. vm_refl. Qed.
Lemma D_57994 : decode_any W_57994 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 108%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57998 : bv 32 := @BV 32 0x01043a03%Z I.
Lemma F_57998 : fetch_word Plain.M.loaded_segments (@BV 64 0x579f8%Z I : word) = Some W_57998.
Proof. vm_refl. Qed.
Lemma D_57998 : decode_any W_57998 = Some (Load SZ8 true (@BV 5 20%Z I) (@BV 5 8%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5799c : bv 32 := @BV 32 0x0680006f%Z I.
Lemma F_5799c : fetch_word Plain.M.loaded_segments (@BV 64 0x579fc%Z I : word) = Some W_5799c.
Proof. vm_refl. Qed.
Lemma D_5799c : decode_any W_5799c = Some (Jal (@BV 5 0%Z I) (@BV 21 104%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_579a0 : bv 32 := @BV 32 0xffe5fb93%Z I.
Lemma F_579a0 : fetch_word Plain.M.loaded_segments (@BV 64 0x57a00%Z I : word) = Some W_579a0.
Proof. vm_refl. Qed.
Lemma D_579a0 : decode_any W_579a0 = Some (OpImm ALU_AND (@BV 5 23%Z I) (@BV 5 11%Z I) (@BV 12 4094%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_579a4 : bv 32 := @BV 32 0xfffb8b93%Z I.
Lemma F_579a4 : fetch_word Plain.M.loaded_segments (@BV 64 0x57a04%Z I : word) = Some W_579a4.
Proof. vm_refl. Qed.
Lemma D_579a4 : decode_any W_579a4 = Some (OpImm ALU_ADD (@BV 5 23%Z I) (@BV 5 23%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_579a8 : bv 32 := @BV 32 0x0015f513%Z I.
Lemma F_579a8 : fetch_word Plain.M.loaded_segments (@BV 64 0x57a08%Z I : word) = Some W_579a8.
Proof. vm_refl. Qed.
Lemma D_579a8 : decode_any W_579a8 = Some (OpImm ALU_AND (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_579ac : bv 32 := @BV 32 0xfc050ce3%Z I.
Lemma F_579ac : fetch_word Plain.M.loaded_segments (@BV 64 0x57a0c%Z I : word) = Some W_579ac.
Proof. vm_refl. Qed.
Lemma D_579ac : decode_any W_579ac = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 8152%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_579b0 : bv 32 := @BV 32 0x00843903%Z I.
Lemma F_579b0 : fetch_word Plain.M.loaded_segments (@BV 64 0x57a10%Z I : word) = Some W_579b0.
Proof. vm_refl. Qed.
Lemma D_579b0 : decode_any W_579b0 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 8%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_579b4 : bv 32 := @BV 32 0x412b85b3%Z I.
Lemma F_579b4 : fetch_word Plain.M.loaded_segments (@BV 64 0x57a14%Z I : word) = Some W_579b4.
Proof. vm_refl. Qed.
Lemma D_579b4 : decode_any W_579b4 = Some (Op ALU_SUB (@BV 5 11%Z I) (@BV 5 23%Z I) (@BV 5 18%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_579b8 : bv 32 := @BV 32 0xfc95fee3%Z I.
Lemma F_579b8 : fetch_word Plain.M.loaded_segments (@BV 64 0x57a18%Z I : word) = Some W_579b8.
Proof. vm_refl. Qed.
Lemma D_579b8 : decode_any W_579b8 = Some (Branch BC_GEU (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 13 8156%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_579bc : bv 32 := @BV 32 0x00990b33%Z I.
Lemma F_579bc : fetch_word Plain.M.loaded_segments (@BV 64 0x57a1c%Z I : word) = Some W_579bc.
Proof. vm_refl. Qed.
Lemma D_579bc : decode_any W_579bc = Some (Op ALU_ADD (@BV 5 22%Z I) (@BV 5 18%Z I) (@BV 5 9%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_579c0 : bv 32 := @BV 32 0xff700593%Z I.
Lemma F_579c0 : fetch_word Plain.M.loaded_segments (@BV 64 0x57a20%Z I : word) = Some W_579c0.
Proof. vm_refl. Qed.
Lemma D_579c0 : decode_any W_579c0 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 4087%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_579c4 : bv 32 := @BV 32 0x417b06b3%Z I.
Lemma F_579c4 : fetch_word Plain.M.loaded_segments (@BV 64 0x57a24%Z I : word) = Some W_579c4.
Proof. vm_refl. Qed.
Lemma D_579c4 : decode_any W_579c4 = Some (Op ALU_SUB (@BV 5 13%Z I) (@BV 5 22%Z I) (@BV 5 23%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_579c8 : bv 32 := @BV 32 0x417585b3%Z I.
Lemma F_579c8 : fetch_word Plain.M.loaded_segments (@BV 64 0x57a28%Z I : word) = Some W_579c8.
Proof. vm_refl. Qed.
Lemma D_579c8 : decode_any W_579c8 = Some (Op ALU_SUB (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 23%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_579cc : bv 32 := @BV 32 0x12d5ec63%Z I.
Lemma F_579cc : fetch_word Plain.M.loaded_segments (@BV 64 0x57a2c%Z I : word) = Some W_579cc.
Proof. vm_refl. Qed.
Lemma D_579cc : decode_any W_579cc = Some (Branch BC_LTU (@BV 5 11%Z I) (@BV 5 13%Z I) (@BV 13 312%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_579d0 : bv 32 := @BV 32 0x02050e63%Z I.
Lemma F_579d0 : fetch_word Plain.M.loaded_segments (@BV 64 0x57a30%Z I : word) = Some W_579d0.
Proof. vm_refl. Qed.
Lemma D_579d0 : decode_any W_579d0 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 60%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_579d4 : bv 32 := @BV 32 0x01043983%Z I.
Lemma F_579d4 : fetch_word Plain.M.loaded_segments (@BV 64 0x57a34%Z I : word) = Some W_579d4.
Proof. vm_refl. Qed.
Lemma D_579d4 : decode_any W_579d4 = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 8%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_579d8 : bv 32 := @BV 32 0xfe500513%Z I.
Lemma F_579d8 : fetch_word Plain.M.loaded_segments (@BV 64 0x57a38%Z I : word) = Some W_579d8.
Proof. vm_refl. Qed.
Lemma D_579d8 : decode_any W_579d8 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 4069%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_579dc : bv 32 := @BV 32 0x00155513%Z I.
Lemma F_579dc : fetch_word Plain.M.loaded_segments (@BV 64 0x57a3c%Z I : word) = Some W_579dc.
Proof. vm_refl. Qed.
Lemma D_579dc : decode_any W_579dc = Some (ShiftImm ALU_SRL (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 6 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_579e0 : bv 32 := @BV 32 0x03757e63%Z I.
Lemma F_579e0 : fetch_word Plain.M.loaded_segments (@BV 64 0x57a40%Z I : word) = Some W_579e0.
Proof. vm_refl. Qed.
Lemma D_579e0 : decode_any W_579e0 = Some (Branch BC_GEU (@BV 5 10%Z I) (@BV 5 23%Z I) (@BV 13 60%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a00 : bv 32 := @BV 32 0x00140a13%Z I.
Lemma F_57a00 : fetch_word Plain.M.loaded_segments (@BV 64 0x57a60%Z I : word) = Some W_57a00.
Proof. vm_refl. Qed.
Lemma D_57a00 : decode_any W_57a00 = Some (OpImm ALU_ADD (@BV 5 20%Z I) (@BV 5 8%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a04 : bv 32 := @BV 32 0x00990b33%Z I.
Lemma F_57a04 : fetch_word Plain.M.loaded_segments (@BV 64 0x57a64%Z I : word) = Some W_57a04.
Proof. vm_refl. Qed.
Lemma D_57a04 : decode_any W_57a04 = Some (Op ALU_ADD (@BV 5 22%Z I) (@BV 5 18%Z I) (@BV 5 9%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a08 : bv 32 := @BV 32 0x0940006f%Z I.
Lemma F_57a08 : fetch_word Plain.M.loaded_segments (@BV 64 0x57a68%Z I : word) = Some W_57a08.
Proof. vm_refl. Qed.
Lemma D_57a08 : decode_any W_57a08 = Some (Jal (@BV 5 0%Z I) (@BV 21 148%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a0c : bv 32 := @BV 32 0x00140993%Z I.
Lemma F_57a0c : fetch_word Plain.M.loaded_segments (@BV 64 0x57a6c%Z I : word) = Some W_57a0c.
Proof. vm_refl. Qed.
Lemma D_57a0c : decode_any W_57a0c = Some (OpImm ALU_ADD (@BV 5 19%Z I) (@BV 5 8%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a10 : bv 32 := @BV 32 0xfe500513%Z I.
Lemma F_57a10 : fetch_word Plain.M.loaded_segments (@BV 64 0x57a70%Z I : word) = Some W_57a10.
Proof. vm_refl. Qed.
Lemma D_57a10 : decode_any W_57a10 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 4069%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a14 : bv 32 := @BV 32 0x00155513%Z I.
Lemma F_57a14 : fetch_word Plain.M.loaded_segments (@BV 64 0x57a74%Z I : word) = Some W_57a14.
Proof. vm_refl. Qed.
Lemma D_57a14 : decode_any W_57a14 = Some (ShiftImm ALU_SRL (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 6 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a18 : bv 32 := @BV 32 0xfd7566e3%Z I.
Lemma F_57a18 : fetch_word Plain.M.loaded_segments (@BV 64 0x57a78%Z I : word) = Some W_57a18.
Proof. vm_refl. Qed.
Lemma D_57a18 : decode_any W_57a18 = Some (Branch BC_LTU (@BV 5 10%Z I) (@BV 5 23%Z I) (@BV 13 8140%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a1c : bv 32 := @BV 32 0x001b9593%Z I.
Lemma F_57a1c : fetch_word Plain.M.loaded_segments (@BV 64 0x57a7c%Z I : word) = Some W_57a1c.
Proof. vm_refl. Qed.
Lemma D_57a1c : decode_any W_57a1c = Some (ShiftImm ALU_SLL (@BV 5 11%Z I) (@BV 5 23%Z I) (@BV 6 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a20 : bv 32 := @BV 32 0x000b0513%Z I.
Lemma F_57a20 : fetch_word Plain.M.loaded_segments (@BV 64 0x57a80%Z I : word) = Some W_57a20.
Proof. vm_refl. Qed.
Lemma D_57a20 : decode_any W_57a20 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 22%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a24 : bv 32 := @BV 32 0x0165e463%Z I.
Lemma F_57a24 : fetch_word Plain.M.loaded_segments (@BV 64 0x57a84%Z I : word) = Some W_57a24.
Proof. vm_refl. Qed.
Lemma D_57a24 : decode_any W_57a24 = Some (Branch BC_LTU (@BV 5 11%Z I) (@BV 5 22%Z I) (@BV 13 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a28 : bv 32 := @BV 32 0x00058513%Z I.
Lemma F_57a28 : fetch_word Plain.M.loaded_segments (@BV 64 0x57a88%Z I : word) = Some W_57a28.
Proof. vm_refl. Qed.
Lemma D_57a28 : decode_any W_57a28 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a2c : bv 32 := @BV 32 0x00756a93%Z I.
Lemma F_57a2c : fetch_word Plain.M.loaded_segments (@BV 64 0x57a8c%Z I : word) = Some W_57a2c.
Proof. vm_refl. Qed.
Lemma D_57a2c : decode_any W_57a2c = Some (OpImm ALU_OR (@BV 5 21%Z I) (@BV 5 10%Z I) (@BV 12 7%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a30 : bv 32 := @BV 32 0x01700593%Z I.
Lemma F_57a30 : fetch_word Plain.M.loaded_segments (@BV 64 0x57a90%Z I : word) = Some W_57a30.
Proof. vm_refl. Qed.
Lemma D_57a30 : decode_any W_57a30 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 23%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a34 : bv 32 := @BV 32 0x00ba9863%Z I.
Lemma F_57a34 : fetch_word Plain.M.loaded_segments (@BV 64 0x57a94%Z I : word) = Some W_57a34.
Proof. vm_refl. Qed.
Lemma D_57a34 : decode_any W_57a34 = Some (Branch BC_NE (@BV 5 21%Z I) (@BV 5 11%Z I) (@BV 13 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a44 : bv 32 := @BV 32 0x001a8a93%Z I.
Lemma F_57a44 : fetch_word Plain.M.loaded_segments (@BV 64 0x57aa4%Z I : word) = Some W_57a44.
Proof. vm_refl. Qed.
Lemma D_57a44 : decode_any W_57a44 = Some (OpImm ALU_ADD (@BV 5 21%Z I) (@BV 5 21%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a48 : bv 32 := @BV 32 0x00b57463%Z I.
Lemma F_57a48 : fetch_word Plain.M.loaded_segments (@BV 64 0x57aa8%Z I : word) = Some W_57a48.
Proof. vm_refl. Qed.
Lemma D_57a48 : decode_any W_57a48 = Some (Branch BC_GEU (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 13 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a50 : bv 32 := @BV 32 0x00060c13%Z I.
Lemma F_57a50 : fetch_word Plain.M.loaded_segments (@BV 64 0x57ab0%Z I : word) = Some W_57a50.
Proof. vm_refl. Qed.
Lemma D_57a50 : decode_any W_57a50 = Some (OpImm ALU_ADD (@BV 5 24%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a54 : bv 32 := @BV 32 0x000a8513%Z I.
Lemma F_57a54 : fetch_word Plain.M.loaded_segments (@BV 64 0x57ab4%Z I : word) = Some W_57a54.
Proof. vm_refl. Qed.
Lemma D_57a54 : decode_any W_57a54 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 21%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a58 : bv 32 := @BV 32 0x07d180ef%Z I.
Lemma F_57a58 : fetch_word Plain.M.loaded_segments (@BV 64 0x57ab8%Z I : word) = Some W_57a58.
Proof. vm_refl. Qed.
Lemma D_57a58 : decode_any W_57a58 = Some (Jal (@BV 5 1%Z I) (@BV 21 100476%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a5c : bv 32 := @BV 32 0x00050a13%Z I.
Lemma F_57a5c : fetch_word Plain.M.loaded_segments (@BV 64 0x57abc%Z I : word) = Some W_57a5c.
Proof. vm_refl. Qed.
Lemma D_57a5c : decode_any W_57a5c = Some (OpImm ALU_ADD (@BV 5 20%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a60 : bv 32 := @BV 32 0x00090a63%Z I.
Lemma F_57a60 : fetch_word Plain.M.loaded_segments (@BV 64 0x57ac0%Z I : word) = Some W_57a60.
Proof. vm_refl. Qed.
Lemma D_57a60 : decode_any W_57a60 = Some (Branch BC_EQ (@BV 5 18%Z I) (@BV 5 0%Z I) (@BV 13 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a64 : bv 32 := @BV 32 0x000a0513%Z I.
Lemma F_57a64 : fetch_word Plain.M.loaded_segments (@BV 64 0x57ac4%Z I : word) = Some W_57a64.
Proof. vm_refl. Qed.
Lemma D_57a64 : decode_any W_57a64 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 20%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a68 : bv 32 := @BV 32 0x00098593%Z I.
Lemma F_57a68 : fetch_word Plain.M.loaded_segments (@BV 64 0x57ac8%Z I : word) = Some W_57a68.
Proof. vm_refl. Qed.
Lemma D_57a68 : decode_any W_57a68 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a6c : bv 32 := @BV 32 0x00090613%Z I.
Lemma F_57a6c : fetch_word Plain.M.loaded_segments (@BV 64 0x57acc%Z I : word) = Some W_57a6c.
Proof. vm_refl. Qed.
Lemma D_57a6c : decode_any W_57a6c = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a70 : bv 32 := @BV 32 0x574170ef%Z I.
Lemma F_57a70 : fetch_word Plain.M.loaded_segments (@BV 64 0x57ad0%Z I : word) = Some W_57a70.
Proof. vm_refl. Qed.
Lemma D_57a70 : decode_any W_57a70 = Some (Jal (@BV 5 1%Z I) (@BV 21 95604%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a74 : bv 32 := @BV 32 0x001b8593%Z I.
Lemma F_57a74 : fetch_word Plain.M.loaded_segments (@BV 64 0x57ad4%Z I : word) = Some W_57a74.
Proof. vm_refl. Qed.
Lemma D_57a74 : decode_any W_57a74 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 23%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a78 : bv 32 := @BV 32 0x01700513%Z I.
Lemma F_57a78 : fetch_word Plain.M.loaded_segments (@BV 64 0x57ad8%Z I : word) = Some W_57a78.
Proof. vm_refl. Qed.
Lemma D_57a78 : decode_any W_57a78 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 23%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a7c : bv 32 := @BV 32 0x00a58663%Z I.
Lemma F_57a7c : fetch_word Plain.M.loaded_segments (@BV 64 0x57adc%Z I : word) = Some W_57a7c.
Proof. vm_refl. Qed.
Lemma D_57a7c : decode_any W_57a7c = Some (Branch BC_EQ (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 13 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a80 : bv 32 := @BV 32 0x00098513%Z I.
Lemma F_57a80 : fetch_word Plain.M.loaded_segments (@BV 64 0x57ae0%Z I : word) = Some W_57a80.
Proof. vm_refl. Qed.
Lemma D_57a80 : decode_any W_57a80 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a84 : bv 32 := @BV 32 0xc50fe0ef%Z I.
Lemma F_57a84 : fetch_word Plain.M.loaded_segments (@BV 64 0x57ae4%Z I : word) = Some W_57a84.
Proof. vm_refl. Qed.
Lemma D_57a84 : decode_any W_57a84 = Some (Jal (@BV 5 1%Z I) (@BV 21 2090064%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a88 : bv 32 := @BV 32 0x001ae513%Z I.
Lemma F_57a88 : fetch_word Plain.M.loaded_segments (@BV 64 0x57ae8%Z I : word) = Some W_57a88.
Proof. vm_refl. Qed.
Lemma D_57a88 : decode_any W_57a88 = Some (OpImm ALU_OR (@BV 5 10%Z I) (@BV 5 21%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a8c : bv 32 := @BV 32 0x00a43023%Z I.
Lemma F_57a8c : fetch_word Plain.M.loaded_segments (@BV 64 0x57aec%Z I : word) = Some W_57a8c.
Proof. vm_refl. Qed.
Lemma D_57a8c : decode_any W_57a8c = Some (Store SZ8 (@BV 5 8%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a90 : bv 32 := @BV 32 0x01243423%Z I.
Lemma F_57a90 : fetch_word Plain.M.loaded_segments (@BV 64 0x57af0%Z I : word) = Some W_57a90.
Proof. vm_refl. Qed.
Lemma D_57a90 : decode_any W_57a90 = Some (Store SZ8 (@BV 5 8%Z I) (@BV 5 18%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a94 : bv 32 := @BV 32 0x01443823%Z I.
Lemma F_57a94 : fetch_word Plain.M.loaded_segments (@BV 64 0x57af4%Z I : word) = Some W_57a94.
Proof. vm_refl. Qed.
Lemma D_57a94 : decode_any W_57a94 = Some (Store SZ8 (@BV 5 8%Z I) (@BV 5 20%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a98 : bv 32 := @BV 32 0x000c0613%Z I.
Lemma F_57a98 : fetch_word Plain.M.loaded_segments (@BV 64 0x57af8%Z I : word) = Some W_57a98.
Proof. vm_refl. Qed.
Lemma D_57a98 : decode_any W_57a98 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 24%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57a9c : bv 32 := @BV 32 0x012a0533%Z I.
Lemma F_57a9c : fetch_word Plain.M.loaded_segments (@BV 64 0x57afc%Z I : word) = Some W_57a9c.
Proof. vm_refl. Qed.
Lemma D_57a9c : decode_any W_57a9c = Some (Op ALU_ADD (@BV 5 10%Z I) (@BV 5 20%Z I) (@BV 5 18%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57aa0 : bv 32 := @BV 32 0x00060593%Z I.
Lemma F_57aa0 : fetch_word Plain.M.loaded_segments (@BV 64 0x57b00%Z I : word) = Some W_57aa0.
Proof. vm_refl. Qed.
Lemma D_57aa0 : decode_any W_57aa0 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57aa4 : bv 32 := @BV 32 0x00048613%Z I.
Lemma F_57aa4 : fetch_word Plain.M.loaded_segments (@BV 64 0x57b04%Z I : word) = Some W_57aa4.
Proof. vm_refl. Qed.
Lemma D_57aa4 : decode_any W_57aa4 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57aa8 : bv 32 := @BV 32 0x6b8170ef%Z I.
Lemma F_57aa8 : fetch_word Plain.M.loaded_segments (@BV 64 0x57b08%Z I : word) = Some W_57aa8.
Proof. vm_refl. Qed.
Lemma D_57aa8 : decode_any W_57aa8 = Some (Jal (@BV 5 1%Z I) (@BV 21 95928%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57aac : bv 32 := @BV 32 0x00044503%Z I.
Lemma F_57aac : fetch_word Plain.M.loaded_segments (@BV 64 0x57b0c%Z I : word) = Some W_57aac.
Proof. vm_refl. Qed.
Lemma D_57aac : decode_any W_57aac = Some (Load SZ1 false (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57ab0 : bv 32 := @BV 32 0x00157513%Z I.
Lemma F_57ab0 : fetch_word Plain.M.loaded_segments (@BV 64 0x57b10%Z I : word) = Some W_57ab0.
Proof. vm_refl. Qed.
Lemma D_57ab0 : decode_any W_57ab0 = Some (OpImm ALU_AND (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57ab4 : bv 32 := @BV 32 0x00051863%Z I.
Lemma F_57ab4 : fetch_word Plain.M.loaded_segments (@BV 64 0x57b14%Z I : word) = Some W_57ab4.
Proof. vm_refl. Qed.
Lemma D_57ab4 : decode_any W_57ab4 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57ab8 : bv 32 := @BV 32 0x001b1513%Z I.
Lemma F_57ab8 : fetch_word Plain.M.loaded_segments (@BV 64 0x57b18%Z I : word) = Some W_57ab8.
Proof. vm_refl. Qed.
Lemma D_57ab8 : decode_any W_57ab8 = Some (ShiftImm ALU_SLL (@BV 5 10%Z I) (@BV 5 22%Z I) (@BV 6 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57abc : bv 32 := @BV 32 0x00a40023%Z I.
Lemma F_57abc : fetch_word Plain.M.loaded_segments (@BV 64 0x57b1c%Z I : word) = Some W_57abc.
Proof. vm_refl. Qed.
Lemma D_57abc : decode_any W_57abc = Some (Store SZ1 (@BV 5 8%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57ac0 : bv 32 := @BV 32 0x0080006f%Z I.
Lemma F_57ac0 : fetch_word Plain.M.loaded_segments (@BV 64 0x57b20%Z I : word) = Some W_57ac0.
Proof. vm_refl. Qed.
Lemma D_57ac0 : decode_any W_57ac0 = Some (Jal (@BV 5 0%Z I) (@BV 21 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57ac4 : bv 32 := @BV 32 0x01643423%Z I.
Lemma F_57ac4 : fetch_word Plain.M.loaded_segments (@BV 64 0x57b24%Z I : word) = Some W_57ac4.
Proof. vm_refl. Qed.
Lemma D_57ac4 : decode_any W_57ac4 = Some (Store SZ8 (@BV 5 8%Z I) (@BV 5 22%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57ac8 : bv 32 := @BV 32 0x016a0a33%Z I.
Lemma F_57ac8 : fetch_word Plain.M.loaded_segments (@BV 64 0x57b28%Z I : word) = Some W_57ac8.
Proof. vm_refl. Qed.
Lemma D_57ac8 : decode_any W_57ac8 = Some (Op ALU_ADD (@BV 5 20%Z I) (@BV 5 20%Z I) (@BV 5 22%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57acc : bv 32 := @BV 32 0x000a0023%Z I.
Lemma F_57acc : fetch_word Plain.M.loaded_segments (@BV 64 0x57b2c%Z I : word) = Some W_57acc.
Proof. vm_refl. Qed.
Lemma D_57acc : decode_any W_57acc = Some (Store SZ1 (@BV 5 20%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57ad0 : bv 32 := @BV 32 0x00040513%Z I.
Lemma F_57ad0 : fetch_word Plain.M.loaded_segments (@BV 64 0x57b30%Z I : word) = Some W_57ad0.
Proof. vm_refl. Qed.
Lemma D_57ad0 : decode_any W_57ad0 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57ad4 : bv 32 := @BV 32 0x04813083%Z I.
Lemma F_57ad4 : fetch_word Plain.M.loaded_segments (@BV 64 0x57b34%Z I : word) = Some W_57ad4.
Proof. vm_refl. Qed.
Lemma D_57ad4 : decode_any W_57ad4 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 72%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57ad8 : bv 32 := @BV 32 0x04013403%Z I.
Lemma F_57ad8 : fetch_word Plain.M.loaded_segments (@BV 64 0x57b38%Z I : word) = Some W_57ad8.
Proof. vm_refl. Qed.
Lemma D_57ad8 : decode_any W_57ad8 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57adc : bv 32 := @BV 32 0x03813483%Z I.
Lemma F_57adc : fetch_word Plain.M.loaded_segments (@BV 64 0x57b3c%Z I : word) = Some W_57adc.
Proof. vm_refl. Qed.
Lemma D_57adc : decode_any W_57adc = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57ae0 : bv 32 := @BV 32 0x03013903%Z I.
Lemma F_57ae0 : fetch_word Plain.M.loaded_segments (@BV 64 0x57b40%Z I : word) = Some W_57ae0.
Proof. vm_refl. Qed.
Lemma D_57ae0 : decode_any W_57ae0 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57ae4 : bv 32 := @BV 32 0x02813983%Z I.
Lemma F_57ae4 : fetch_word Plain.M.loaded_segments (@BV 64 0x57b44%Z I : word) = Some W_57ae4.
Proof. vm_refl. Qed.
Lemma D_57ae4 : decode_any W_57ae4 = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 2%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57ae8 : bv 32 := @BV 32 0x02013a03%Z I.
Lemma F_57ae8 : fetch_word Plain.M.loaded_segments (@BV 64 0x57b48%Z I : word) = Some W_57ae8.
Proof. vm_refl. Qed.
Lemma D_57ae8 : decode_any W_57ae8 = Some (Load SZ8 true (@BV 5 20%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57aec : bv 32 := @BV 32 0x01813a83%Z I.
Lemma F_57aec : fetch_word Plain.M.loaded_segments (@BV 64 0x57b4c%Z I : word) = Some W_57aec.
Proof. vm_refl. Qed.
Lemma D_57aec : decode_any W_57aec = Some (Load SZ8 true (@BV 5 21%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57af0 : bv 32 := @BV 32 0x01013b03%Z I.
Lemma F_57af0 : fetch_word Plain.M.loaded_segments (@BV 64 0x57b50%Z I : word) = Some W_57af0.
Proof. vm_refl. Qed.
Lemma D_57af0 : decode_any W_57af0 = Some (Load SZ8 true (@BV 5 22%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57af4 : bv 32 := @BV 32 0x00813b83%Z I.
Lemma F_57af4 : fetch_word Plain.M.loaded_segments (@BV 64 0x57b54%Z I : word) = Some W_57af4.
Proof. vm_refl. Qed.
Lemma D_57af4 : decode_any W_57af4 = Some (Load SZ8 true (@BV 5 23%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57af8 : bv 32 := @BV 32 0x00013c03%Z I.
Lemma F_57af8 : fetch_word Plain.M.loaded_segments (@BV 64 0x57b58%Z I : word) = Some W_57af8.
Proof. vm_refl. Qed.
Lemma D_57af8 : decode_any W_57af8 = Some (Load SZ8 true (@BV 5 24%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57afc : bv 32 := @BV 32 0x05010113%Z I.
Lemma F_57afc : fetch_word Plain.M.loaded_segments (@BV 64 0x57b5c%Z I : word) = Some W_57afc.
Proof. vm_refl. Qed.
Lemma D_57afc : decode_any W_57afc = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 80%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57b00 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_57b00 : fetch_word Plain.M.loaded_segments (@BV 64 0x57b60%Z I : word) = Some W_57b00.
Proof. vm_refl. Qed.
Lemma D_57b00 : decode_any W_57b00 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57b08 : bv 32 := @BV 32 0x00054703%Z I.
Lemma F_57b08 : fetch_word Plain.M.loaded_segments (@BV 64 0x57b68%Z I : word) = Some W_57b08.
Proof. vm_refl. Qed.
Lemma D_57b08 : decode_any W_57b08 = Some (Load SZ1 false (@BV 5 14%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57b0c : bv 32 := @BV 32 0x00177693%Z I.
Lemma F_57b0c : fetch_word Plain.M.loaded_segments (@BV 64 0x57b6c%Z I : word) = Some W_57b0c.
Proof. vm_refl. Qed.
Lemma D_57b0c : decode_any W_57b0c = Some (OpImm ALU_AND (@BV 5 13%Z I) (@BV 5 14%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57b10 : bv 32 := @BV 32 0x02068463%Z I.
Lemma F_57b10 : fetch_word Plain.M.loaded_segments (@BV 64 0x57b70%Z I : word) = Some W_57b10.
Proof. vm_refl. Qed.
Lemma D_57b10 : decode_any W_57b10 = Some (Branch BC_EQ (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 13 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57b14 : bv 32 := @BV 32 0x00853703%Z I.
Lemma F_57b14 : fetch_word Plain.M.loaded_segments (@BV 64 0x57b74%Z I : word) = Some W_57b14.
Proof. vm_refl. Qed.
Lemma D_57b14 : decode_any W_57b14 = Some (Load SZ8 true (@BV 5 14%Z I) (@BV 5 10%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57b18 : bv 32 := @BV 32 0x02b76463%Z I.
Lemma F_57b18 : fetch_word Plain.M.loaded_segments (@BV 64 0x57b78%Z I : word) = Some W_57b18.
Proof. vm_refl. Qed.
Lemma D_57b18 : decode_any W_57b18 = Some (Branch BC_LTU (@BV 5 14%Z I) (@BV 5 11%Z I) (@BV 13 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57b1c : bv 32 := @BV 32 0x02069663%Z I.
Lemma F_57b1c : fetch_word Plain.M.loaded_segments (@BV 64 0x57b7c%Z I : word) = Some W_57b1c.
Proof. vm_refl. Qed.
Lemma D_57b1c : decode_any W_57b1c = Some (Branch BC_NE (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 13 44%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57b20 : bv 32 := @BV 32 0x00150613%Z I.
Lemma F_57b20 : fetch_word Plain.M.loaded_segments (@BV 64 0x57b80%Z I : word) = Some W_57b20.
Proof. vm_refl. Qed.
Lemma D_57b20 : decode_any W_57b20 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 10%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57b24 : bv 32 := @BV 32 0x00159693%Z I.
Lemma F_57b24 : fetch_word Plain.M.loaded_segments (@BV 64 0x57b84%Z I : word) = Some W_57b24.
Proof. vm_refl. Qed.
Lemma D_57b24 : decode_any W_57b24 = Some (ShiftImm ALU_SLL (@BV 5 13%Z I) (@BV 5 11%Z I) (@BV 6 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57b28 : bv 32 := @BV 32 0x00d50023%Z I.
Lemma F_57b28 : fetch_word Plain.M.loaded_segments (@BV 64 0x57b88%Z I : word) = Some W_57b28.
Proof. vm_refl. Qed.
Lemma D_57b28 : decode_any W_57b28 = Some (Store SZ1 (@BV 5 10%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57b2c : bv 32 := @BV 32 0x00b605b3%Z I.
Lemma F_57b2c : fetch_word Plain.M.loaded_segments (@BV 64 0x57b8c%Z I : word) = Some W_57b2c.
Proof. vm_refl. Qed.
Lemma D_57b2c : decode_any W_57b2c = Some (Op ALU_ADD (@BV 5 11%Z I) (@BV 5 12%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57b30 : bv 32 := @BV 32 0x00058023%Z I.
Lemma F_57b30 : fetch_word Plain.M.loaded_segments (@BV 64 0x57b90%Z I : word) = Some W_57b30.
Proof. vm_refl. Qed.
Lemma D_57b30 : decode_any W_57b30 = Some (Store SZ1 (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57b34 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_57b34 : fetch_word Plain.M.loaded_segments (@BV 64 0x57b94%Z I : word) = Some W_57b34.
Proof. vm_refl. Qed.
Lemma D_57b34 : decode_any W_57b34 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57b38 : bv 32 := @BV 32 0x00175713%Z I.
Lemma F_57b38 : fetch_word Plain.M.loaded_segments (@BV 64 0x57b98%Z I : word) = Some W_57b38.
Proof. vm_refl. Qed.
Lemma D_57b38 : decode_any W_57b38 = Some (ShiftImm ALU_SRL (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 6 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57b3c : bv 32 := @BV 32 0xfeb770e3%Z I.
Lemma F_57b3c : fetch_word Plain.M.loaded_segments (@BV 64 0x57b9c%Z I : word) = Some W_57b3c.
Proof. vm_refl. Qed.
Lemma D_57b3c : decode_any W_57b3c = Some (Branch BC_GEU (@BV 5 14%Z I) (@BV 5 11%Z I) (@BV 13 8160%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57b40 : bv 32 := @BV 32 0x40e585b3%Z I.
Lemma F_57b40 : fetch_word Plain.M.loaded_segments (@BV 64 0x57ba0%Z I : word) = Some W_57b40.
Proof. vm_refl. Qed.
Lemma D_57b40 : decode_any W_57b40 = Some (Op ALU_SUB (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 14%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57b44 : bv 32 := @BV 32 0xdedff06f%Z I.
Lemma F_57b44 : fetch_word Plain.M.loaded_segments (@BV 64 0x57ba4%Z I : word) = Some W_57b44.
Proof. vm_refl. Qed.
Lemma D_57b44 : decode_any W_57b44 = Some (Jal (@BV 5 0%Z I) (@BV 21 2096620%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57b48 : bv 32 := @BV 32 0x01053603%Z I.
Lemma F_57b48 : fetch_word Plain.M.loaded_segments (@BV 64 0x57ba8%Z I : word) = Some W_57b48.
Proof. vm_refl. Qed.
Lemma D_57b48 : decode_any W_57b48 = Some (Load SZ8 true (@BV 5 12%Z I) (@BV 5 10%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57b4c : bv 32 := @BV 32 0x00b53423%Z I.
Lemma F_57b4c : fetch_word Plain.M.loaded_segments (@BV 64 0x57bac%Z I : word) = Some W_57b4c.
Proof. vm_refl. Qed.
Lemma D_57b4c : decode_any W_57b4c = Some (Store SZ8 (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57b50 : bv 32 := @BV 32 0x00b605b3%Z I.
Lemma F_57b50 : fetch_word Plain.M.loaded_segments (@BV 64 0x57bb0%Z I : word) = Some W_57b50.
Proof. vm_refl. Qed.
Lemma D_57b50 : decode_any W_57b50 = Some (Op ALU_ADD (@BV 5 11%Z I) (@BV 5 12%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57b54 : bv 32 := @BV 32 0x00058023%Z I.
Lemma F_57b54 : fetch_word Plain.M.loaded_segments (@BV 64 0x57bb4%Z I : word) = Some W_57b54.
Proof. vm_refl. Qed.
Lemma D_57b54 : decode_any W_57b54 = Some (Store SZ1 (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57b58 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_57b58 : fetch_word Plain.M.loaded_segments (@BV 64 0x57bb8%Z I : word) = Some W_57b58.
Proof. vm_refl. Qed.
Lemma D_57b58 : decode_any W_57b58 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e74 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_60e74 : fetch_word Plain.M.loaded_segments (@BV 64 0x60ed4%Z I : word) = Some W_60e74.
Proof. vm_refl. Qed.
Lemma D_60e74 : decode_any W_60e74 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e78 : bv 32 := @BV 32 0xe8010113%Z I.
Lemma F_60e78 : fetch_word Plain.M.loaded_segments (@BV 64 0x60ed8%Z I : word) = Some W_60e78.
Proof. vm_refl. Qed.
Lemma D_60e78 : decode_any W_60e78 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 3712%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e7c : bv 32 := @BV 32 0x16113c23%Z I.
Lemma F_60e7c : fetch_word Plain.M.loaded_segments (@BV 64 0x60edc%Z I : word) = Some W_60e7c.
Proof. vm_refl. Qed.
Lemma D_60e7c : decode_any W_60e7c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 376%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e80 : bv 32 := @BV 32 0x16813823%Z I.
Lemma F_60e80 : fetch_word Plain.M.loaded_segments (@BV 64 0x60ee0%Z I : word) = Some W_60e80.
Proof. vm_refl. Qed.
Lemma D_60e80 : decode_any W_60e80 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 368%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e84 : bv 32 := @BV 32 0x16913423%Z I.
Lemma F_60e84 : fetch_word Plain.M.loaded_segments (@BV 64 0x60ee4%Z I : word) = Some W_60e84.
Proof. vm_refl. Qed.
Lemma D_60e84 : decode_any W_60e84 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 360%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e88 : bv 32 := @BV 32 0x17213023%Z I.
Lemma F_60e88 : fetch_word Plain.M.loaded_segments (@BV 64 0x60ee8%Z I : word) = Some W_60e88.
Proof. vm_refl. Qed.
Lemma D_60e88 : decode_any W_60e88 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 352%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e8c : bv 32 := @BV 32 0x00058413%Z I.
Lemma F_60e8c : fetch_word Plain.M.loaded_segments (@BV 64 0x60eec%Z I : word) = Some W_60e8c.
Proof. vm_refl. Qed.
Lemma D_60e8c : decode_any W_60e8c = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e90 : bv 32 := @BV 32 0x00050493%Z I.
Lemma F_60e90 : fetch_word Plain.M.loaded_segments (@BV 64 0x60ef0%Z I : word) = Some W_60e90.
Proof. vm_refl. Qed.
Lemma D_60e90 : decode_any W_60e90 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e94 : bv 32 := @BV 32 0x03010513%Z I.
Lemma F_60e94 : fetch_word Plain.M.loaded_segments (@BV 64 0x60ef4%Z I : word) = Some W_60e94.
Proof. vm_refl. Qed.
Lemma D_60e94 : decode_any W_60e94 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 2%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e98 : bv 32 := @BV 32 0x13000613%Z I.
Lemma F_60e98 : fetch_word Plain.M.loaded_segments (@BV 64 0x60ef8%Z I : word) = Some W_60e98.
Proof. vm_refl. Qed.
Lemma D_60e98 : decode_any W_60e98 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 304%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e9c : bv 32 := @BV 32 0x00000593%Z I.
Lemma F_60e9c : fetch_word Plain.M.loaded_segments (@BV 64 0x60efc%Z I : word) = Some W_60e9c.
Proof. vm_refl. Qed.
Lemma D_60e9c : decode_any W_60e9c = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ea0 : bv 32 := @BV 32 0x2c00e0ef%Z I.
Lemma F_60ea0 : fetch_word Plain.M.loaded_segments (@BV 64 0x60f00%Z I : word) = Some W_60ea0.
Proof. vm_refl. Qed.
Lemma D_60ea0 : decode_any W_60ea0 = Some (Jal (@BV 5 1%Z I) (@BV 21 58048%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ea4 : bv 32 := @BV 32 0x00013517%Z I.
Lemma F_60ea4 : fetch_word Plain.M.loaded_segments (@BV 64 0x60f04%Z I : word) = Some W_60ea4.
Proof. vm_refl. Qed.
Lemma D_60ea4 : decode_any W_60ea4 = Some (Auipc (@BV 5 10%Z I) (@BV 20 19%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ea8 : bv 32 := @BV 32 0x7c453503%Z I.
Lemma F_60ea8 : fetch_word Plain.M.loaded_segments (@BV 64 0x60f08%Z I : word) = Some W_60ea8.
Proof. vm_refl. Qed.
Lemma D_60ea8 : decode_any W_60ea8 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 1988%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60eac : bv 32 := @BV 32 0x00953023%Z I.
Lemma F_60eac : fetch_word Plain.M.loaded_segments (@BV 64 0x60f0c%Z I : word) = Some W_60eac.
Proof. vm_refl. Qed.
Lemma D_60eac : decode_any W_60eac = Some (Store SZ8 (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60eb0 : bv 32 := @BV 32 0x0004b503%Z I.
Lemma F_60eb0 : fetch_word Plain.M.loaded_segments (@BV 64 0x60f10%Z I : word) = Some W_60eb0.
Proof. vm_refl. Qed.
Lemma D_60eb0 : decode_any W_60eb0 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60eb4 : bv 32 := @BV 32 0x00848493%Z I.
Lemma F_60eb4 : fetch_word Plain.M.loaded_segments (@BV 64 0x60f14%Z I : word) = Some W_60eb4.
Proof. vm_refl. Qed.
Lemma D_60eb4 : decode_any W_60eb4 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 9%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60eb8 : bv 32 := @BV 32 0xfe051ce3%Z I.
Lemma F_60eb8 : fetch_word Plain.M.loaded_segments (@BV 64 0x60f18%Z I : word) = Some W_60eb8.
Proof. vm_refl. Qed.
Lemma D_60eb8 : decode_any W_60eb8 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 8184%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ebc : bv 32 := @BV 32 0x00046517%Z I.
Lemma F_60ebc : fetch_word Plain.M.loaded_segments (@BV 64 0x60f1c%Z I : word) = Some W_60ebc.
Proof. vm_refl. Qed.
Lemma D_60ebc : decode_any W_60ebc = Some (Auipc (@BV 5 10%Z I) (@BV 20 70%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ec0 : bv 32 := @BV 32 0x89450913%Z I.
Lemma F_60ec0 : fetch_word Plain.M.loaded_segments (@BV 64 0x60f20%Z I : word) = Some W_60ec0.
Proof. vm_refl. Qed.
Lemma D_60ec0 : decode_any W_60ec0 = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 10%Z I) (@BV 12 2196%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ec4 : bv 32 := @BV 32 0x00993423%Z I.
Lemma F_60ec4 : fetch_word Plain.M.loaded_segments (@BV 64 0x60f24%Z I : word) = Some W_60ec4.
Proof. vm_refl. Qed.
Lemma D_60ec4 : decode_any W_60ec4 = Some (Store SZ8 (@BV 5 18%Z I) (@BV 5 9%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ec8 : bv 32 := @BV 32 0x0004b583%Z I.
Lemma F_60ec8 : fetch_word Plain.M.loaded_segments (@BV 64 0x60f28%Z I : word) = Some W_60ec8.
Proof. vm_refl. Qed.
Lemma D_60ec8 : decode_any W_60ec8 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ecc : bv 32 := @BV 32 0x04058c63%Z I.
Lemma F_60ecc : fetch_word Plain.M.loaded_segments (@BV 64 0x60f2c%Z I : word) = Some W_60ecc.
Proof. vm_refl. Qed.
Lemma D_60ecc : decode_any W_60ecc = Some (Branch BC_EQ (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 88%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ed0 : bv 32 := @BV 32 0x01048493%Z I.
Lemma F_60ed0 : fetch_word Plain.M.loaded_segments (@BV 64 0x60f30%Z I : word) = Some W_60ed0.
Proof. vm_refl. Qed.
Lemma D_60ed0 : decode_any W_60ed0 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 9%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ed4 : bv 32 := @BV 32 0x02500513%Z I.
Lemma F_60ed4 : fetch_word Plain.M.loaded_segments (@BV 64 0x60f34%Z I : word) = Some W_60ed4.
Proof. vm_refl. Qed.
Lemma D_60ed4 : decode_any W_60ed4 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 37%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ed8 : bv 32 := @BV 32 0x03010613%Z I.
Lemma F_60ed8 : fetch_word Plain.M.loaded_segments (@BV 64 0x60f38%Z I : word) = Some W_60ed8.
Proof. vm_refl. Qed.
Lemma D_60ed8 : decode_any W_60ed8 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 2%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60edc : bv 32 := @BV 32 0x0100006f%Z I.
Lemma F_60edc : fetch_word Plain.M.loaded_segments (@BV 64 0x60f3c%Z I : word) = Some W_60edc.
Proof. vm_refl. Qed.
Lemma D_60edc : decode_any W_60edc = Some (Jal (@BV 5 0%Z I) (@BV 21 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ee0 : bv 32 := @BV 32 0x0004b583%Z I.
Lemma F_60ee0 : fetch_word Plain.M.loaded_segments (@BV 64 0x60f40%Z I : word) = Some W_60ee0.
Proof. vm_refl. Qed.
Lemma D_60ee0 : decode_any W_60ee0 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ee4 : bv 32 := @BV 32 0x01048493%Z I.
Lemma F_60ee4 : fetch_word Plain.M.loaded_segments (@BV 64 0x60f44%Z I : word) = Some W_60ee4.
Proof. vm_refl. Qed.
Lemma D_60ee4 : decode_any W_60ee4 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 9%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ee8 : bv 32 := @BV 32 0x00058e63%Z I.
Lemma F_60ee8 : fetch_word Plain.M.loaded_segments (@BV 64 0x60f48%Z I : word) = Some W_60ee8.
Proof. vm_refl. Qed.
Lemma D_60ee8 : decode_any W_60ee8 = Some (Branch BC_EQ (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 28%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60eec : bv 32 := @BV 32 0xfeb56ae3%Z I.
Lemma F_60eec : fetch_word Plain.M.loaded_segments (@BV 64 0x60f4c%Z I : word) = Some W_60eec.
Proof. vm_refl. Qed.
Lemma D_60eec : decode_any W_60eec = Some (Branch BC_LTU (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 13 8180%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ef0 : bv 32 := @BV 32 0xff84b683%Z I.
Lemma F_60ef0 : fetch_word Plain.M.loaded_segments (@BV 64 0x60f50%Z I : word) = Some W_60ef0.
Proof. vm_refl. Qed.
Lemma D_60ef0 : decode_any W_60ef0 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 9%Z I) (@BV 12 4088%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ef4 : bv 32 := @BV 32 0x00359593%Z I.
Lemma F_60ef4 : fetch_word Plain.M.loaded_segments (@BV 64 0x60f54%Z I : word) = Some W_60ef4.
Proof. vm_refl. Qed.
Lemma D_60ef4 : decode_any W_60ef4 = Some (ShiftImm ALU_SLL (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 6 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ef8 : bv 32 := @BV 32 0x00b605b3%Z I.
Lemma F_60ef8 : fetch_word Plain.M.loaded_segments (@BV 64 0x60f58%Z I : word) = Some W_60ef8.
Proof. vm_refl. Qed.
Lemma D_60ef8 : decode_any W_60ef8 = Some (Op ALU_ADD (@BV 5 11%Z I) (@BV 5 12%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60efc : bv 32 := @BV 32 0x00d5b023%Z I.
Lemma F_60efc : fetch_word Plain.M.loaded_segments (@BV 64 0x60f5c%Z I : word) = Some W_60efc.
Proof. vm_refl. Qed.
Lemma D_60efc : decode_any W_60efc = Some (Store SZ8 (@BV 5 11%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f00 : bv 32 := @BV 32 0xfe1ff06f%Z I.
Lemma F_60f00 : fetch_word Plain.M.loaded_segments (@BV 64 0x60f60%Z I : word) = Some W_60f00.
Proof. vm_refl. Qed.
Lemma D_60f00 : decode_any W_60f00 = Some (Jal (@BV 5 0%Z I) (@BV 21 2097120%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f04 : bv 32 := @BV 32 0x0b013583%Z I.
Lemma F_60f04 : fetch_word Plain.M.loaded_segments (@BV 64 0x60f64%Z I : word) = Some W_60f04.
Proof. vm_refl. Qed.
Lemma D_60f04 : decode_any W_60f04 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 2%Z I) (@BV 12 176%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f08 : bv 32 := @BV 32 0x13013503%Z I.
Lemma F_60f08 : fetch_word Plain.M.loaded_segments (@BV 64 0x60f68%Z I : word) = Some W_60f08.
Proof. vm_refl. Qed.
Lemma D_60f08 : decode_any W_60f08 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 2%Z I) (@BV 12 304%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f0c : bv 32 := @BV 32 0x00046617%Z I.
Lemma F_60f0c : fetch_word Plain.M.loaded_segments (@BV 64 0x60f6c%Z I : word) = Some W_60f0c.
Proof. vm_refl. Qed.
Lemma D_60f0c : decode_any W_60f0c = Some (Auipc (@BV 5 12%Z I) (@BV 20 70%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f10 : bv 32 := @BV 32 0x8ab63623%Z I.
Lemma F_60f10 : fetch_word Plain.M.loaded_segments (@BV 64 0x60f70%Z I : word) = Some W_60f10.
Proof. vm_refl. Qed.
Lemma D_60f10 : decode_any W_60f10 = Some (Store SZ8 (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 12 2220%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f14 : bv 32 := @BV 32 0x00050c63%Z I.
Lemma F_60f14 : fetch_word Plain.M.loaded_segments (@BV 64 0x60f74%Z I : word) = Some W_60f14.
Proof. vm_refl. Qed.
Lemma D_60f14 : decode_any W_60f14 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f2c : bv 32 := @BV 32 0x06013503%Z I.
Lemma F_60f2c : fetch_word Plain.M.loaded_segments (@BV 64 0x60f8c%Z I : word) = Some W_60f2c.
Proof. vm_refl. Qed.
Lemma D_60f2c : decode_any W_60f2c = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 2%Z I) (@BV 12 96%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f30 : bv 32 := @BV 32 0x02a93823%Z I.
Lemma F_60f30 : fetch_word Plain.M.loaded_segments (@BV 64 0x60f90%Z I : word) = Some W_60f30.
Proof. vm_refl. Qed.
Lemma D_60f30 : decode_any W_60f30 = Some (Store SZ8 (@BV 5 18%Z I) (@BV 5 10%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f34 : bv 32 := @BV 32 0x00041463%Z I.
Lemma F_60f34 : fetch_word Plain.M.loaded_segments (@BV 64 0x60f94%Z I : word) = Some W_60f34.
Proof. vm_refl. Qed.
Lemma D_60f34 : decode_any W_60f34 = Some (Branch BC_NE (@BV 5 8%Z I) (@BV 5 0%Z I) (@BV 13 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f3c : bv 32 := @BV 32 0x00041663%Z I.
Lemma F_60f3c : fetch_word Plain.M.loaded_segments (@BV 64 0x60f9c%Z I : word) = Some W_60f3c.
Proof. vm_refl. Qed.
Lemma D_60f3c : decode_any W_60f3c = Some (Branch BC_NE (@BV 5 8%Z I) (@BV 5 0%Z I) (@BV 13 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f48 : bv 32 := @BV 32 0x00013517%Z I.
Lemma F_60f48 : fetch_word Plain.M.loaded_segments (@BV 64 0x60fa8%Z I : word) = Some W_60f48.
Proof. vm_refl. Qed.
Lemma D_60f48 : decode_any W_60f48 = Some (Auipc (@BV 5 10%Z I) (@BV 20 19%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f4c : bv 32 := @BV 32 0x72853583%Z I.
Lemma F_60f4c : fetch_word Plain.M.loaded_segments (@BV 64 0x60fac%Z I : word) = Some W_60f4c.
Proof. vm_refl. Qed.
Lemma D_60f4c : decode_any W_60f4c = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 1832%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f50 : bv 32 := @BV 32 0x00013517%Z I.
Lemma F_60f50 : fetch_word Plain.M.loaded_segments (@BV 64 0x60fb0%Z I : word) = Some W_60f50.
Proof. vm_refl. Qed.
Lemma D_60f50 : decode_any W_60f50 = Some (Auipc (@BV 5 10%Z I) (@BV 20 19%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f54 : bv 32 := @BV 32 0x72853503%Z I.
Lemma F_60f54 : fetch_word Plain.M.loaded_segments (@BV 64 0x60fb4%Z I : word) = Some W_60f54.
Proof. vm_refl. Qed.
Lemma D_60f54 : decode_any W_60f54 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 1832%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f58 : bv 32 := @BV 32 0x0085b023%Z I.
Lemma F_60f58 : fetch_word Plain.M.loaded_segments (@BV 64 0x60fb8%Z I : word) = Some W_60f58.
Proof. vm_refl. Qed.
Lemma D_60f58 : decode_any W_60f58 = Some (Store SZ8 (@BV 5 11%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f5c : bv 32 := @BV 32 0x00140593%Z I.
Lemma F_60f5c : fetch_word Plain.M.loaded_segments (@BV 64 0x60fbc%Z I : word) = Some W_60f5c.
Proof. vm_refl. Qed.
Lemma D_60f5c : decode_any W_60f5c = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 8%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f60 : bv 32 := @BV 32 0x00853023%Z I.
Lemma F_60f60 : fetch_word Plain.M.loaded_segments (@BV 64 0x60fc0%Z I : word) = Some W_60f60.
Proof. vm_refl. Qed.
Lemma D_60f60 : decode_any W_60f60 = Some (Store SZ8 (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f64 : bv 32 := @BV 32 0x02f00613%Z I.
Lemma F_60f64 : fetch_word Plain.M.loaded_segments (@BV 64 0x60fc4%Z I : word) = Some W_60f64.
Proof. vm_refl. Qed.
Lemma D_60f64 : decode_any W_60f64 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 47%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f68 : bv 32 := @BV 32 0x00c0006f%Z I.
Lemma F_60f68 : fetch_word Plain.M.loaded_segments (@BV 64 0x60fc8%Z I : word) = Some W_60f68.
Proof. vm_refl. Qed.
Lemma D_60f68 : decode_any W_60f68 = Some (Jal (@BV 5 0%Z I) (@BV 21 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f6c : bv 32 := @BV 32 0x00b53023%Z I.
Lemma F_60f6c : fetch_word Plain.M.loaded_segments (@BV 64 0x60fcc%Z I : word) = Some W_60f6c.
Proof. vm_refl. Qed.
Lemma D_60f6c : decode_any W_60f6c = Some (Store SZ8 (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f70 : bv 32 := @BV 32 0x00158593%Z I.
Lemma F_60f70 : fetch_word Plain.M.loaded_segments (@BV 64 0x60fd0%Z I : word) = Some W_60f70.
Proof. vm_refl. Qed.
Lemma D_60f70 : decode_any W_60f70 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f74 : bv 32 := @BV 32 0xfff5c683%Z I.
Lemma F_60f74 : fetch_word Plain.M.loaded_segments (@BV 64 0x60fd4%Z I : word) = Some W_60f74.
Proof. vm_refl. Qed.
Lemma D_60f74 : decode_any W_60f74 = Some (Load SZ1 false (@BV 5 13%Z I) (@BV 5 11%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f78 : bv 32 := @BV 32 0xfec68ae3%Z I.
Lemma F_60f78 : fetch_word Plain.M.loaded_segments (@BV 64 0x60fd8%Z I : word) = Some W_60f78.
Proof. vm_refl. Qed.
Lemma D_60f78 : decode_any W_60f78 = Some (Branch BC_EQ (@BV 5 13%Z I) (@BV 5 12%Z I) (@BV 13 8180%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f7c : bv 32 := @BV 32 0xfe069ae3%Z I.
Lemma F_60f7c : fetch_word Plain.M.loaded_segments (@BV 64 0x60fdc%Z I : word) = Some W_60f7c.
Proof. vm_refl. Qed.
Lemma D_60f7c : decode_any W_60f7c = Some (Branch BC_NE (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 13 8180%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f80 : bv 32 := @BV 32 0x03010513%Z I.
Lemma F_60f80 : fetch_word Plain.M.loaded_segments (@BV 64 0x60fe0%Z I : word) = Some W_60f80.
Proof. vm_refl. Qed.
Lemma D_60f80 : decode_any W_60f80 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 2%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f84 : bv 32 := @BV 32 0x214000ef%Z I.
Lemma F_60f84 : fetch_word Plain.M.loaded_segments (@BV 64 0x60fe4%Z I : word) = Some W_60f84.
Proof. vm_refl. Qed.
Lemma D_60f84 : decode_any W_60f84 = Some (Jal (@BV 5 1%Z I) (@BV 21 532%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f88 : bv 32 := @BV 32 0x0f813503%Z I.
Lemma F_60f88 : fetch_word Plain.M.loaded_segments (@BV 64 0x60fe8%Z I : word) = Some W_60f88.
Proof. vm_refl. Qed.
Lemma D_60f88 : decode_any W_60f88 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 2%Z I) (@BV 12 248%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f8c : bv 32 := @BV 32 0x0e5000ef%Z I.
Lemma F_60f8c : fetch_word Plain.M.loaded_segments (@BV 64 0x60fec%Z I : word) = Some W_60f8c.
Proof. vm_refl. Qed.
Lemma D_60f8c : decode_any W_60f8c = Some (Jal (@BV 5 1%Z I) (@BV 21 2276%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f90 : bv 32 := @BV 32 0x08813503%Z I.
Lemma F_60f90 : fetch_word Plain.M.loaded_segments (@BV 64 0x60ff0%Z I : word) = Some W_60f90.
Proof. vm_refl. Qed.
Lemma D_60f90 : decode_any W_60f90 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 2%Z I) (@BV 12 136%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f94 : bv 32 := @BV 32 0x09013583%Z I.
Lemma F_60f94 : fetch_word Plain.M.loaded_segments (@BV 64 0x60ff4%Z I : word) = Some W_60f94.
Proof. vm_refl. Qed.
Lemma D_60f94 : decode_any W_60f94 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 2%Z I) (@BV 12 144%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f98 : bv 32 := @BV 32 0x00b51c63%Z I.
Lemma F_60f98 : fetch_word Plain.M.loaded_segments (@BV 64 0x60ff8%Z I : word) = Some W_60f98.
Proof. vm_refl. Qed.
Lemma D_60f98 : decode_any W_60f98 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 13 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60f9c : bv 32 := @BV 32 0x09813503%Z I.
Lemma F_60f9c : fetch_word Plain.M.loaded_segments (@BV 64 0x60ffc%Z I : word) = Some W_60f9c.
Proof. vm_refl. Qed.
Lemma D_60f9c : decode_any W_60f9c = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 2%Z I) (@BV 12 152%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60fa0 : bv 32 := @BV 32 0x0a013583%Z I.
Lemma F_60fa0 : fetch_word Plain.M.loaded_segments (@BV 64 0x61000%Z I : word) = Some W_60fa0.
Proof. vm_refl. Qed.
Lemma D_60fa0 : decode_any W_60fa0 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 2%Z I) (@BV 12 160%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60fa4 : bv 32 := @BV 32 0x00b51663%Z I.
Lemma F_60fa4 : fetch_word Plain.M.loaded_segments (@BV 64 0x61004%Z I : word) = Some W_60fa4.
Proof. vm_refl. Qed.
Lemma D_60fa4 : decode_any W_60fa4 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 13 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60fa8 : bv 32 := @BV 32 0x0e813503%Z I.
Lemma F_60fa8 : fetch_word Plain.M.loaded_segments (@BV 64 0x61008%Z I : word) = Some W_60fa8.
Proof. vm_refl. Qed.
Lemma D_60fa8 : decode_any W_60fa8 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 2%Z I) (@BV 12 232%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60fac : bv 32 := @BV 32 0x0e050063%Z I.
Lemma F_60fac : fetch_word Plain.M.loaded_segments (@BV 64 0x6100c%Z I : word) = Some W_60fac.
Proof. vm_refl. Qed.
Lemma D_60fac : decode_any W_60fac = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 224%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6108c : bv 32 := @BV 32 0x17813083%Z I.
Lemma F_6108c : fetch_word Plain.M.loaded_segments (@BV 64 0x610ec%Z I : word) = Some W_6108c.
Proof. vm_refl. Qed.
Lemma D_6108c : decode_any W_6108c = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 376%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61090 : bv 32 := @BV 32 0x17013403%Z I.
Lemma F_61090 : fetch_word Plain.M.loaded_segments (@BV 64 0x610f0%Z I : word) = Some W_61090.
Proof. vm_refl. Qed.
Lemma D_61090 : decode_any W_61090 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 368%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61094 : bv 32 := @BV 32 0x16813483%Z I.
Lemma F_61094 : fetch_word Plain.M.loaded_segments (@BV 64 0x610f4%Z I : word) = Some W_61094.
Proof. vm_refl. Qed.
Lemma D_61094 : decode_any W_61094 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 360%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61098 : bv 32 := @BV 32 0x16013903%Z I.
Lemma F_61098 : fetch_word Plain.M.loaded_segments (@BV 64 0x610f8%Z I : word) = Some W_61098.
Proof. vm_refl. Qed.
Lemma D_61098 : decode_any W_61098 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 352%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6109c : bv 32 := @BV 32 0x18010113%Z I.
Lemma F_6109c : fetch_word Plain.M.loaded_segments (@BV 64 0x610fc%Z I : word) = Some W_6109c.
Proof. vm_refl. Qed.
Lemma D_6109c : decode_any W_6109c = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 384%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610a0 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_610a0 : fetch_word Plain.M.loaded_segments (@BV 64 0x61100%Z I : word) = Some W_610a0.
Proof. vm_refl. Qed.
Lemma D_610a0 : decode_any W_610a0 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610a4 : bv 32 := @BV 32 0xfe010113%Z I.
Lemma F_610a4 : fetch_word Plain.M.loaded_segments (@BV 64 0x61104%Z I : word) = Some W_610a4.
Proof. vm_refl. Qed.
Lemma D_610a4 : decode_any W_610a4 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4064%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610a8 : bv 32 := @BV 32 0x00113c23%Z I.
Lemma F_610a8 : fetch_word Plain.M.loaded_segments (@BV 64 0x61108%Z I : word) = Some W_610a8.
Proof. vm_refl. Qed.
Lemma D_610a8 : decode_any W_610a8 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610ac : bv 32 := @BV 32 0x00813823%Z I.
Lemma F_610ac : fetch_word Plain.M.loaded_segments (@BV 64 0x6110c%Z I : word) = Some W_610ac.
Proof. vm_refl. Qed.
Lemma D_610ac : decode_any W_610ac = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610b0 : bv 32 := @BV 32 0x00913423%Z I.
Lemma F_610b0 : fetch_word Plain.M.loaded_segments (@BV 64 0x61110%Z I : word) = Some W_610b0.
Proof. vm_refl. Qed.
Lemma D_610b0 : decode_any W_610b0 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610b4 : bv 32 := @BV 32 0xdc1ff0ef%Z I.
Lemma F_610b4 : fetch_word Plain.M.loaded_segments (@BV 64 0x61114%Z I : word) = Some W_610b4.
Proof. vm_refl. Qed.
Lemma D_610b4 : decode_any W_610b4 = Some (Jal (@BV 5 1%Z I) (@BV 21 2096576%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610b8 : bv 32 := @BV 32 0x00013517%Z I.
Lemma F_610b8 : fetch_word Plain.M.loaded_segments (@BV 64 0x61118%Z I : word) = Some W_610b8.
Proof. vm_refl. Qed.
Lemma D_610b8 : decode_any W_610b8 = Some (Auipc (@BV 5 10%Z I) (@BV 20 19%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610bc : bv 32 := @BV 32 0x00013597%Z I.
Lemma F_610bc : fetch_word Plain.M.loaded_segments (@BV 64 0x6111c%Z I : word) = Some W_610bc.
Proof. vm_refl. Qed.
Lemma D_610bc : decode_any W_610bc = Some (Auipc (@BV 5 11%Z I) (@BV 20 19%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610c0 : bv 32 := @BV 32 0x5c853403%Z I.
Lemma F_610c0 : fetch_word Plain.M.loaded_segments (@BV 64 0x61120%Z I : word) = Some W_610c0.
Proof. vm_refl. Qed.
Lemma D_610c0 : decode_any W_610c0 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 10%Z I) (@BV 12 1480%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610c4 : bv 32 := @BV 32 0x5cc5b483%Z I.
Lemma F_610c4 : fetch_word Plain.M.loaded_segments (@BV 64 0x61124%Z I : word) = Some W_610c4.
Proof. vm_refl. Qed.
Lemma D_610c4 : decode_any W_610c4 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 11%Z I) (@BV 12 1484%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610c8 : bv 32 := @BV 32 0x0084fa63%Z I.
Lemma F_610c8 : fetch_word Plain.M.loaded_segments (@BV 64 0x61128%Z I : word) = Some W_610c8.
Proof. vm_refl. Qed.
Lemma D_610c8 : decode_any W_610c8 = Some (Branch BC_GEU (@BV 5 9%Z I) (@BV 5 8%Z I) (@BV 13 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610cc : bv 32 := @BV 32 0x0004b503%Z I.
Lemma F_610cc : fetch_word Plain.M.loaded_segments (@BV 64 0x6112c%Z I : word) = Some W_610cc.
Proof. vm_refl. Qed.
Lemma D_610cc : decode_any W_610cc = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610d0 : bv 32 := @BV 32 0x000500e7%Z I.
Lemma F_610d0 : fetch_word Plain.M.loaded_segments (@BV 64 0x61130%Z I : word) = Some W_610d0.
Proof. vm_refl. Qed.
Lemma D_610d0 : decode_any W_610d0 = Some (Jalr (@BV 5 1%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610d4 : bv 32 := @BV 32 0x00848493%Z I.
Lemma F_610d4 : fetch_word Plain.M.loaded_segments (@BV 64 0x61134%Z I : word) = Some W_610d4.
Proof. vm_refl. Qed.
Lemma D_610d4 : decode_any W_610d4 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 9%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610d8 : bv 32 := @BV 32 0xfe84eae3%Z I.
Lemma F_610d8 : fetch_word Plain.M.loaded_segments (@BV 64 0x61138%Z I : word) = Some W_610d8.
Proof. vm_refl. Qed.
Lemma D_610d8 : decode_any W_610d8 = Some (Branch BC_LTU (@BV 5 9%Z I) (@BV 5 8%Z I) (@BV 13 8180%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610dc : bv 32 := @BV 32 0x01813083%Z I.
Lemma F_610dc : fetch_word Plain.M.loaded_segments (@BV 64 0x6113c%Z I : word) = Some W_610dc.
Proof. vm_refl. Qed.
Lemma D_610dc : decode_any W_610dc = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610e0 : bv 32 := @BV 32 0x01013403%Z I.
Lemma F_610e0 : fetch_word Plain.M.loaded_segments (@BV 64 0x61140%Z I : word) = Some W_610e0.
Proof. vm_refl. Qed.
Lemma D_610e0 : decode_any W_610e0 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610e4 : bv 32 := @BV 32 0x00813483%Z I.
Lemma F_610e4 : fetch_word Plain.M.loaded_segments (@BV 64 0x61144%Z I : word) = Some W_610e4.
Proof. vm_refl. Qed.
Lemma D_610e4 : decode_any W_610e4 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610e8 : bv 32 := @BV 32 0x02010113%Z I.
Lemma F_610e8 : fetch_word Plain.M.loaded_segments (@BV 64 0x61148%Z I : word) = Some W_610e8.
Proof. vm_refl. Qed.
Lemma D_610e8 : decode_any W_610e8 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610ec : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_610ec : fetch_word Plain.M.loaded_segments (@BV 64 0x6114c%Z I : word) = Some W_610ec.
Proof. vm_refl. Qed.
Lemma D_610ec : decode_any W_610ec = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610f0 : bv 32 := @BV 32 0xfe010113%Z I.
Lemma F_610f0 : fetch_word Plain.M.loaded_segments (@BV 64 0x61150%Z I : word) = Some W_610f0.
Proof. vm_refl. Qed.
Lemma D_610f0 : decode_any W_610f0 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4064%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610f4 : bv 32 := @BV 32 0x00113c23%Z I.
Lemma F_610f4 : fetch_word Plain.M.loaded_segments (@BV 64 0x61154%Z I : word) = Some W_610f4.
Proof. vm_refl. Qed.
Lemma D_610f4 : decode_any W_610f4 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610f8 : bv 32 := @BV 32 0x00813823%Z I.
Lemma F_610f8 : fetch_word Plain.M.loaded_segments (@BV 64 0x61158%Z I : word) = Some W_610f8.
Proof. vm_refl. Qed.
Lemma D_610f8 : decode_any W_610f8 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610fc : bv 32 := @BV 32 0x00913423%Z I.
Lemma F_610fc : fetch_word Plain.M.loaded_segments (@BV 64 0x6115c%Z I : word) = Some W_610fc.
Proof. vm_refl. Qed.
Lemma D_610fc : decode_any W_610fc = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61100 : bv 32 := @BV 32 0x01213023%Z I.
Lemma F_61100 : fetch_word Plain.M.loaded_segments (@BV 64 0x61160%Z I : word) = Some W_61100.
Proof. vm_refl. Qed.
Lemma D_61100 : decode_any W_61100 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61104 : bv 32 := @BV 32 0x00060413%Z I.
Lemma F_61104 : fetch_word Plain.M.loaded_segments (@BV 64 0x61164%Z I : word) = Some W_61104.
Proof. vm_refl. Qed.
Lemma D_61104 : decode_any W_61104 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61108 : bv 32 := @BV 32 0x00058493%Z I.
Lemma F_61108 : fetch_word Plain.M.loaded_segments (@BV 64 0x61168%Z I : word) = Some W_61108.
Proof. vm_refl. Qed.
Lemma D_61108 : decode_any W_61108 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6110c : bv 32 := @BV 32 0x00050913%Z I.
Lemma F_6110c : fetch_word Plain.M.loaded_segments (@BV 64 0x6116c%Z I : word) = Some W_6110c.
Proof. vm_refl. Qed.
Lemma D_6110c : decode_any W_6110c = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61110 : bv 32 := @BV 32 0x00063583%Z I.
Lemma F_61110 : fetch_word Plain.M.loaded_segments (@BV 64 0x61170%Z I : word) = Some W_61110.
Proof. vm_refl. Qed.
Lemma D_61110 : decode_any W_61110 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61114 : bv 32 := @BV 32 0x00349513%Z I.
Lemma F_61114 : fetch_word Plain.M.loaded_segments (@BV 64 0x61174%Z I : word) = Some W_61114.
Proof. vm_refl. Qed.
Lemma D_61114 : decode_any W_61114 = Some (ShiftImm ALU_SLL (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 6 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61118 : bv 32 := @BV 32 0x00a60533%Z I.
Lemma F_61118 : fetch_word Plain.M.loaded_segments (@BV 64 0x61178%Z I : word) = Some W_61118.
Proof. vm_refl. Qed.
Lemma D_61118 : decode_any W_61118 = Some (Op ALU_ADD (@BV 5 10%Z I) (@BV 5 12%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6111c : bv 32 := @BV 32 0x00850513%Z I.
Lemma F_6111c : fetch_word Plain.M.loaded_segments (@BV 64 0x6117c%Z I : word) = Some W_6111c.
Proof. vm_refl. Qed.
Lemma D_6111c : decode_any W_6111c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61120 : bv 32 := @BV 32 0xd59ff0ef%Z I.
Lemma F_61120 : fetch_word Plain.M.loaded_segments (@BV 64 0x61180%Z I : word) = Some W_61120.
Proof. vm_refl. Qed.
Lemma D_61120 : decode_any W_61120 = Some (Jal (@BV 5 1%Z I) (@BV 21 2096472%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61124 : bv 32 := @BV 32 0x00000517%Z I.
Lemma F_61124 : fetch_word Plain.M.loaded_segments (@BV 64 0x61184%Z I : word) = Some W_61124.
Proof. vm_refl. Qed.
Lemma D_61124 : decode_any W_61124 = Some (Auipc (@BV 5 10%Z I) (@BV 20 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61128 : bv 32 := @BV 32 0x02c50313%Z I.
Lemma F_61128 : fetch_word Plain.M.loaded_segments (@BV 64 0x61188%Z I : word) = Some W_61128.
Proof. vm_refl. Qed.
Lemma D_61128 : decode_any W_61128 = Some (OpImm ALU_ADD (@BV 5 6%Z I) (@BV 5 10%Z I) (@BV 12 44%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6112c : bv 32 := @BV 32 0x00090513%Z I.
Lemma F_6112c : fetch_word Plain.M.loaded_segments (@BV 64 0x6118c%Z I : word) = Some W_6112c.
Proof. vm_refl. Qed.
Lemma D_6112c : decode_any W_6112c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61130 : bv 32 := @BV 32 0x00048593%Z I.
Lemma F_61130 : fetch_word Plain.M.loaded_segments (@BV 64 0x61190%Z I : word) = Some W_61130.
Proof. vm_refl. Qed.
Lemma D_61130 : decode_any W_61130 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61134 : bv 32 := @BV 32 0x00040613%Z I.
Lemma F_61134 : fetch_word Plain.M.loaded_segments (@BV 64 0x61194%Z I : word) = Some W_61134.
Proof. vm_refl. Qed.
Lemma D_61134 : decode_any W_61134 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61138 : bv 32 := @BV 32 0x01813083%Z I.
Lemma F_61138 : fetch_word Plain.M.loaded_segments (@BV 64 0x61198%Z I : word) = Some W_61138.
Proof. vm_refl. Qed.
Lemma D_61138 : decode_any W_61138 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6113c : bv 32 := @BV 32 0x01013403%Z I.
Lemma F_6113c : fetch_word Plain.M.loaded_segments (@BV 64 0x6119c%Z I : word) = Some W_6113c.
Proof. vm_refl. Qed.
Lemma D_6113c : decode_any W_6113c = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61140 : bv 32 := @BV 32 0x00813483%Z I.
Lemma F_61140 : fetch_word Plain.M.loaded_segments (@BV 64 0x611a0%Z I : word) = Some W_61140.
Proof. vm_refl. Qed.
Lemma D_61140 : decode_any W_61140 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61144 : bv 32 := @BV 32 0x00013903%Z I.
Lemma F_61144 : fetch_word Plain.M.loaded_segments (@BV 64 0x611a4%Z I : word) = Some W_61144.
Proof. vm_refl. Qed.
Lemma D_61144 : decode_any W_61144 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61148 : bv 32 := @BV 32 0x02010113%Z I.
Lemma F_61148 : fetch_word Plain.M.loaded_segments (@BV 64 0x611a8%Z I : word) = Some W_61148.
Proof. vm_refl. Qed.
Lemma D_61148 : decode_any W_61148 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6114c : bv 32 := @BV 32 0x00030067%Z I.
Lemma F_6114c : fetch_word Plain.M.loaded_segments (@BV 64 0x611ac%Z I : word) = Some W_6114c.
Proof. vm_refl. Qed.
Lemma D_6114c : decode_any W_6114c = Some (Jalr (@BV 5 0%Z I) (@BV 5 6%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61150 : bv 32 := @BV 32 0xfd010113%Z I.
Lemma F_61150 : fetch_word Plain.M.loaded_segments (@BV 64 0x611b0%Z I : word) = Some W_61150.
Proof. vm_refl. Qed.
Lemma D_61150 : decode_any W_61150 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4048%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61154 : bv 32 := @BV 32 0x02113423%Z I.
Lemma F_61154 : fetch_word Plain.M.loaded_segments (@BV 64 0x611b4%Z I : word) = Some W_61154.
Proof. vm_refl. Qed.
Lemma D_61154 : decode_any W_61154 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61158 : bv 32 := @BV 32 0x02813023%Z I.
Lemma F_61158 : fetch_word Plain.M.loaded_segments (@BV 64 0x611b8%Z I : word) = Some W_61158.
Proof. vm_refl. Qed.
Lemma D_61158 : decode_any W_61158 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6115c : bv 32 := @BV 32 0x00913c23%Z I.
Lemma F_6115c : fetch_word Plain.M.loaded_segments (@BV 64 0x611bc%Z I : word) = Some W_6115c.
Proof. vm_refl. Qed.
Lemma D_6115c : decode_any W_6115c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61160 : bv 32 := @BV 32 0x01213823%Z I.
Lemma F_61160 : fetch_word Plain.M.loaded_segments (@BV 64 0x611c0%Z I : word) = Some W_61160.
Proof. vm_refl. Qed.
Lemma D_61160 : decode_any W_61160 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61164 : bv 32 := @BV 32 0x01313423%Z I.
Lemma F_61164 : fetch_word Plain.M.loaded_segments (@BV 64 0x611c4%Z I : word) = Some W_61164.
Proof. vm_refl. Qed.
Lemma D_61164 : decode_any W_61164 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 19%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61168 : bv 32 := @BV 32 0x00060413%Z I.
Lemma F_61168 : fetch_word Plain.M.loaded_segments (@BV 64 0x611c8%Z I : word) = Some W_61168.
Proof. vm_refl. Qed.
Lemma D_61168 : decode_any W_61168 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6116c : bv 32 := @BV 32 0x00058493%Z I.
Lemma F_6116c : fetch_word Plain.M.loaded_segments (@BV 64 0x611cc%Z I : word) = Some W_6116c.
Proof. vm_refl. Qed.
Lemma D_6116c : decode_any W_6116c = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61170 : bv 32 := @BV 32 0x00050913%Z I.
Lemma F_61170 : fetch_word Plain.M.loaded_segments (@BV 64 0x611d0%Z I : word) = Some W_61170.
Proof. vm_refl. Qed.
Lemma D_61170 : decode_any W_61170 = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61174 : bv 32 := @BV 32 0x00359513%Z I.
Lemma F_61174 : fetch_word Plain.M.loaded_segments (@BV 64 0x611d4%Z I : word) = Some W_61174.
Proof. vm_refl. Qed.
Lemma D_61174 : decode_any W_61174 = Some (ShiftImm ALU_SLL (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 6 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61178 : bv 32 := @BV 32 0x00a60533%Z I.
Lemma F_61178 : fetch_word Plain.M.loaded_segments (@BV 64 0x611d8%Z I : word) = Some W_61178.
Proof. vm_refl. Qed.
Lemma D_61178 : decode_any W_61178 = Some (Op ALU_ADD (@BV 5 10%Z I) (@BV 5 12%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6117c : bv 32 := @BV 32 0x00850993%Z I.
Lemma F_6117c : fetch_word Plain.M.loaded_segments (@BV 64 0x611dc%Z I : word) = Some W_6117c.
Proof. vm_refl. Qed.
Lemma D_6117c : decode_any W_6117c = Some (OpImm ALU_ADD (@BV 5 19%Z I) (@BV 5 10%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61180 : bv 32 := @BV 32 0xf25ff0ef%Z I.
Lemma F_61180 : fetch_word Plain.M.loaded_segments (@BV 64 0x611e0%Z I : word) = Some W_61180.
Proof. vm_refl. Qed.
Lemma D_61180 : decode_any W_61180 = Some (Jal (@BV 5 1%Z I) (@BV 21 2096932%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61184 : bv 32 := @BV 32 0x00048513%Z I.
Lemma F_61184 : fetch_word Plain.M.loaded_segments (@BV 64 0x611e4%Z I : word) = Some W_61184.
Proof. vm_refl. Qed.
Lemma D_61184 : decode_any W_61184 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61188 : bv 32 := @BV 32 0x00040593%Z I.
Lemma F_61188 : fetch_word Plain.M.loaded_segments (@BV 64 0x611e8%Z I : word) = Some W_61188.
Proof. vm_refl. Qed.
Lemma D_61188 : decode_any W_61188 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6118c : bv 32 := @BV 32 0x00098613%Z I.
Lemma F_6118c : fetch_word Plain.M.loaded_segments (@BV 64 0x611ec%Z I : word) = Some W_6118c.
Proof. vm_refl. Qed.
Lemma D_6118c : decode_any W_6118c = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61190 : bv 32 := @BV 32 0x000900e7%Z I.
Lemma F_61190 : fetch_word Plain.M.loaded_segments (@BV 64 0x611f0%Z I : word) = Some W_61190.
Proof. vm_refl. Qed.
Lemma D_61190 : decode_any W_61190 = Some (Jalr (@BV 5 1%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition W_61454 : bv 32 := @BV 32 0x00020513%Z I.
Lemma F_61454 : fetch_word Plain.M.loaded_segments (@BV 64 0x614a8%Z I : word) = Some W_61454.
Proof. vm_refl. Qed.
Lemma D_61454 : decode_any W_61454 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 4%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61458 : bv 32 := @BV 32 0xf5c50513%Z I.
Lemma F_61458 : fetch_word Plain.M.loaded_segments (@BV 64 0x614ac%Z I : word) = Some W_61458.
Proof. vm_refl. Qed.
Lemma D_61458 : decode_any W_61458 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 3932%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6145c : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_6145c : fetch_word Plain.M.loaded_segments (@BV 64 0x614b0%Z I : word) = Some W_6145c.
Proof. vm_refl. Qed.
Lemma D_6145c : decode_any W_6145c = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_614f4 : bv 32 := @BV 32 0x00050593%Z I.
Lemma F_614f4 : fetch_word Plain.M.loaded_segments (@BV 64 0x61548%Z I : word) = Some W_614f4.
Proof. vm_refl. Qed.
Lemma D_614f4 : decode_any W_614f4 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_614f8 : bv 32 := @BV 32 0x05e00893%Z I.
Lemma F_614f8 : fetch_word Plain.M.loaded_segments (@BV 64 0x6154c%Z I : word) = Some W_614f8.
Proof. vm_refl. Qed.
Lemma D_614f8 : decode_any W_614f8 = Some (OpImm ALU_ADD (@BV 5 17%Z I) (@BV 5 0%Z I) (@BV 12 94%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_614fc : bv 32 := @BV 32 0x00000073%Z I.
Lemma F_614fc : fetch_word Plain.M.loaded_segments (@BV 64 0x61550%Z I : word) = Some W_614fc.
Proof. vm_refl. Qed.

Lemma E_614fc : is_ecall W_614fc = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6178c : bv 32 := @BV 32 0x561020ef%Z I.
Lemma F_6178c : fetch_word Plain.M.loaded_segments (@BV 64 0x617e0%Z I : word) = Some W_6178c.
Proof. vm_refl. Qed.
Lemma D_6178c : decode_any W_6178c = Some (Jal (@BV 5 1%Z I) (@BV 21 11616%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61790 : bv 32 := @BV 32 0x00040513%Z I.
Lemma F_61790 : fetch_word Plain.M.loaded_segments (@BV 64 0x617e4%Z I : word) = Some W_61790.
Proof. vm_refl. Qed.
Lemma D_61790 : decode_any W_61790 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61794 : bv 32 := @BV 32 0xd61ff0ef%Z I.
Lemma F_61794 : fetch_word Plain.M.loaded_segments (@BV 64 0x617e8%Z I : word) = Some W_61794.
Proof. vm_refl. Qed.
Lemma D_61794 : decode_any W_61794 = Some (Jal (@BV 5 1%Z I) (@BV 21 2096480%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6187c : bv 32 := @BV 32 0xff010113%Z I.
Lemma F_6187c : fetch_word Plain.M.loaded_segments (@BV 64 0x618d0%Z I : word) = Some W_6187c.
Proof. vm_refl. Qed.
Lemma D_6187c : decode_any W_6187c = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4080%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61880 : bv 32 := @BV 32 0x00113423%Z I.
Lemma F_61880 : fetch_word Plain.M.loaded_segments (@BV 64 0x618d4%Z I : word) = Some W_61880.
Proof. vm_refl. Qed.
Lemma D_61880 : decode_any W_61880 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61884 : bv 32 := @BV 32 0x00050e63%Z I.
Lemma F_61884 : fetch_word Plain.M.loaded_segments (@BV 64 0x618d8%Z I : word) = Some W_61884.
Proof. vm_refl. Qed.
Lemma D_61884 : decode_any W_61884 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 28%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61888 : bv 32 := @BV 32 0x00050593%Z I.
Lemma F_61888 : fetch_word Plain.M.loaded_segments (@BV 64 0x618dc%Z I : word) = Some W_61888.
Proof. vm_refl. Qed.
Lemma D_61888 : decode_any W_61888 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6188c : bv 32 := @BV 32 0x00013517%Z I.
Lemma F_6188c : fetch_word Plain.M.loaded_segments (@BV 64 0x618e0%Z I : word) = Some W_6188c.
Proof. vm_refl. Qed.
Lemma D_6188c : decode_any W_6188c = Some (Auipc (@BV 5 10%Z I) (@BV 20 19%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61890 : bv 32 := @BV 32 0xe1053503%Z I.
Lemma F_61890 : fetch_word Plain.M.loaded_segments (@BV 64 0x618e4%Z I : word) = Some W_61890.
Proof. vm_refl. Qed.
Lemma D_61890 : decode_any W_61890 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 3600%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61894 : bv 32 := @BV 32 0x00800613%Z I.
Lemma F_61894 : fetch_word Plain.M.loaded_segments (@BV 64 0x618e8%Z I : word) = Some W_61894.
Proof. vm_refl. Qed.
Lemma D_61894 : decode_any W_61894 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61898 : bv 32 := @BV 32 0x3540d0ef%Z I.
Lemma F_61898 : fetch_word Plain.M.loaded_segments (@BV 64 0x618ec%Z I : word) = Some W_61898.
Proof. vm_refl. Qed.
Lemma D_61898 : decode_any W_61898 = Some (Jal (@BV 5 1%Z I) (@BV 21 54100%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6189c : bv 32 := @BV 32 0x01c0006f%Z I.
Lemma F_6189c : fetch_word Plain.M.loaded_segments (@BV 64 0x618f0%Z I : word) = Some W_6189c.
Proof. vm_refl. Qed.
Lemma D_6189c : decode_any W_6189c = Some (Jal (@BV 5 0%Z I) (@BV 21 28%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_618b8 : bv 32 := @BV 32 0x00013517%Z I.
Lemma F_618b8 : fetch_word Plain.M.loaded_segments (@BV 64 0x6190c%Z I : word) = Some W_618b8.
Proof. vm_refl. Qed.
Lemma D_618b8 : decode_any W_618b8 = Some (Auipc (@BV 5 10%Z I) (@BV 20 19%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_618bc : bv 32 := @BV 32 0xde453503%Z I.
Lemma F_618bc : fetch_word Plain.M.loaded_segments (@BV 64 0x61910%Z I : word) = Some W_618bc.
Proof. vm_refl. Qed.
Lemma D_618bc : decode_any W_618bc = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 3556%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_618c0 : bv 32 := @BV 32 0x000500a3%Z I.
Lemma F_618c0 : fetch_word Plain.M.loaded_segments (@BV 64 0x61914%Z I : word) = Some W_618c0.
Proof. vm_refl. Qed.
Lemma D_618c0 : decode_any W_618c0 = Some (Store SZ1 (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_618c4 : bv 32 := @BV 32 0x00053503%Z I.
Lemma F_618c4 : fetch_word Plain.M.loaded_segments (@BV 64 0x61918%Z I : word) = Some W_618c4.
Proof. vm_refl. Qed.
Lemma D_618c4 : decode_any W_618c4 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_618c8 : bv 32 := @BV 32 0x00020593%Z I.
Lemma F_618c8 : fetch_word Plain.M.loaded_segments (@BV 64 0x6191c%Z I : word) = Some W_618c8.
Proof. vm_refl. Qed.
Lemma D_618c8 : decode_any W_618c8 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 4%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_618cc : bv 32 := @BV 32 0xfea5b823%Z I.
Lemma F_618cc : fetch_word Plain.M.loaded_segments (@BV 64 0x61920%Z I : word) = Some W_618cc.
Proof. vm_refl. Qed.
Lemma D_618cc : decode_any W_618cc = Some (Store SZ8 (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 4080%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_618d0 : bv 32 := @BV 32 0x00813083%Z I.
Lemma F_618d0 : fetch_word Plain.M.loaded_segments (@BV 64 0x61924%Z I : word) = Some W_618d0.
Proof. vm_refl. Qed.
Lemma D_618d0 : decode_any W_618d0 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_618d4 : bv 32 := @BV 32 0x01010113%Z I.
Lemma F_618d4 : fetch_word Plain.M.loaded_segments (@BV 64 0x61928%Z I : word) = Some W_618d4.
Proof. vm_refl. Qed.
Lemma D_618d4 : decode_any W_618d4 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_618d8 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_618d8 : fetch_word Plain.M.loaded_segments (@BV 64 0x6192c%Z I : word) = Some W_618d8.
Proof. vm_refl. Qed.
Lemma D_618d8 : decode_any W_618d8 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_618e4 : bv 32 := @BV 32 0xfffff5b7%Z I.
Lemma F_618e4 : fetch_word Plain.M.loaded_segments (@BV 64 0x61938%Z I : word) = Some W_618e4.
Proof. vm_refl. Qed.
Lemma D_618e4 : decode_any W_618e4 = Some (Lui (@BV 5 11%Z I) (@BV 20 1048575%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_618e8 : bv 32 := @BV 32 0x0015859b%Z I.
Lemma F_618e8 : fetch_word Plain.M.loaded_segments (@BV 64 0x6193c%Z I : word) = Some W_618e8.
Proof. vm_refl. Qed.
Lemma D_618e8 : decode_any W_618e8 = Some (OpImm32 (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_618ec : bv 32 := @BV 32 0x02b56663%Z I.
Lemma F_618ec : fetch_word Plain.M.loaded_segments (@BV 64 0x61940%Z I : word) = Some W_618ec.
Proof. vm_refl. Qed.
Lemma D_618ec : decode_any W_618ec = Some (Branch BC_LTU (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 13 44%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_618f0 : bv 32 := @BV 32 0xff010113%Z I.
Lemma F_618f0 : fetch_word Plain.M.loaded_segments (@BV 64 0x61944%Z I : word) = Some W_618f0.
Proof. vm_refl. Qed.
Lemma D_618f0 : decode_any W_618f0 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4080%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_618f4 : bv 32 := @BV 32 0x00113423%Z I.
Lemma F_618f4 : fetch_word Plain.M.loaded_segments (@BV 64 0x61948%Z I : word) = Some W_618f4.
Proof. vm_refl. Qed.
Lemma D_618f4 : decode_any W_618f4 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_618f8 : bv 32 := @BV 32 0x00813023%Z I.
Lemma F_618f8 : fetch_word Plain.M.loaded_segments (@BV 64 0x6194c%Z I : word) = Some W_618f8.
Proof. vm_refl. Qed.
Lemma D_618f8 : decode_any W_618f8 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_618fc : bv 32 := @BV 32 0x40a0043b%Z I.
Lemma F_618fc : fetch_word Plain.M.loaded_segments (@BV 64 0x61950%Z I : word) = Some W_618fc.
Proof. vm_refl. Qed.
Lemma D_618fc : decode_any W_618fc = Some (Op32 ALU_SUB (@BV 5 8%Z I) (@BV 5 0%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61900 : bv 32 := @BV 32 0xb55ff0ef%Z I.
Lemma F_61900 : fetch_word Plain.M.loaded_segments (@BV 64 0x61954%Z I : word) = Some W_61900.
Proof. vm_refl. Qed.
Lemma D_61900 : decode_any W_61900 = Some (Jal (@BV 5 1%Z I) (@BV 21 2095956%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61904 : bv 32 := @BV 32 0x00852023%Z I.
Lemma F_61904 : fetch_word Plain.M.loaded_segments (@BV 64 0x61958%Z I : word) = Some W_61904.
Proof. vm_refl. Qed.
Lemma D_61904 : decode_any W_61904 = Some (Store SZ4 (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61908 : bv 32 := @BV 32 0xfff00513%Z I.
Lemma F_61908 : fetch_word Plain.M.loaded_segments (@BV 64 0x6195c%Z I : word) = Some W_61908.
Proof. vm_refl. Qed.
Lemma D_61908 : decode_any W_61908 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6190c : bv 32 := @BV 32 0x00813083%Z I.
Lemma F_6190c : fetch_word Plain.M.loaded_segments (@BV 64 0x61960%Z I : word) = Some W_6190c.
Proof. vm_refl. Qed.
Lemma D_6190c : decode_any W_6190c = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61910 : bv 32 := @BV 32 0x00013403%Z I.
Lemma F_61910 : fetch_word Plain.M.loaded_segments (@BV 64 0x61964%Z I : word) = Some W_61910.
Proof. vm_refl. Qed.
Lemma D_61910 : decode_any W_61910 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61914 : bv 32 := @BV 32 0x01010113%Z I.
Lemma F_61914 : fetch_word Plain.M.loaded_segments (@BV 64 0x61968%Z I : word) = Some W_61914.
Proof. vm_refl. Qed.
Lemma D_61914 : decode_any W_61914 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61918 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_61918 : fetch_word Plain.M.loaded_segments (@BV 64 0x6196c%Z I : word) = Some W_61918.
Proof. vm_refl. Qed.
Lemma D_61918 : decode_any W_61918 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61acc : bv 32 := @BV 32 0x4240006f%Z I.
Lemma F_61acc : fetch_word Plain.M.loaded_segments (@BV 64 0x61b20%Z I : word) = Some W_61acc.
Proof. vm_refl. Qed.
Lemma D_61acc : decode_any W_61acc = Some (Jal (@BV 5 0%Z I) (@BV 21 1060%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61c0c : bv 32 := @BV 32 0x4710006f%Z I.
Lemma F_61c0c : fetch_word Plain.M.loaded_segments (@BV 64 0x61c60%Z I : word) = Some W_61c0c.
Proof. vm_refl. Qed.
Lemma D_61c0c : decode_any W_61c0c = Some (Jal (@BV 5 0%Z I) (@BV 21 3184%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61ef0 : bv 32 := @BV 32 0x1c050463%Z I.
Lemma F_61ef0 : fetch_word Plain.M.loaded_segments (@BV 64 0x61f44%Z I : word) = Some W_61ef0.
Proof. vm_refl. Qed.
Lemma D_61ef0 : decode_any W_61ef0 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 456%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61ef4 : bv 32 := @BV 32 0xfd010113%Z I.
Lemma F_61ef4 : fetch_word Plain.M.loaded_segments (@BV 64 0x61f48%Z I : word) = Some W_61ef4.
Proof. vm_refl. Qed.
Lemma D_61ef4 : decode_any W_61ef4 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4048%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61ef8 : bv 32 := @BV 32 0x02113423%Z I.
Lemma F_61ef8 : fetch_word Plain.M.loaded_segments (@BV 64 0x61f4c%Z I : word) = Some W_61ef8.
Proof. vm_refl. Qed.
Lemma D_61ef8 : decode_any W_61ef8 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61efc : bv 32 := @BV 32 0x02813023%Z I.
Lemma F_61efc : fetch_word Plain.M.loaded_segments (@BV 64 0x61f50%Z I : word) = Some W_61efc.
Proof. vm_refl. Qed.
Lemma D_61efc : decode_any W_61efc = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f00 : bv 32 := @BV 32 0x00913c23%Z I.
Lemma F_61f00 : fetch_word Plain.M.loaded_segments (@BV 64 0x61f54%Z I : word) = Some W_61f00.
Proof. vm_refl. Qed.
Lemma D_61f00 : decode_any W_61f00 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f04 : bv 32 := @BV 32 0x01213823%Z I.
Lemma F_61f04 : fetch_word Plain.M.loaded_segments (@BV 64 0x61f58%Z I : word) = Some W_61f04.
Proof. vm_refl. Qed.
Lemma D_61f04 : decode_any W_61f04 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f08 : bv 32 := @BV 32 0x01313423%Z I.
Lemma F_61f08 : fetch_word Plain.M.loaded_segments (@BV 64 0x61f5c%Z I : word) = Some W_61f08.
Proof. vm_refl. Qed.
Lemma D_61f08 : decode_any W_61f08 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 19%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f0c : bv 32 := @BV 32 0x00050493%Z I.
Lemma F_61f0c : fetch_word Plain.M.loaded_segments (@BV 64 0x61f60%Z I : word) = Some W_61f0c.
Proof. vm_refl. Qed.
Lemma D_61f0c : decode_any W_61f0c = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f10 : bv 32 := @BV 32 0x1ac000ef%Z I.
Lemma F_61f10 : fetch_word Plain.M.loaded_segments (@BV 64 0x61f64%Z I : word) = Some W_61f10.
Proof. vm_refl. Qed.
Lemma D_61f10 : decode_any W_61f10 = Some (Jal (@BV 5 1%Z I) (@BV 21 428%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f14 : bv 32 := @BV 32 0x02053583%Z I.
Lemma F_61f14 : fetch_word Plain.M.loaded_segments (@BV 64 0x61f68%Z I : word) = Some W_61f14.
Proof. vm_refl. Qed.
Lemma D_61f14 : decode_any W_61f14 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f18 : bv 32 := @BV 32 0xffd4c683%Z I.
Lemma F_61f18 : fetch_word Plain.M.loaded_segments (@BV 64 0x61f6c%Z I : word) = Some W_61f18.
Proof. vm_refl. Qed.
Lemma D_61f18 : decode_any W_61f18 = Some (Load SZ1 false (@BV 5 13%Z I) (@BV 5 9%Z I) (@BV 12 4093%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f1c : bv 32 := @BV 32 0x00c5d613%Z I.
Lemma F_61f1c : fetch_word Plain.M.loaded_segments (@BV 64 0x61f70%Z I : word) = Some W_61f1c.
Proof. vm_refl. Qed.
Lemma D_61f1c : decode_any W_61f1c = Some (ShiftImm ALU_SRL (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 6 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f20 : bv 32 := @BV 32 0x01f6f413%Z I.
Lemma F_61f20 : fetch_word Plain.M.loaded_segments (@BV 64 0x61f74%Z I : word) = Some W_61f20.
Proof. vm_refl. Qed.
Lemma D_61f20 : decode_any W_61f20 = Some (OpImm ALU_AND (@BV 5 8%Z I) (@BV 5 13%Z I) (@BV 12 31%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f24 : bv 32 := @BV 32 0x00060e63%Z I.
Lemma F_61f24 : fetch_word Plain.M.loaded_segments (@BV 64 0x61f78%Z I : word) = Some W_61f24.
Proof. vm_refl. Qed.
Lemma D_61f24 : decode_any W_61f24 = Some (Branch BC_EQ (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 13 28%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f28 : bv 32 := @BV 32 0x01f5f613%Z I.
Lemma F_61f28 : fetch_word Plain.M.loaded_segments (@BV 64 0x61f7c%Z I : word) = Some W_61f28.
Proof. vm_refl. Qed.
Lemma D_61f28 : decode_any W_61f28 = Some (OpImm ALU_AND (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 12 31%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f2c : bv 32 := @BV 32 0x00061a63%Z I.
Lemma F_61f2c : fetch_word Plain.M.loaded_segments (@BV 64 0x61f80%Z I : word) = Some W_61f2c.
Proof. vm_refl. Qed.
Lemma D_61f2c : decode_any W_61f2c = Some (Branch BC_NE (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 13 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f30 : bv 32 := @BV 32 0xfffff637%Z I.
Lemma F_61f30 : fetch_word Plain.M.loaded_segments (@BV 64 0x61f84%Z I : word) = Some W_61f30.
Proof. vm_refl. Qed.
Lemma D_61f30 : decode_any W_61f30 = Some (Lui (@BV 5 12%Z I) (@BV 20 1048575%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f34 : bv 32 := @BV 32 0x00c5f633%Z I.
Lemma F_61f34 : fetch_word Plain.M.loaded_segments (@BV 64 0x61f88%Z I : word) = Some W_61f34.
Proof. vm_refl. Qed.
Lemma D_61f34 : decode_any W_61f34 = Some (Op ALU_AND (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f38 : bv 32 := @BV 32 0xff060613%Z I.
Lemma F_61f38 : fetch_word Plain.M.loaded_segments (@BV 64 0x61f8c%Z I : word) = Some W_61f38.
Proof. vm_refl. Qed.
Lemma D_61f38 : decode_any W_61f38 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 4080%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f3c : bv 32 := @BV 32 0x0200006f%Z I.
Lemma F_61f3c : fetch_word Plain.M.loaded_segments (@BV 64 0x61f90%Z I : word) = Some W_61f3c.
Proof. vm_refl. Qed.
Lemma D_61f3c : decode_any W_61f3c = Some (Jal (@BV 5 0%Z I) (@BV 21 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f40 : bv 32 := @BV 32 0x0055d613%Z I.
Lemma F_61f40 : fetch_word Plain.M.loaded_segments (@BV 64 0x61f94%Z I : word) = Some W_61f40.
Proof. vm_refl. Qed.
Lemma D_61f40 : decode_any W_61f40 = Some (ShiftImm ALU_SRL (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 6 5%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f44 : bv 32 := @BV 32 0xfffc2717%Z I.
Lemma F_61f44 : fetch_word Plain.M.loaded_segments (@BV 64 0x61f98%Z I : word) = Some W_61f44.
Proof. vm_refl. Qed.
Lemma D_61f44 : decode_any W_61f44 = Some (Auipc (@BV 5 14%Z I) (@BV 20 1048514%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f48 : bv 32 := @BV 32 0x07e67613%Z I.
Lemma F_61f48 : fetch_word Plain.M.loaded_segments (@BV 64 0x61f9c%Z I : word) = Some W_61f48.
Proof. vm_refl. Qed.
Lemma D_61f48 : decode_any W_61f48 = Some (OpImm ALU_AND (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 126%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f4c : bv 32 := @BV 32 0x9fc70713%Z I.
Lemma F_61f4c : fetch_word Plain.M.loaded_segments (@BV 64 0x61fa0%Z I : word) = Some W_61f4c.
Proof. vm_refl. Qed.
Lemma D_61f4c : decode_any W_61f4c = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 12 2556%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f50 : bv 32 := @BV 32 0x00c70633%Z I.
Lemma F_61f50 : fetch_word Plain.M.loaded_segments (@BV 64 0x61fa4%Z I : word) = Some W_61f50.
Proof. vm_refl. Qed.
Lemma D_61f50 : decode_any W_61f50 = Some (Op ALU_ADD (@BV 5 12%Z I) (@BV 5 14%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f54 : bv 32 := @BV 32 0x00065603%Z I.
Lemma F_61f54 : fetch_word Plain.M.loaded_segments (@BV 64 0x61fa8%Z I : word) = Some W_61f54.
Proof. vm_refl. Qed.
Lemma D_61f54 : decode_any W_61f54 = Some (Load SZ2 false (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f58 : bv 32 := @BV 32 0x00461613%Z I.
Lemma F_61f58 : fetch_word Plain.M.loaded_segments (@BV 64 0x61fac%Z I : word) = Some W_61f58.
Proof. vm_refl. Qed.
Lemma D_61f58 : decode_any W_61f58 = Some (ShiftImm ALU_SLL (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 6 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f5c : bv 32 := @BV 32 0x01053703%Z I.
Lemma F_61f5c : fetch_word Plain.M.loaded_segments (@BV 64 0x61fb0%Z I : word) = Some W_61f5c.
Proof. vm_refl. Qed.
Lemma D_61f5c : decode_any W_61f5c = Some (Load SZ8 true (@BV 5 14%Z I) (@BV 5 10%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f60 : bv 32 := @BV 32 0x028607b3%Z I.
Lemma F_61f60 : fetch_word Plain.M.loaded_segments (@BV 64 0x61fb4%Z I : word) = Some W_61f60.
Proof. vm_refl. Qed.
Lemma D_61f60 : decode_any W_61f60 = Some (Mul M_MUL (@BV 5 15%Z I) (@BV 5 12%Z I) (@BV 5 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f64 : bv 32 := @BV 32 0x0a000813%Z I.
Lemma F_61f64 : fetch_word Plain.M.loaded_segments (@BV 64 0x61fb8%Z I : word) = Some W_61f64.
Proof. vm_refl. Qed.
Lemma D_61f64 : decode_any W_61f64 = Some (OpImm ALU_ADD (@BV 5 16%Z I) (@BV 5 0%Z I) (@BV 12 160%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f68 : bv 32 := @BV 32 0x00c70633%Z I.
Lemma F_61f68 : fetch_word Plain.M.loaded_segments (@BV 64 0x61fbc%Z I : word) = Some W_61f68.
Proof. vm_refl. Qed.
Lemma D_61f68 : decode_any W_61f68 = Some (Op ALU_ADD (@BV 5 12%Z I) (@BV 5 14%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f6c : bv 32 := @BV 32 0x00f607b3%Z I.
Lemma F_61f6c : fetch_word Plain.M.loaded_segments (@BV 64 0x61fc0%Z I : word) = Some W_61f6c.
Proof. vm_refl. Qed.
Lemma D_61f6c : decode_any W_61f6c = Some (Op ALU_ADD (@BV 5 15%Z I) (@BV 5 12%Z I) (@BV 5 15%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f70 : bv 32 := @BV 32 0x00c78613%Z I.
Lemma F_61f70 : fetch_word Plain.M.loaded_segments (@BV 64 0x61fc4%Z I : word) = Some W_61f70.
Proof. vm_refl. Qed.
Lemma D_61f70 : decode_any W_61f70 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 15%Z I) (@BV 12 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f74 : bv 32 := @BV 32 0x0056d713%Z I.
Lemma F_61f74 : fetch_word Plain.M.loaded_segments (@BV 64 0x61fc8%Z I : word) = Some W_61f74.
Proof. vm_refl. Qed.
Lemma D_61f74 : decode_any W_61f74 = Some (ShiftImm ALU_SRL (@BV 5 14%Z I) (@BV 5 13%Z I) (@BV 6 5%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f78 : bv 32 := @BV 32 0x0306e663%Z I.
Lemma F_61f78 : fetch_word Plain.M.loaded_segments (@BV 64 0x61fcc%Z I : word) = Some W_61f78.
Proof. vm_refl. Qed.
Lemma D_61f78 : decode_any W_61f78 = Some (Branch BC_LTU (@BV 5 13%Z I) (@BV 5 16%Z I) (@BV 13 44%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f7c : bv 32 := @BV 32 0x00500693%Z I.
Lemma F_61f7c : fetch_word Plain.M.loaded_segments (@BV 64 0x61fd0%Z I : word) = Some W_61f7c.
Proof. vm_refl. Qed.
Lemma D_61f7c : decode_any W_61f7c = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 12 5%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f80 : bv 32 := @BV 32 0x00d70463%Z I.
Lemma F_61f80 : fetch_word Plain.M.loaded_segments (@BV 64 0x61fd4%Z I : word) = Some W_61f80.
Proof. vm_refl. Qed.
Lemma D_61f80 : decode_any W_61f80 = Some (Branch BC_EQ (@BV 5 14%Z I) (@BV 5 13%Z I) (@BV 13 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f88 : bv 32 := @BV 32 0x0087e703%Z I.
Lemma F_61f88 : fetch_word Plain.M.loaded_segments (@BV 64 0x61fdc%Z I : word) = Some W_61f88.
Proof. vm_refl. Qed.
Lemma D_61f88 : decode_any W_61f88 = Some (Load SZ4 false (@BV 5 14%Z I) (@BV 5 15%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f8c : bv 32 := @BV 32 0x00400693%Z I.
Lemma F_61f8c : fetch_word Plain.M.loaded_segments (@BV 64 0x61fe0%Z I : word) = Some W_61f8c.
Proof. vm_refl. Qed.
Lemma D_61f8c : decode_any W_61f8c = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 12 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f90 : bv 32 := @BV 32 0x00e6e463%Z I.
Lemma F_61f90 : fetch_word Plain.M.loaded_segments (@BV 64 0x61fe4%Z I : word) = Some W_61f90.
Proof. vm_refl. Qed.
Lemma D_61f90 : decode_any W_61f90 = Some (Branch BC_LTU (@BV 5 13%Z I) (@BV 5 14%Z I) (@BV 13 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f98 : bv 32 := @BV 32 0x0077c683%Z I.
Lemma F_61f98 : fetch_word Plain.M.loaded_segments (@BV 64 0x61fec%Z I : word) = Some W_61f98.
Proof. vm_refl. Qed.
Lemma D_61f98 : decode_any W_61f98 = Some (Load SZ1 false (@BV 5 13%Z I) (@BV 5 15%Z I) (@BV 12 7%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61f9c : bv 32 := @BV 32 0x00068463%Z I.
Lemma F_61f9c : fetch_word Plain.M.loaded_segments (@BV 64 0x61ff0%Z I : word) = Some W_61f9c.
Proof. vm_refl. Qed.
Lemma D_61f9c : decode_any W_61f9c = Some (Branch BC_EQ (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 13 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61fa4 : bv 32 := @BV 32 0x409606b3%Z I.
Lemma F_61fa4 : fetch_word Plain.M.loaded_segments (@BV 64 0x61ff8%Z I : word) = Some W_61fa4.
Proof. vm_refl. Qed.
Lemma D_61fa4 : decode_any W_61fa4 = Some (Op ALU_SUB (@BV 5 13%Z I) (@BV 5 12%Z I) (@BV 5 9%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61fa8 : bv 32 := @BV 32 0x00e6f463%Z I.
Lemma F_61fa8 : fetch_word Plain.M.loaded_segments (@BV 64 0x61ffc%Z I : word) = Some W_61fa8.
Proof. vm_refl. Qed.
Lemma D_61fa8 : decode_any W_61fa8 = Some (Branch BC_GEU (@BV 5 13%Z I) (@BV 5 14%Z I) (@BV 13 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61fb0 : bv 32 := @BV 32 0x40e606b3%Z I.
Lemma F_61fb0 : fetch_word Plain.M.loaded_segments (@BV 64 0x62004%Z I : word) = Some W_61fb0.
Proof. vm_refl. Qed.
Lemma D_61fb0 : decode_any W_61fb0 = Some (Op ALU_SUB (@BV 5 13%Z I) (@BV 5 12%Z I) (@BV 5 14%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61fb4 : bv 32 := @BV 32 0x0006c683%Z I.
Lemma F_61fb4 : fetch_word Plain.M.loaded_segments (@BV 64 0x62008%Z I : word) = Some W_61fb4.
Proof. vm_refl. Qed.
Lemma D_61fb4 : decode_any W_61fb4 = Some (Load SZ1 false (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61fb8 : bv 32 := @BV 32 0x00068463%Z I.
Lemma F_61fb8 : fetch_word Plain.M.loaded_segments (@BV 64 0x6200c%Z I : word) = Some W_61fb8.
Proof. vm_refl. Qed.
Lemma D_61fb8 : decode_any W_61fb8 = Some (Branch BC_EQ (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 13 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61fc0 : bv 32 := @BV 32 0x00064603%Z I.
Lemma F_61fc0 : fetch_word Plain.M.loaded_segments (@BV 64 0x62014%Z I : word) = Some W_61fc0.
Proof. vm_refl. Qed.
Lemma D_61fc0 : decode_any W_61fc0 = Some (Load SZ1 false (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61fc4 : bv 32 := @BV 32 0x00060463%Z I.
Lemma F_61fc4 : fetch_word Plain.M.loaded_segments (@BV 64 0x62018%Z I : word) = Some W_61fc4.
Proof. vm_refl. Qed.
Lemma D_61fc4 : decode_any W_61fc4 = Some (Branch BC_EQ (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 13 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61fcc : bv 32 := @BV 32 0x00100613%Z I.
Lemma F_61fcc : fetch_word Plain.M.loaded_segments (@BV 64 0x62020%Z I : word) = Some W_61fcc.
Proof. vm_refl. Qed.
Lemma D_61fcc : decode_any W_61fcc = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61fd0 : bv 32 := @BV 32 0x00200693%Z I.
Lemma F_61fd0 : fetch_word Plain.M.loaded_segments (@BV 64 0x62024%Z I : word) = Some W_61fd0.
Proof. vm_refl. Qed.
Lemma D_61fd0 : decode_any W_61fd0 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 12 2%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61fd4 : bv 32 := @BV 32 0xfff00713%Z I.
Lemma F_61fd4 : fetch_word Plain.M.loaded_segments (@BV 64 0x62028%Z I : word) = Some W_61fd4.
Proof. vm_refl. Qed.
Lemma D_61fd4 : decode_any W_61fd4 = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61fd8 : bv 32 := @BV 32 0x00b696bb%Z I.
Lemma F_61fd8 : fetch_word Plain.M.loaded_segments (@BV 64 0x6202c%Z I : word) = Some W_61fd8.
Proof. vm_refl. Qed.
Lemma D_61fd8 : decode_any W_61fd8 = Some (Op32 ALU_SLL (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61fdc : bv 32 := @BV 32 0x01c50593%Z I.
Lemma F_61fdc : fetch_word Plain.M.loaded_segments (@BV 64 0x62030%Z I : word) = Some W_61fdc.
Proof. vm_refl. Qed.
Lemma D_61fdc : decode_any W_61fdc = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 28%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61fe0 : bv 32 := @BV 32 0x0086163b%Z I.
Lemma F_61fe0 : fetch_word Plain.M.loaded_segments (@BV 64 0x62034%Z I : word) = Some W_61fe0.
Proof. vm_refl. Qed.
Lemma D_61fe0 : decode_any W_61fe0 = Some (Op32 ALU_SLL (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 5 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61fe4 : bv 32 := @BV 32 0xfee48ea3%Z I.
Lemma F_61fe4 : fetch_word Plain.M.loaded_segments (@BV 64 0x62038%Z I : word) = Some W_61fe4.
Proof. vm_refl. Qed.
Lemma D_61fe4 : decode_any W_61fe4 = Some (Store SZ1 (@BV 5 9%Z I) (@BV 5 14%Z I) (@BV 12 4093%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61fe8 : bv 32 := @BV 32 0xfe049f23%Z I.
Lemma F_61fe8 : fetch_word Plain.M.loaded_segments (@BV 64 0x6203c%Z I : word) = Some W_61fe8.
Proof. vm_refl. Qed.
Lemma D_61fe8 : decode_any W_61fe8 = Some (Store SZ2 (@BV 5 9%Z I) (@BV 5 0%Z I) (@BV 12 4094%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61fec : bv 32 := @BV 32 0xfff6869b%Z I.
Lemma F_61fec : fetch_word Plain.M.loaded_segments (@BV 64 0x62040%Z I : word) = Some W_61fec.
Proof. vm_refl. Qed.
Lemma D_61fec : decode_any W_61fec = Some (OpImm32 (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61ff0 : bv 32 := @BV 32 0x00044717%Z I.
Lemma F_61ff0 : fetch_word Plain.M.loaded_segments (@BV 64 0x62044%Z I : word) = Some W_61ff0.
Proof. vm_refl. Qed.
Lemma D_61ff0 : decode_any W_61ff0 = Some (Auipc (@BV 5 14%Z I) (@BV 20 68%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61ff4 : bv 32 := @BV 32 0x01c52783%Z I.
Lemma F_61ff4 : fetch_word Plain.M.loaded_segments (@BV 64 0x62048%Z I : word) = Some W_61ff4.
Proof. vm_refl. Qed.
Lemma D_61ff4 : decode_any W_61ff4 = Some (Load SZ4 true (@BV 5 15%Z I) (@BV 5 10%Z I) (@BV 12 28%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61ff8 : bv 32 := @BV 32 0x01852803%Z I.
Lemma F_61ff8 : fetch_word Plain.M.loaded_segments (@BV 64 0x6204c%Z I : word) = Some W_61ff8.
Proof. vm_refl. Qed.
Lemma D_61ff8 : decode_any W_61ff8 = Some (Load SZ4 true (@BV 5 16%Z I) (@BV 5 10%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61ffc : bv 32 := @BV 32 0x00f86833%Z I.
Lemma F_61ffc : fetch_word Plain.M.loaded_segments (@BV 64 0x62050%Z I : word) = Some W_61ffc.
Proof. vm_refl. Qed.
Lemma D_61ffc : decode_any W_61ffc = Some (Op ALU_OR (@BV 5 16%Z I) (@BV 5 16%Z I) (@BV 5 15%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62000 : bv 32 := @BV 32 0x00c878b3%Z I.
Lemma F_62000 : fetch_word Plain.M.loaded_segments (@BV 64 0x62054%Z I : word) = Some W_62000.
Proof. vm_refl. Qed.
Lemma D_62000 : decode_any W_62000 = Some (Op ALU_AND (@BV 5 17%Z I) (@BV 5 16%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62004 : bv 32 := @BV 32 0x00088463%Z I.
Lemma F_62004 : fetch_word Plain.M.loaded_segments (@BV 64 0x62058%Z I : word) = Some W_62004.
Proof. vm_refl. Qed.
Lemma D_62004 : decode_any W_62004 = Some (Branch BC_EQ (@BV 5 17%Z I) (@BV 5 0%Z I) (@BV 13 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6200c : bv 32 := @BV 32 0x76f74883%Z I.
Lemma F_6200c : fetch_word Plain.M.loaded_segments (@BV 64 0x62060%Z I : word) = Some W_6200c.
Proof. vm_refl. Qed.
Lemma D_6200c : decode_any W_6200c = Some (Load SZ1 false (@BV 5 17%Z I) (@BV 5 14%Z I) (@BV 12 1903%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62010 : bv 32 := @BV 32 0x02078863%Z I.
Lemma F_62010 : fetch_word Plain.M.loaded_segments (@BV 64 0x62064%Z I : word) = Some W_62010.
Proof. vm_refl. Qed.
Lemma D_62010 : decode_any W_62010 = Some (Branch BC_EQ (@BV 5 15%Z I) (@BV 5 0%Z I) (@BV 13 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62014 : bv 32 := @BV 32 0x00c8083b%Z I.
Lemma F_62014 : fetch_word Plain.M.loaded_segments (@BV 64 0x62068%Z I : word) = Some W_62014.
Proof. vm_refl. Qed.
Lemma D_62014 : decode_any W_62014 = Some (Op32 ALU_ADD (@BV 5 16%Z I) (@BV 5 16%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62018 : bv 32 := @BV 32 0x02d80463%Z I.
Lemma F_62018 : fetch_word Plain.M.loaded_segments (@BV 64 0x6206c%Z I : word) = Some W_62018.
Proof. vm_refl. Qed.
Lemma D_62018 : decode_any W_62018 = Some (Branch BC_EQ (@BV 5 16%Z I) (@BV 5 13%Z I) (@BV 13 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6201c : bv 32 := @BV 32 0x00c7883b%Z I.
Lemma F_6201c : fetch_word Plain.M.loaded_segments (@BV 64 0x62070%Z I : word) = Some W_6201c.
Proof. vm_refl. Qed.
Lemma D_6201c : decode_any W_6201c = Some (Op32 ALU_ADD (@BV 5 16%Z I) (@BV 5 15%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62020 : bv 32 := @BV 32 0x06088e63%Z I.
Lemma F_62020 : fetch_word Plain.M.loaded_segments (@BV 64 0x62074%Z I : word) = Some W_62020.
Proof. vm_refl. Qed.
Lemma D_62020 : decode_any W_62020 = Some (Branch BC_EQ (@BV 5 17%Z I) (@BV 5 0%Z I) (@BV 13 124%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62040 : bv 32 := @BV 32 0x00088e63%Z I.
Lemma F_62040 : fetch_word Plain.M.loaded_segments (@BV 64 0x62094%Z I : word) = Some W_62040.
Proof. vm_refl. Qed.
Lemma D_62040 : decode_any W_62040 = Some (Branch BC_EQ (@BV 5 17%Z I) (@BV 5 0%Z I) (@BV 13 28%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6205c : bv 32 := @BV 32 0x00040593%Z I.
Lemma F_6205c : fetch_word Plain.M.loaded_segments (@BV 64 0x620b0%Z I : word) = Some W_6205c.
Proof. vm_refl. Qed.
Lemma D_6205c : decode_any W_6205c = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62060 : bv 32 := @BV 32 0x16c000ef%Z I.
Lemma F_62060 : fetch_word Plain.M.loaded_segments (@BV 64 0x620b4%Z I : word) = Some W_62060.
Proof. vm_refl. Qed.
Lemma D_62060 : decode_any W_62060 = Some (Jal (@BV 5 1%Z I) (@BV 21 364%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62064 : bv 32 := @BV 32 0x00050413%Z I.
Lemma F_62064 : fetch_word Plain.M.loaded_segments (@BV 64 0x620b8%Z I : word) = Some W_62064.
Proof. vm_refl. Qed.
Lemma D_62064 : decode_any W_62064 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62068 : bv 32 := @BV 32 0x00058493%Z I.
Lemma F_62068 : fetch_word Plain.M.loaded_segments (@BV 64 0x620bc%Z I : word) = Some W_62068.
Proof. vm_refl. Qed.
Lemma D_62068 : decode_any W_62068 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6206c : bv 32 := @BV 32 0x00044517%Z I.
Lemma F_6206c : fetch_word Plain.M.loaded_segments (@BV 64 0x620c0%Z I : word) = Some W_6206c.
Proof. vm_refl. Qed.
Lemma D_6206c : decode_any W_6206c = Some (Auipc (@BV 5 10%Z I) (@BV 20 68%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62070 : bv 32 := @BV 32 0x76050513%Z I.
Lemma F_62070 : fetch_word Plain.M.loaded_segments (@BV 64 0x620c4%Z I : word) = Some W_62070.
Proof. vm_refl. Qed.
Lemma D_62070 : decode_any W_62070 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 1888%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62074 : bv 32 := @BV 32 0x66c0d0ef%Z I.
Lemma F_62074 : fetch_word Plain.M.loaded_segments (@BV 64 0x620c8%Z I : word) = Some W_62074.
Proof. vm_refl. Qed.
Lemma D_62074 : decode_any W_62074 = Some (Jal (@BV 5 1%Z I) (@BV 21 54892%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62078 : bv 32 := @BV 32 0x02048463%Z I.
Lemma F_62078 : fetch_word Plain.M.loaded_segments (@BV 64 0x620cc%Z I : word) = Some W_62078.
Proof. vm_refl. Qed.
Lemma D_62078 : decode_any W_62078 = Some (Branch BC_EQ (@BV 5 9%Z I) (@BV 5 0%Z I) (@BV 13 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6207c : bv 32 := @BV 32 0xbd8ff0ef%Z I.
Lemma F_6207c : fetch_word Plain.M.loaded_segments (@BV 64 0x620d0%Z I : word) = Some W_6207c.
Proof. vm_refl. Qed.
Lemma D_6207c : decode_any W_6207c = Some (Jal (@BV 5 1%Z I) (@BV 21 2094040%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62080 : bv 32 := @BV 32 0x00050913%Z I.
Lemma F_62080 : fetch_word Plain.M.loaded_segments (@BV 64 0x620d4%Z I : word) = Some W_62080.
Proof. vm_refl. Qed.
Lemma D_62080 : decode_any W_62080 = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62084 : bv 32 := @BV 32 0x00052983%Z I.
Lemma F_62084 : fetch_word Plain.M.loaded_segments (@BV 64 0x620d8%Z I : word) = Some W_62084.
Proof. vm_refl. Qed.
Lemma D_62084 : decode_any W_62084 = Some (Load SZ4 true (@BV 5 19%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62088 : bv 32 := @BV 32 0x00040513%Z I.
Lemma F_62088 : fetch_word Plain.M.loaded_segments (@BV 64 0x620dc%Z I : word) = Some W_62088.
Proof. vm_refl. Qed.
Lemma D_62088 : decode_any W_62088 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6208c : bv 32 := @BV 32 0x00048593%Z I.
Lemma F_6208c : fetch_word Plain.M.loaded_segments (@BV 64 0x620e0%Z I : word) = Some W_6208c.
Proof. vm_refl. Qed.
Lemma D_6208c : decode_any W_6208c = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62090 : bv 32 := @BV 32 0x59d010ef%Z I.
Lemma F_62090 : fetch_word Plain.M.loaded_segments (@BV 64 0x620e4%Z I : word) = Some W_62090.
Proof. vm_refl. Qed.
Lemma D_62090 : decode_any W_62090 = Some (Jal (@BV 5 1%Z I) (@BV 21 7580%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62094 : bv 32 := @BV 32 0x01392023%Z I.
Lemma F_62094 : fetch_word Plain.M.loaded_segments (@BV 64 0x620e8%Z I : word) = Some W_62094.
Proof. vm_refl. Qed.
Lemma D_62094 : decode_any W_62094 = Some (Store SZ4 (@BV 5 18%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62098 : bv 32 := @BV 32 0x0080006f%Z I.
Lemma F_62098 : fetch_word Plain.M.loaded_segments (@BV 64 0x620ec%Z I : word) = Some W_62098.
Proof. vm_refl. Qed.
Lemma D_62098 : decode_any W_62098 = Some (Jal (@BV 5 0%Z I) (@BV 21 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6209c : bv 32 := @BV 32 0x0105a023%Z I.
Lemma F_6209c : fetch_word Plain.M.loaded_segments (@BV 64 0x620f0%Z I : word) = Some W_6209c.
Proof. vm_refl. Qed.
Lemma D_6209c : decode_any W_6209c = Some (Store SZ4 (@BV 5 11%Z I) (@BV 5 16%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_620a0 : bv 32 := @BV 32 0x02813083%Z I.
Lemma F_620a0 : fetch_word Plain.M.loaded_segments (@BV 64 0x620f4%Z I : word) = Some W_620a0.
Proof. vm_refl. Qed.
Lemma D_620a0 : decode_any W_620a0 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_620a4 : bv 32 := @BV 32 0x02013403%Z I.
Lemma F_620a4 : fetch_word Plain.M.loaded_segments (@BV 64 0x620f8%Z I : word) = Some W_620a4.
Proof. vm_refl. Qed.
Lemma D_620a4 : decode_any W_620a4 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_620a8 : bv 32 := @BV 32 0x01813483%Z I.
Lemma F_620a8 : fetch_word Plain.M.loaded_segments (@BV 64 0x620fc%Z I : word) = Some W_620a8.
Proof. vm_refl. Qed.
Lemma D_620a8 : decode_any W_620a8 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_620ac : bv 32 := @BV 32 0x01013903%Z I.
Lemma F_620ac : fetch_word Plain.M.loaded_segments (@BV 64 0x62100%Z I : word) = Some W_620ac.
Proof. vm_refl. Qed.
Lemma D_620ac : decode_any W_620ac = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_620b0 : bv 32 := @BV 32 0x00813983%Z I.
Lemma F_620b0 : fetch_word Plain.M.loaded_segments (@BV 64 0x62104%Z I : word) = Some W_620b0.
Proof. vm_refl. Qed.
Lemma D_620b0 : decode_any W_620b0 = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_620b4 : bv 32 := @BV 32 0x03010113%Z I.
Lemma F_620b4 : fetch_word Plain.M.loaded_segments (@BV 64 0x62108%Z I : word) = Some W_620b4.
Proof. vm_refl. Qed.
Lemma D_620b4 : decode_any W_620b4 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_620b8 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_620b8 : fetch_word Plain.M.loaded_segments (@BV 64 0x6210c%Z I : word) = Some W_620b8.
Proof. vm_refl. Qed.
Lemma D_620b8 : decode_any W_620b8 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_620bc : bv 32 := @BV 32 0x00f57593%Z I.
Lemma F_620bc : fetch_word Plain.M.loaded_segments (@BV 64 0x62110%Z I : word) = Some W_620bc.
Proof. vm_refl. Qed.
Lemma D_620bc : decode_any W_620bc = Some (OpImm ALU_AND (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 15%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_620c0 : bv 32 := @BV 32 0x00058463%Z I.
Lemma F_620c0 : fetch_word Plain.M.loaded_segments (@BV 64 0x62114%Z I : word) = Some W_620c0.
Proof. vm_refl. Qed.
Lemma D_620c0 : decode_any W_620c0 = Some (Branch BC_EQ (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_620c8 : bv 32 := @BV 32 0xffc54603%Z I.
Lemma F_620c8 : fetch_word Plain.M.loaded_segments (@BV 64 0x6211c%Z I : word) = Some W_620c8.
Proof. vm_refl. Qed.
Lemma D_620c8 : decode_any W_620c8 = Some (Load SZ1 false (@BV 5 12%Z I) (@BV 5 10%Z I) (@BV 12 4092%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_620cc : bv 32 := @BV 32 0xffd54683%Z I.
Lemma F_620cc : fetch_word Plain.M.loaded_segments (@BV 64 0x62120%Z I : word) = Some W_620cc.
Proof. vm_refl. Qed.
Lemma D_620cc : decode_any W_620cc = Some (Load SZ1 false (@BV 5 13%Z I) (@BV 5 10%Z I) (@BV 12 4093%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_620d0 : bv 32 := @BV 32 0xffe55583%Z I.
Lemma F_620d0 : fetch_word Plain.M.loaded_segments (@BV 64 0x62124%Z I : word) = Some W_620d0.
Proof. vm_refl. Qed.
Lemma D_620d0 : decode_any W_620d0 = Some (Load SZ2 false (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 4094%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_620d4 : bv 32 := @BV 32 0x00060e63%Z I.
Lemma F_620d4 : fetch_word Plain.M.loaded_segments (@BV 64 0x62128%Z I : word) = Some W_620d4.
Proof. vm_refl. Qed.
Lemma D_620d4 : decode_any W_620d4 = Some (Branch BC_EQ (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 13 28%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_620f0 : bv 32 := @BV 32 0x00459613%Z I.
Lemma F_620f0 : fetch_word Plain.M.loaded_segments (@BV 64 0x62144%Z I : word) = Some W_620f0.
Proof. vm_refl. Qed.
Lemma D_620f0 : decode_any W_620f0 = Some (ShiftImm ALU_SLL (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 6 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_620f4 : bv 32 := @BV 32 0x40c50633%Z I.
Lemma F_620f4 : fetch_word Plain.M.loaded_segments (@BV 64 0x62148%Z I : word) = Some W_620f4.
Proof. vm_refl. Qed.
Lemma D_620f4 : decode_any W_620f4 = Some (Op ALU_SUB (@BV 5 12%Z I) (@BV 5 10%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_620f8 : bv 32 := @BV 32 0xff063503%Z I.
Lemma F_620f8 : fetch_word Plain.M.loaded_segments (@BV 64 0x6214c%Z I : word) = Some W_620f8.
Proof. vm_refl. Qed.
Lemma D_620f8 : decode_any W_620f8 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 12%Z I) (@BV 12 4080%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_620fc : bv 32 := @BV 32 0x01053703%Z I.
Lemma F_620fc : fetch_word Plain.M.loaded_segments (@BV 64 0x62150%Z I : word) = Some W_620fc.
Proof. vm_refl. Qed.
Lemma D_620fc : decode_any W_620fc = Some (Load SZ8 true (@BV 5 14%Z I) (@BV 5 10%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62100 : bv 32 := @BV 32 0xff060613%Z I.
Lemma F_62100 : fetch_word Plain.M.loaded_segments (@BV 64 0x62154%Z I : word) = Some W_62100.
Proof. vm_refl. Qed.
Lemma D_62100 : decode_any W_62100 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 4080%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62104 : bv 32 := @BV 32 0x01f6f693%Z I.
Lemma F_62104 : fetch_word Plain.M.loaded_segments (@BV 64 0x62158%Z I : word) = Some W_62104.
Proof. vm_refl. Qed.
Lemma D_62104 : decode_any W_62104 = Some (OpImm ALU_AND (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 31%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62108 : bv 32 := @BV 32 0x00c70463%Z I.
Lemma F_62108 : fetch_word Plain.M.loaded_segments (@BV 64 0x6215c%Z I : word) = Some W_62108.
Proof. vm_refl. Qed.
Lemma D_62108 : decode_any W_62108 = Some (Branch BC_EQ (@BV 5 14%Z I) (@BV 5 12%Z I) (@BV 13 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62110 : bv 32 := @BV 32 0x02053603%Z I.
Lemma F_62110 : fetch_word Plain.M.loaded_segments (@BV 64 0x62164%Z I : word) = Some W_62110.
Proof. vm_refl. Qed.
Lemma D_62110 : decode_any W_62110 = Some (Load SZ8 true (@BV 5 12%Z I) (@BV 5 10%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62114 : bv 32 := @BV 32 0x01f67713%Z I.
Lemma F_62114 : fetch_word Plain.M.loaded_segments (@BV 64 0x62168%Z I : word) = Some W_62114.
Proof. vm_refl. Qed.
Lemma D_62114 : decode_any W_62114 = Some (OpImm ALU_AND (@BV 5 14%Z I) (@BV 5 12%Z I) (@BV 12 31%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62118 : bv 32 := @BV 32 0x00d77463%Z I.
Lemma F_62118 : fetch_word Plain.M.loaded_segments (@BV 64 0x6216c%Z I : word) = Some W_62118.
Proof. vm_refl. Qed.
Lemma D_62118 : decode_any W_62118 = Some (Branch BC_GEU (@BV 5 14%Z I) (@BV 5 13%Z I) (@BV 13 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62120 : bv 32 := @BV 32 0x01852783%Z I.
Lemma F_62120 : fetch_word Plain.M.loaded_segments (@BV 64 0x62174%Z I : word) = Some W_62120.
Proof. vm_refl. Qed.
Lemma D_62120 : decode_any W_62120 = Some (Load SZ4 true (@BV 5 15%Z I) (@BV 5 10%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62124 : bv 32 := @BV 32 0x00100713%Z I.
Lemma F_62124 : fetch_word Plain.M.loaded_segments (@BV 64 0x62178%Z I : word) = Some W_62124.
Proof. vm_refl. Qed.
Lemma D_62124 : decode_any W_62124 = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62128 : bv 32 := @BV 32 0x00d7173b%Z I.
Lemma F_62128 : fetch_word Plain.M.loaded_segments (@BV 64 0x6217c%Z I : word) = Some W_62128.
Proof. vm_refl. Qed.
Lemma D_62128 : decode_any W_62128 = Some (Op32 ALU_SLL (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 5 13%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6212c : bv 32 := @BV 32 0x00e7f7b3%Z I.
Lemma F_6212c : fetch_word Plain.M.loaded_segments (@BV 64 0x62180%Z I : word) = Some W_6212c.
Proof. vm_refl. Qed.
Lemma D_6212c : decode_any W_6212c = Some (Op ALU_AND (@BV 5 15%Z I) (@BV 5 15%Z I) (@BV 5 14%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62130 : bv 32 := @BV 32 0x00078463%Z I.
Lemma F_62130 : fetch_word Plain.M.loaded_segments (@BV 64 0x62184%Z I : word) = Some W_62130.
Proof. vm_refl. Qed.
Lemma D_62130 : decode_any W_62130 = Some (Branch BC_EQ (@BV 5 15%Z I) (@BV 5 0%Z I) (@BV 13 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62138 : bv 32 := @BV 32 0x01c52783%Z I.
Lemma F_62138 : fetch_word Plain.M.loaded_segments (@BV 64 0x6218c%Z I : word) = Some W_62138.
Proof. vm_refl. Qed.
Lemma D_62138 : decode_any W_62138 = Some (Load SZ4 true (@BV 5 15%Z I) (@BV 5 10%Z I) (@BV 12 28%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6213c : bv 32 := @BV 32 0x00e7f733%Z I.
Lemma F_6213c : fetch_word Plain.M.loaded_segments (@BV 64 0x62190%Z I : word) = Some W_6213c.
Proof. vm_refl. Qed.
Lemma D_6213c : decode_any W_6213c = Some (Op ALU_AND (@BV 5 14%Z I) (@BV 5 15%Z I) (@BV 5 14%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62140 : bv 32 := @BV 32 0x00070463%Z I.
Lemma F_62140 : fetch_word Plain.M.loaded_segments (@BV 64 0x62194%Z I : word) = Some W_62140.
Proof. vm_refl. Qed.
Lemma D_62140 : decode_any W_62140 = Some (Branch BC_EQ (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 13 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62148 : bv 32 := @BV 32 0xfffff737%Z I.
Lemma F_62148 : fetch_word Plain.M.loaded_segments (@BV 64 0x6219c%Z I : word) = Some W_62148.
Proof. vm_refl. Qed.
Lemma D_62148 : decode_any W_62148 = Some (Lui (@BV 5 14%Z I) (@BV 20 1048575%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6214c : bv 32 := @BV 32 0x00044797%Z I.
Lemma F_6214c : fetch_word Plain.M.loaded_segments (@BV 64 0x621a0%Z I : word) = Some W_6214c.
Proof. vm_refl. Qed.
Lemma D_6214c : decode_any W_6214c = Some (Auipc (@BV 5 15%Z I) (@BV 20 68%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62150 : bv 32 := @BV 32 0x00e57733%Z I.
Lemma F_62150 : fetch_word Plain.M.loaded_segments (@BV 64 0x621a4%Z I : word) = Some W_62150.
Proof. vm_refl. Qed.
Lemma D_62150 : decode_any W_62150 = Some (Op ALU_AND (@BV 5 14%Z I) (@BV 5 10%Z I) (@BV 5 14%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62154 : bv 32 := @BV 32 0x00073703%Z I.
Lemma F_62154 : fetch_word Plain.M.loaded_segments (@BV 64 0x621a8%Z I : word) = Some W_62154.
Proof. vm_refl. Qed.
Lemma D_62154 : decode_any W_62154 = Some (Load SZ8 true (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62158 : bv 32 := @BV 32 0x6887b783%Z I.
Lemma F_62158 : fetch_word Plain.M.loaded_segments (@BV 64 0x621ac%Z I : word) = Some W_62158.
Proof. vm_refl. Qed.
Lemma D_62158 : decode_any W_62158 = Some (Load SZ8 true (@BV 5 15%Z I) (@BV 5 15%Z I) (@BV 12 1672%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6215c : bv 32 := @BV 32 0x00f70463%Z I.
Lemma F_6215c : fetch_word Plain.M.loaded_segments (@BV 64 0x621b0%Z I : word) = Some W_6215c.
Proof. vm_refl. Qed.
Lemma D_6215c : decode_any W_6215c = Some (Branch BC_EQ (@BV 5 14%Z I) (@BV 5 15%Z I) (@BV 13 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62164 : bv 32 := @BV 32 0x03461713%Z I.
Lemma F_62164 : fetch_word Plain.M.loaded_segments (@BV 64 0x621b8%Z I : word) = Some W_62164.
Proof. vm_refl. Qed.
Lemma D_62164 : decode_any W_62164 = Some (ShiftImm ALU_SLL (@BV 5 14%Z I) (@BV 5 12%Z I) (@BV 6 52%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62168 : bv 32 := @BV 32 0x03a75713%Z I.
Lemma F_62168 : fetch_word Plain.M.loaded_segments (@BV 64 0x621bc%Z I : word) = Some W_62168.
Proof. vm_refl. Qed.
Lemma D_62168 : decode_any W_62168 = Some (ShiftImm ALU_SRL (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 6 58%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6216c : bv 32 := @BV 32 0x02f00793%Z I.
Lemma F_6216c : fetch_word Plain.M.loaded_segments (@BV 64 0x621c0%Z I : word) = Some W_6216c.
Proof. vm_refl. Qed.
Lemma D_6216c : decode_any W_6216c = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 0%Z I) (@BV 12 47%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62170 : bv 32 := @BV 32 0x02e7ea63%Z I.
Lemma F_62170 : fetch_word Plain.M.loaded_segments (@BV 64 0x621c4%Z I : word) = Some W_62170.
Proof. vm_refl. Qed.
Lemma D_62170 : decode_any W_62170 = Some (Branch BC_LTU (@BV 5 15%Z I) (@BV 5 14%Z I) (@BV 13 52%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62174 : bv 32 := @BV 32 0x00171713%Z I.
Lemma F_62174 : fetch_word Plain.M.loaded_segments (@BV 64 0x621c8%Z I : word) = Some W_62174.
Proof. vm_refl. Qed.
Lemma D_62174 : decode_any W_62174 = Some (ShiftImm ALU_SLL (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 6 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62178 : bv 32 := @BV 32 0xfffc1797%Z I.
Lemma F_62178 : fetch_word Plain.M.loaded_segments (@BV 64 0x621cc%Z I : word) = Some W_62178.
Proof. vm_refl. Qed.
Lemma D_62178 : decode_any W_62178 = Some (Auipc (@BV 5 15%Z I) (@BV 20 1048513%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6217c : bv 32 := @BV 32 0x7c878793%Z I.
Lemma F_6217c : fetch_word Plain.M.loaded_segments (@BV 64 0x621d0%Z I : word) = Some W_6217c.
Proof. vm_refl. Qed.
Lemma D_6217c : decode_any W_6217c = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 15%Z I) (@BV 12 1992%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62180 : bv 32 := @BV 32 0x00e78733%Z I.
Lemma F_62180 : fetch_word Plain.M.loaded_segments (@BV 64 0x621d4%Z I : word) = Some W_62180.
Proof. vm_refl. Qed.
Lemma D_62180 : decode_any W_62180 = Some (Op ALU_ADD (@BV 5 14%Z I) (@BV 5 15%Z I) (@BV 5 14%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62184 : bv 32 := @BV 32 0x00075703%Z I.
Lemma F_62184 : fetch_word Plain.M.loaded_segments (@BV 64 0x621d8%Z I : word) = Some W_62184.
Proof. vm_refl. Qed.
Lemma D_62184 : decode_any W_62184 = Some (Load SZ2 false (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62188 : bv 32 := @BV 32 0x02d707b3%Z I.
Lemma F_62188 : fetch_word Plain.M.loaded_segments (@BV 64 0x621dc%Z I : word) = Some W_62188.
Proof. vm_refl. Qed.
Lemma D_62188 : decode_any W_62188 = Some (Mul M_MUL (@BV 5 15%Z I) (@BV 5 14%Z I) (@BV 5 13%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6218c : bv 32 := @BV 32 0x00f5f463%Z I.
Lemma F_6218c : fetch_word Plain.M.loaded_segments (@BV 64 0x621e0%Z I : word) = Some W_6218c.
Proof. vm_refl. Qed.
Lemma D_6218c : decode_any W_6218c = Some (Branch BC_GEU (@BV 5 11%Z I) (@BV 5 15%Z I) (@BV 13 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62194 : bv 32 := @BV 32 0x00168693%Z I.
Lemma F_62194 : fetch_word Plain.M.loaded_segments (@BV 64 0x621e8%Z I : word) = Some W_62194.
Proof. vm_refl. Qed.
Lemma D_62194 : decode_any W_62194 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62198 : bv 32 := @BV 32 0x02e686b3%Z I.
Lemma F_62198 : fetch_word Plain.M.loaded_segments (@BV 64 0x621ec%Z I : word) = Some W_62198.
Proof. vm_refl. Qed.
Lemma D_62198 : decode_any W_62198 = Some (Mul M_MUL (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 5 14%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6219c : bv 32 := @BV 32 0x00d5f863%Z I.
Lemma F_6219c : fetch_word Plain.M.loaded_segments (@BV 64 0x621f0%Z I : word) = Some W_6219c.
Proof. vm_refl. Qed.
Lemma D_6219c : decode_any W_6219c = Some (Branch BC_GEU (@BV 5 11%Z I) (@BV 5 13%Z I) (@BV 13 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621a0 : bv 32 := @BV 32 0x0100006f%Z I.
Lemma F_621a0 : fetch_word Plain.M.loaded_segments (@BV 64 0x621f4%Z I : word) = Some W_621a0.
Proof. vm_refl. Qed.
Lemma D_621a0 : decode_any W_621a0 = Some (Jal (@BV 5 0%Z I) (@BV 21 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621a4 : bv 32 := @BV 32 0x03f00693%Z I.
Lemma F_621a4 : fetch_word Plain.M.loaded_segments (@BV 64 0x621f8%Z I : word) = Some W_621a4.
Proof. vm_refl. Qed.
Lemma D_621a4 : decode_any W_621a4 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 12 63%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621a8 : bv 32 := @BV 32 0x00d70463%Z I.
Lemma F_621a8 : fetch_word Plain.M.loaded_segments (@BV 64 0x621fc%Z I : word) = Some W_621a8.
Proof. vm_refl. Qed.
Lemma D_621a8 : decode_any W_621a8 = Some (Branch BC_EQ (@BV 5 14%Z I) (@BV 5 13%Z I) (@BV 13 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621b0 : bv 32 := @BV 32 0x00c65613%Z I.
Lemma F_621b0 : fetch_word Plain.M.loaded_segments (@BV 64 0x62204%Z I : word) = Some W_621b0.
Proof. vm_refl. Qed.
Lemma D_621b0 : decode_any W_621b0 = Some (ShiftImm ALU_SRL (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 6 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621b4 : bv 32 := @BV 32 0x00060a63%Z I.
Lemma F_621b4 : fetch_word Plain.M.loaded_segments (@BV 64 0x62208%Z I : word) = Some W_621b4.
Proof. vm_refl. Qed.
Lemma D_621b4 : decode_any W_621b4 = Some (Branch BC_EQ (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 13 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621b8 : bv 32 := @BV 32 0x00861613%Z I.
Lemma F_621b8 : fetch_word Plain.M.loaded_segments (@BV 64 0x6220c%Z I : word) = Some W_621b8.
Proof. vm_refl. Qed.
Lemma D_621b8 : decode_any W_621b8 = Some (ShiftImm ALU_SLL (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 6 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621bc : bv 32 := @BV 32 0xfff60613%Z I.
Lemma F_621bc : fetch_word Plain.M.loaded_segments (@BV 64 0x62210%Z I : word) = Some W_621bc.
Proof. vm_refl. Qed.
Lemma D_621bc : decode_any W_621bc = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621c0 : bv 32 := @BV 32 0x00b67463%Z I.
Lemma F_621c0 : fetch_word Plain.M.loaded_segments (@BV 64 0x62214%Z I : word) = Some W_621c0.
Proof. vm_refl. Qed.
Lemma D_621c0 : decode_any W_621c0 = Some (Branch BC_GEU (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 13 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621c8 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_621c8 : fetch_word Plain.M.loaded_segments (@BV 64 0x6221c%Z I : word) = Some W_621c8.
Proof. vm_refl. Qed.
Lemma D_621c8 : decode_any W_621c8 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621cc : bv 32 := @BV 32 0xfa010113%Z I.
Lemma F_621cc : fetch_word Plain.M.loaded_segments (@BV 64 0x62220%Z I : word) = Some W_621cc.
Proof. vm_refl. Qed.
Lemma D_621cc : decode_any W_621cc = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4000%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621d0 : bv 32 := @BV 32 0x04113c23%Z I.
Lemma F_621d0 : fetch_word Plain.M.loaded_segments (@BV 64 0x62224%Z I : word) = Some W_621d0.
Proof. vm_refl. Qed.
Lemma D_621d0 : decode_any W_621d0 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 88%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621d4 : bv 32 := @BV 32 0x04813823%Z I.
Lemma F_621d4 : fetch_word Plain.M.loaded_segments (@BV 64 0x62228%Z I : word) = Some W_621d4.
Proof. vm_refl. Qed.
Lemma D_621d4 : decode_any W_621d4 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 80%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621d8 : bv 32 := @BV 32 0x04913423%Z I.
Lemma F_621d8 : fetch_word Plain.M.loaded_segments (@BV 64 0x6222c%Z I : word) = Some W_621d8.
Proof. vm_refl. Qed.
Lemma D_621d8 : decode_any W_621d8 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 72%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621dc : bv 32 := @BV 32 0x05213023%Z I.
Lemma F_621dc : fetch_word Plain.M.loaded_segments (@BV 64 0x62230%Z I : word) = Some W_621dc.
Proof. vm_refl. Qed.
Lemma D_621dc : decode_any W_621dc = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621e0 : bv 32 := @BV 32 0x03313c23%Z I.
Lemma F_621e0 : fetch_word Plain.M.loaded_segments (@BV 64 0x62234%Z I : word) = Some W_621e0.
Proof. vm_refl. Qed.
Lemma D_621e0 : decode_any W_621e0 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 19%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621e4 : bv 32 := @BV 32 0x00012617%Z I.
Lemma F_621e4 : fetch_word Plain.M.loaded_segments (@BV 64 0x62238%Z I : word) = Some W_621e4.
Proof. vm_refl. Qed.
Lemma D_621e4 : decode_any W_621e4 = Some (Auipc (@BV 5 12%Z I) (@BV 20 18%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621e8 : bv 32 := @BV 32 0x4b863483%Z I.
Lemma F_621e8 : fetch_word Plain.M.loaded_segments (@BV 64 0x6223c%Z I : word) = Some W_621e8.
Proof. vm_refl. Qed.
Lemma D_621e8 : decode_any W_621e8 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 12%Z I) (@BV 12 1208%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621ec : bv 32 := @BV 32 0x0004b603%Z I.
Lemma F_621ec : fetch_word Plain.M.loaded_segments (@BV 64 0x62240%Z I : word) = Some W_621ec.
Proof. vm_refl. Qed.
Lemma D_621ec : decode_any W_621ec = Some (Load SZ8 true (@BV 5 12%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621f0 : bv 32 := @BV 32 0x02c13823%Z I.
Lemma F_621f0 : fetch_word Plain.M.loaded_segments (@BV 64 0x62244%Z I : word) = Some W_621f0.
Proof. vm_refl. Qed.
Lemma D_621f0 : decode_any W_621f0 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 12%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621f4 : bv 32 := @BV 32 0x02053783%Z I.
Lemma F_621f4 : fetch_word Plain.M.loaded_segments (@BV 64 0x62248%Z I : word) = Some W_621f4.
Proof. vm_refl. Qed.
Lemma D_621f4 : decode_any W_621f4 = Some (Load SZ8 true (@BV 5 15%Z I) (@BV 5 10%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621f8 : bv 32 := @BV 32 0x01c52603%Z I.
Lemma F_621f8 : fetch_word Plain.M.loaded_segments (@BV 64 0x6224c%Z I : word) = Some W_621f8.
Proof. vm_refl. Qed.
Lemma D_621f8 : decode_any W_621f8 = Some (Load SZ4 true (@BV 5 12%Z I) (@BV 5 10%Z I) (@BV 12 28%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621fc : bv 32 := @BV 32 0x01852683%Z I.
Lemma F_621fc : fetch_word Plain.M.loaded_segments (@BV 64 0x62250%Z I : word) = Some W_621fc.
Proof. vm_refl. Qed.
Lemma D_621fc : decode_any W_621fc = Some (Load SZ4 true (@BV 5 13%Z I) (@BV 5 10%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62200 : bv 32 := @BV 32 0x00100713%Z I.
Lemma F_62200 : fetch_word Plain.M.loaded_segments (@BV 64 0x62254%Z I : word) = Some W_62200.
Proof. vm_refl. Qed.
Lemma D_62200 : decode_any W_62200 = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62204 : bv 32 := @BV 32 0x00b715bb%Z I.
Lemma F_62204 : fetch_word Plain.M.loaded_segments (@BV 64 0x62258%Z I : word) = Some W_62204.
Proof. vm_refl. Qed.
Lemma D_62204 : decode_any W_62204 = Some (Op32 ALU_SLL (@BV 5 11%Z I) (@BV 5 14%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62208 : bv 32 := @BV 32 0x03479713%Z I.
Lemma F_62208 : fetch_word Plain.M.loaded_segments (@BV 64 0x6225c%Z I : word) = Some W_62208.
Proof. vm_refl. Qed.
Lemma D_62208 : decode_any W_62208 = Some (ShiftImm ALU_SLL (@BV 5 14%Z I) (@BV 5 15%Z I) (@BV 6 52%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6220c : bv 32 := @BV 32 0x00c6e6b3%Z I.
Lemma F_6220c : fetch_word Plain.M.loaded_segments (@BV 64 0x62260%Z I : word) = Some W_6220c.
Proof. vm_refl. Qed.
Lemma D_6220c : decode_any W_6220c = Some (Op ALU_OR (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62210 : bv 32 := @BV 32 0x0207f813%Z I.
Lemma F_62210 : fetch_word Plain.M.loaded_segments (@BV 64 0x62264%Z I : word) = Some W_62210.
Proof. vm_refl. Qed.
Lemma D_62210 : decode_any W_62210 = Some (OpImm ALU_AND (@BV 5 16%Z I) (@BV 5 15%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62214 : bv 32 := @BV 32 0x03a75613%Z I.
Lemma F_62214 : fetch_word Plain.M.loaded_segments (@BV 64 0x62268%Z I : word) = Some W_62214.
Proof. vm_refl. Qed.
Lemma D_62214 : decode_any W_62214 = Some (ShiftImm ALU_SRL (@BV 5 12%Z I) (@BV 5 14%Z I) (@BV 6 58%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62218 : bv 32 := @BV 32 0x10080863%Z I.
Lemma F_62218 : fetch_word Plain.M.loaded_segments (@BV 64 0x6226c%Z I : word) = Some W_62218.
Proof. vm_refl. Qed.
Lemma D_62218 : decode_any W_62218 = Some (Branch BC_EQ (@BV 5 16%Z I) (@BV 5 0%Z I) (@BV 13 272%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6221c : bv 32 := @BV 32 0x00b6873b%Z I.
Lemma F_6221c : fetch_word Plain.M.loaded_segments (@BV 64 0x62270%Z I : word) = Some W_6221c.
Proof. vm_refl. Qed.
Lemma D_6221c : decode_any W_6221c = Some (Op32 ALU_ADD (@BV 5 14%Z I) (@BV 5 13%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62220 : bv 32 := @BV 32 0x00200813%Z I.
Lemma F_62220 : fetch_word Plain.M.loaded_segments (@BV 64 0x62274%Z I : word) = Some W_62220.
Proof. vm_refl. Qed.
Lemma D_62220 : decode_any W_62220 = Some (OpImm ALU_ADD (@BV 5 16%Z I) (@BV 5 0%Z I) (@BV 12 2%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62224 : bv 32 := @BV 32 0x00f8183b%Z I.
Lemma F_62224 : fetch_word Plain.M.loaded_segments (@BV 64 0x62278%Z I : word) = Some W_62224.
Proof. vm_refl. Qed.
Lemma D_62224 : decode_any W_62224 = Some (Op32 ALU_SLL (@BV 5 16%Z I) (@BV 5 16%Z I) (@BV 5 15%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62228 : bv 32 := @BV 32 0xfff8081b%Z I.
Lemma F_62228 : fetch_word Plain.M.loaded_segments (@BV 64 0x6227c%Z I : word) = Some W_62228.
Proof. vm_refl. Qed.
Lemma D_62228 : decode_any W_62228 = Some (OpImm32 (@BV 5 16%Z I) (@BV 5 16%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6222c : bv 32 := @BV 32 0x0f071e63%Z I.
Lemma F_6222c : fetch_word Plain.M.loaded_segments (@BV 64 0x62280%Z I : word) = Some W_6222c.
Proof. vm_refl. Qed.
Lemma D_6222c : decode_any W_6222c = Some (Branch BC_NE (@BV 5 14%Z I) (@BV 5 16%Z I) (@BV 13 252%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62230 : bv 32 := @BV 32 0x02f00713%Z I.
Lemma F_62230 : fetch_word Plain.M.loaded_segments (@BV 64 0x62284%Z I : word) = Some W_62230.
Proof. vm_refl. Qed.
Lemma D_62230 : decode_any W_62230 = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 12 47%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62234 : bv 32 := @BV 32 0x00044817%Z I.
Lemma F_62234 : fetch_word Plain.M.loaded_segments (@BV 64 0x62288%Z I : word) = Some W_62234.
Proof. vm_refl. Qed.
Lemma D_62234 : decode_any W_62234 = Some (Auipc (@BV 5 16%Z I) (@BV 20 68%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62238 : bv 32 := @BV 32 0x5a080913%Z I.
Lemma F_62238 : fetch_word Plain.M.loaded_segments (@BV 64 0x6228c%Z I : word) = Some W_62238.
Proof. vm_refl. Qed.
Lemma D_62238 : decode_any W_62238 = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 16%Z I) (@BV 12 1440%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6223c : bv 32 := @BV 32 0x0ac76263%Z I.
Lemma F_6223c : fetch_word Plain.M.loaded_segments (@BV 64 0x62290%Z I : word) = Some W_6223c.
Proof. vm_refl. Qed.
Lemma D_6223c : decode_any W_6223c = Some (Branch BC_LTU (@BV 5 14%Z I) (@BV 5 12%Z I) (@BV 13 164%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62240 : bv 32 := @BV 32 0x01f7f713%Z I.
Lemma F_62240 : fetch_word Plain.M.loaded_segments (@BV 64 0x62294%Z I : word) = Some W_62240.
Proof. vm_refl. Qed.
Lemma D_62240 : decode_any W_62240 = Some (OpImm ALU_AND (@BV 5 14%Z I) (@BV 5 15%Z I) (@BV 12 31%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62244 : bv 32 := @BV 32 0x00c7d893%Z I.
Lemma F_62244 : fetch_word Plain.M.loaded_segments (@BV 64 0x62298%Z I : word) = Some W_62244.
Proof. vm_refl. Qed.
Lemma D_62244 : decode_any W_62244 = Some (ShiftImm ALU_SRL (@BV 5 17%Z I) (@BV 5 15%Z I) (@BV 6 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62248 : bv 32 := @BV 32 0xfffc1817%Z I.
Lemma F_62248 : fetch_word Plain.M.loaded_segments (@BV 64 0x6229c%Z I : word) = Some W_62248.
Proof. vm_refl. Qed.
Lemma D_62248 : decode_any W_62248 = Some (Auipc (@BV 5 16%Z I) (@BV 20 1048513%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6224c : bv 32 := @BV 32 0x6f880813%Z I.
Lemma F_6224c : fetch_word Plain.M.loaded_segments (@BV 64 0x622a0%Z I : word) = Some W_6224c.
Proof. vm_refl. Qed.
Lemma D_6224c : decode_any W_6224c = Some (OpImm ALU_ADD (@BV 5 16%Z I) (@BV 5 16%Z I) (@BV 12 1784%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62250 : bv 32 := @BV 32 0x00088e63%Z I.
Lemma F_62250 : fetch_word Plain.M.loaded_segments (@BV 64 0x622a4%Z I : word) = Some W_62250.
Proof. vm_refl. Qed.
Lemma D_62250 : decode_any W_62250 = Some (Branch BC_EQ (@BV 5 17%Z I) (@BV 5 0%Z I) (@BV 13 28%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62254 : bv 32 := @BV 32 0x00071c63%Z I.
Lemma F_62254 : fetch_word Plain.M.loaded_segments (@BV 64 0x622a8%Z I : word) = Some W_62254.
Proof. vm_refl. Qed.
Lemma D_62254 : decode_any W_62254 = Some (Branch BC_NE (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 13 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62258 : bv 32 := @BV 32 0xfffff2b7%Z I.
Lemma F_62258 : fetch_word Plain.M.loaded_segments (@BV 64 0x622ac%Z I : word) = Some W_62258.
Proof. vm_refl. Qed.
Lemma D_62258 : decode_any W_62258 = Some (Lui (@BV 5 5%Z I) (@BV 20 1048575%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6225c : bv 32 := @BV 32 0x0057f7b3%Z I.
Lemma F_6225c : fetch_word Plain.M.loaded_segments (@BV 64 0x622b0%Z I : word) = Some W_6225c.
Proof. vm_refl. Qed.
Lemma D_6225c : decode_any W_6225c = Some (Op ALU_AND (@BV 5 15%Z I) (@BV 5 15%Z I) (@BV 5 5%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62260 : bv 32 := @BV 32 0xff078793%Z I.
Lemma F_62260 : fetch_word Plain.M.loaded_segments (@BV 64 0x622b4%Z I : word) = Some W_62260.
Proof. vm_refl. Qed.
Lemma D_62260 : decode_any W_62260 = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 15%Z I) (@BV 12 4080%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62264 : bv 32 := @BV 32 0x02089063%Z I.
Lemma F_62264 : fetch_word Plain.M.loaded_segments (@BV 64 0x622b8%Z I : word) = Some W_62264.
Proof. vm_refl. Qed.
Lemma D_62264 : decode_any W_62264 = Some (Branch BC_NE (@BV 5 17%Z I) (@BV 5 0%Z I) (@BV 13 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6226c : bv 32 := @BV 32 0x0057d793%Z I.
Lemma F_6226c : fetch_word Plain.M.loaded_segments (@BV 64 0x622c0%Z I : word) = Some W_6226c.
Proof. vm_refl. Qed.
Lemma D_6226c : decode_any W_6226c = Some (ShiftImm ALU_SRL (@BV 5 15%Z I) (@BV 5 15%Z I) (@BV 6 5%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62270 : bv 32 := @BV 32 0x07e7f793%Z I.
Lemma F_62270 : fetch_word Plain.M.loaded_segments (@BV 64 0x622c4%Z I : word) = Some W_62270.
Proof. vm_refl. Qed.
Lemma D_62270 : decode_any W_62270 = Some (OpImm ALU_AND (@BV 5 15%Z I) (@BV 5 15%Z I) (@BV 12 126%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62274 : bv 32 := @BV 32 0x00f807b3%Z I.
Lemma F_62274 : fetch_word Plain.M.loaded_segments (@BV 64 0x622c8%Z I : word) = Some W_62274.
Proof. vm_refl. Qed.
Lemma D_62274 : decode_any W_62274 = Some (Op ALU_ADD (@BV 5 15%Z I) (@BV 5 16%Z I) (@BV 5 15%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62278 : bv 32 := @BV 32 0x0007d783%Z I.
Lemma F_62278 : fetch_word Plain.M.loaded_segments (@BV 64 0x622cc%Z I : word) = Some W_62278.
Proof. vm_refl. Qed.
Lemma D_62278 : decode_any W_62278 = Some (Load SZ2 false (@BV 5 15%Z I) (@BV 5 15%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6227c : bv 32 := @BV 32 0x00479793%Z I.
Lemma F_6227c : fetch_word Plain.M.loaded_segments (@BV 64 0x622d0%Z I : word) = Some W_6227c.
Proof. vm_refl. Qed.
Lemma D_6227c : decode_any W_6227c = Some (ShiftImm ALU_SLL (@BV 5 15%Z I) (@BV 5 15%Z I) (@BV 6 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62280 : bv 32 := @BV 32 0x06088063%Z I.
Lemma F_62280 : fetch_word Plain.M.loaded_segments (@BV 64 0x622d4%Z I : word) = Some W_62280.
Proof. vm_refl. Qed.
Lemma D_62280 : decode_any W_62280 = Some (Branch BC_EQ (@BV 5 17%Z I) (@BV 5 0%Z I) (@BV 13 96%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62284 : bv 32 := @BV 32 0x00161893%Z I.
Lemma F_62284 : fetch_word Plain.M.loaded_segments (@BV 64 0x622d8%Z I : word) = Some W_62284.
Proof. vm_refl. Qed.
Lemma D_62284 : decode_any W_62284 = Some (ShiftImm ALU_SLL (@BV 5 17%Z I) (@BV 5 12%Z I) (@BV 6 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62288 : bv 32 := @BV 32 0x01180833%Z I.
Lemma F_62288 : fetch_word Plain.M.loaded_segments (@BV 64 0x622dc%Z I : word) = Some W_62288.
Proof. vm_refl. Qed.
Lemma D_62288 : decode_any W_62288 = Some (Op ALU_ADD (@BV 5 16%Z I) (@BV 5 16%Z I) (@BV 5 17%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6228c : bv 32 := @BV 32 0x00085803%Z I.
Lemma F_6228c : fetch_word Plain.M.loaded_segments (@BV 64 0x622e0%Z I : word) = Some W_6228c.
Proof. vm_refl. Qed.
Lemma D_6228c : decode_any W_6228c = Some (Load SZ2 false (@BV 5 16%Z I) (@BV 5 16%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62290 : bv 32 := @BV 32 0x00481813%Z I.
Lemma F_62290 : fetch_word Plain.M.loaded_segments (@BV 64 0x622e4%Z I : word) = Some W_62290.
Proof. vm_refl. Qed.
Lemma D_62290 : decode_any W_62290 = Some (ShiftImm ALU_SLL (@BV 5 16%Z I) (@BV 5 16%Z I) (@BV 6 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62294 : bv 32 := @BV 32 0x0507e663%Z I.
Lemma F_62294 : fetch_word Plain.M.loaded_segments (@BV 64 0x622e8%Z I : word) = Some W_62294.
Proof. vm_refl. Qed.
Lemma D_62294 : decode_any W_62294 = Some (Branch BC_LTU (@BV 5 15%Z I) (@BV 5 16%Z I) (@BV 13 76%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62298 : bv 32 := @BV 32 0x00853783%Z I.
Lemma F_62298 : fetch_word Plain.M.loaded_segments (@BV 64 0x622ec%Z I : word) = Some W_62298.
Proof. vm_refl. Qed.
Lemma D_62298 : decode_any W_62298 = Some (Load SZ8 true (@BV 5 15%Z I) (@BV 5 10%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6229c : bv 32 := @BV 32 0x04a79263%Z I.
Lemma F_6229c : fetch_word Plain.M.loaded_segments (@BV 64 0x622f0%Z I : word) = Some W_6229c.
Proof. vm_refl. Qed.
Lemma D_6229c : decode_any W_6229c = Some (Branch BC_NE (@BV 5 15%Z I) (@BV 5 10%Z I) (@BV 13 68%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_622a0 : bv 32 := @BV 32 0xff960793%Z I.
Lemma F_622a0 : fetch_word Plain.M.loaded_segments (@BV 64 0x622f4%Z I : word) = Some W_622a0.
Proof. vm_refl. Qed.
Lemma D_622a0 : decode_any W_622a0 = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 12%Z I) (@BV 12 4089%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_622a4 : bv 32 := @BV 32 0x01f00813%Z I.
Lemma F_622a4 : fetch_word Plain.M.loaded_segments (@BV 64 0x622f8%Z I : word) = Some W_622a4.
Proof. vm_refl. Qed.
Lemma D_622a4 : decode_any W_622a4 = Some (OpImm ALU_ADD (@BV 5 16%Z I) (@BV 5 0%Z I) (@BV 12 31%Z I), 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
