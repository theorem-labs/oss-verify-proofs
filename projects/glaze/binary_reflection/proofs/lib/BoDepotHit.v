(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.InstrEnc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Bo_code_8f208_8f794.
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
Definition W_8f208 : bv 32 := @BV 32 0xfe010113%Z I.
Lemma F_8f208 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f208%Z I : word) = Some W_8f208.
Proof. vm_refl. Qed.
Lemma D_8f208 : decode_any W_8f208 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4064%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f20c : bv 32 := @BV 32 0x00113c23%Z I.
Lemma F_8f20c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f20c%Z I : word) = Some W_8f20c.
Proof. vm_refl. Qed.
Lemma D_8f20c : decode_any W_8f20c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f210 : bv 32 := @BV 32 0x00813823%Z I.
Lemma F_8f210 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f210%Z I : word) = Some W_8f210.
Proof. vm_refl. Qed.
Lemma D_8f210 : decode_any W_8f210 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f214 : bv 32 := @BV 32 0x00060593%Z I.
Lemma F_8f214 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f214%Z I : word) = Some W_8f214.
Proof. vm_refl. Qed.
Lemma D_8f214 : decode_any W_8f214 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f218 : bv 32 := @BV 32 0x00050413%Z I.
Lemma F_8f218 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f218%Z I : word) = Some W_8f218.
Proof. vm_refl. Qed.
Lemma D_8f218 : decode_any W_8f218 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f21c : bv 32 := @BV 32 0x00d53023%Z I.
Lemma F_8f21c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f21c%Z I : word) = Some W_8f21c.
Proof. vm_refl. Qed.
Lemma D_8f21c : decode_any W_8f21c = Some (Store SZ8 (@BV 5 10%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f220 : bv 32 := @BV 32 0x00013423%Z I.
Lemma F_8f220 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f220%Z I : word) = Some W_8f220.
Proof. vm_refl. Qed.
Lemma D_8f220 : decode_any W_8f220 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 0%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f224 : bv 32 := @BV 32 0x00151517%Z I.
Lemma F_8f224 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f224%Z I : word) = Some W_8f224.
Proof. vm_refl. Qed.
Lemma D_8f224 : decode_any W_8f224 = Some (Auipc (@BV 5 10%Z I) (@BV 20 337%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f228 : bv 32 := @BV 32 0xe6450513%Z I.
Lemma F_8f228 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f228%Z I : word) = Some W_8f228.
Proof. vm_refl. Qed.
Lemma D_8f228 : decode_any W_8f228 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 3684%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f22c : bv 32 := @BV 32 0x00810613%Z I.
Lemma F_8f22c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f22c%Z I : word) = Some W_8f22c.
Proof. vm_refl. Qed.
Lemma D_8f22c : decode_any W_8f22c = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f230 : bv 32 := @BV 32 0xcc5fd0ef%Z I.
Lemma F_8f230 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f230%Z I : word) = Some W_8f230.
Proof. vm_refl. Qed.
Lemma D_8f230 : decode_any W_8f230 = Some (Jal (@BV 5 1%Z I) (@BV 21 2088132%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f234 : bv 32 := @BV 32 0x00813583%Z I.
Lemma F_8f234 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f234%Z I : word) = Some W_8f234.
Proof. vm_refl. Qed.
Lemma D_8f234 : decode_any W_8f234 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f238 : bv 32 := @BV 32 0x00a42623%Z I.
Lemma F_8f238 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f238%Z I : word) = Some W_8f238.
Proof. vm_refl. Qed.
Lemma D_8f238 : decode_any W_8f238 = Some (Store SZ4 (@BV 5 8%Z I) (@BV 5 10%Z I) (@BV 12 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f23c : bv 32 := @BV 32 0x00059a63%Z I.
Lemma F_8f23c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f23c%Z I : word) = Some W_8f23c.
Proof. vm_refl. Qed.
Lemma D_8f23c : decode_any W_8f23c = Some (Branch BC_NE (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f240 : bv 32 := @BV 32 0x01813083%Z I.
Lemma F_8f240 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f240%Z I : word) = Some W_8f240.
Proof. vm_refl. Qed.
Lemma D_8f240 : decode_any W_8f240 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f244 : bv 32 := @BV 32 0x01013403%Z I.
Lemma F_8f244 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f244%Z I : word) = Some W_8f244.
Proof. vm_refl. Qed.
Lemma D_8f244 : decode_any W_8f244 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f248 : bv 32 := @BV 32 0x02010113%Z I.
Lemma F_8f248 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f248%Z I : word) = Some W_8f248.
Proof. vm_refl. Qed.
Lemma D_8f248 : decode_any W_8f248 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f24c : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_8f24c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f24c%Z I : word) = Some W_8f24c.
Proof. vm_refl. Qed.
Lemma D_8f24c : decode_any W_8f24c = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f250 : bv 32 := @BV 32 0x014000ef%Z I.
Lemma F_8f250 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f250%Z I : word) = Some W_8f250.
Proof. vm_refl. Qed.
Lemma D_8f250 : decode_any W_8f250 = Some (Jal (@BV 5 1%Z I) (@BV 21 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f254 : bv 32 := @BV 32 0x01813083%Z I.
Lemma F_8f254 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f254%Z I : word) = Some W_8f254.
Proof. vm_refl. Qed.
Lemma D_8f254 : decode_any W_8f254 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f258 : bv 32 := @BV 32 0x01013403%Z I.
Lemma F_8f258 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f258%Z I : word) = Some W_8f258.
Proof. vm_refl. Qed.
Lemma D_8f258 : decode_any W_8f258 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f25c : bv 32 := @BV 32 0x02010113%Z I.
Lemma F_8f25c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f25c%Z I : word) = Some W_8f25c.
Proof. vm_refl. Qed.
Lemma D_8f25c : decode_any W_8f25c = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f260 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_8f260 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f260%Z I : word) = Some W_8f260.
Proof. vm_refl. Qed.
Lemma D_8f260 : decode_any W_8f260 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f264 : bv 32 := @BV 32 0xff010113%Z I.
Lemma F_8f264 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f264%Z I : word) = Some W_8f264.
Proof. vm_refl. Qed.
Lemma D_8f264 : decode_any W_8f264 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4080%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f268 : bv 32 := @BV 32 0x00113423%Z I.
Lemma F_8f268 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f268%Z I : word) = Some W_8f268.
Proof. vm_refl. Qed.
Lemma D_8f268 : decode_any W_8f268 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f26c : bv 32 := @BV 32 0x00813023%Z I.
Lemma F_8f26c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f26c%Z I : word) = Some W_8f26c.
Proof. vm_refl. Qed.
Lemma D_8f26c : decode_any W_8f26c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f270 : bv 32 := @BV 32 0x00077517%Z I.
Lemma F_8f270 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f270%Z I : word) = Some W_8f270.
Proof. vm_refl. Qed.
Lemma D_8f270 : decode_any W_8f270 = Some (Auipc (@BV 5 10%Z I) (@BV 20 119%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f274 : bv 32 := @BV 32 0xc9853503%Z I.
Lemma F_8f274 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f274%Z I : word) = Some W_8f274.
Proof. vm_refl. Qed.
Lemma D_8f274 : decode_any W_8f274 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 3224%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f278 : bv 32 := @BV 32 0x0f052503%Z I.
Lemma F_8f278 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f278%Z I : word) = Some W_8f278.
Proof. vm_refl. Qed.
Lemma D_8f278 : decode_any W_8f278 = Some (Load SZ4 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 240%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f27c : bv 32 := @BV 32 0x06050463%Z I.
Lemma F_8f27c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f27c%Z I : word) = Some W_8f27c.
Proof. vm_refl. Qed.
Lemma D_8f27c : decode_any W_8f27c = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 104%Z I), 4%Z).
Proof. vm_refl. Qed.












































































(* [comment removed for export] *)
Definition W_8f2e4 : bv 32 := @BV 32 0x00813083%Z I.
Lemma F_8f2e4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f2e4%Z I : word) = Some W_8f2e4.
Proof. vm_refl. Qed.
Lemma D_8f2e4 : decode_any W_8f2e4 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f2e8 : bv 32 := @BV 32 0x00013403%Z I.
Lemma F_8f2e8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f2e8%Z I : word) = Some W_8f2e8.
Proof. vm_refl. Qed.
Lemma D_8f2e8 : decode_any W_8f2e8 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f2ec : bv 32 := @BV 32 0x01010113%Z I.
Lemma F_8f2ec : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f2ec%Z I : word) = Some W_8f2ec.
Proof. vm_refl. Qed.
Lemma D_8f2ec : decode_any W_8f2ec = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f2f0 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_8f2f0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f2f0%Z I : word) = Some W_8f2f0.
Proof. vm_refl. Qed.
Lemma D_8f2f0 : decode_any W_8f2f0 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.









































































































































































































































































(* [comment removed for export] *)
Definition W_8f4f0 : bv 32 := @BV 32 0x00058613%Z I.

Lemma D_8f4f0 : decode_any W_8f4f0 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f4f4 : bv 32 := @BV 32 0x00161597%Z I.
Lemma F_8f4f4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f4f4%Z I : word) = Some W_8f4f4.
Proof. vm_refl. Qed.
Lemma D_8f4f4 : decode_any W_8f4f4 = Some (Auipc (@BV 5 11%Z I) (@BV 20 353%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f4f8 : bv 32 := @BV 32 0xba458593%Z I.
Lemma F_8f4f8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f4f8%Z I : word) = Some W_8f4f8.
Proof. vm_refl. Qed.
Lemma D_8f4f8 : decode_any W_8f4f8 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 2980%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f4fc : bv 32 := @BV 32 0x00050693%Z I.

Lemma D_8f4fc : decode_any W_8f4fc = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f500 : bv 32 := @BV 32 0x00058513%Z I.

Lemma D_8f500 : decode_any W_8f500 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f504 : bv 32 := @BV 32 0x00068593%Z I.

Lemma D_8f504 : decode_any W_8f504 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f508 : bv 32 := @BV 32 0x00000693%Z I.

Lemma D_8f508 : decode_any W_8f508 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f50c : bv 32 := @BV 32 0x0040006f%Z I.

Lemma D_8f50c : decode_any W_8f50c = Some (Jal (@BV 5 0%Z I) (@BV 21 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f510 : bv 32 := @BV 32 0xf9010113%Z I.

Lemma D_8f510 : decode_any W_8f510 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 3984%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f514 : bv 32 := @BV 32 0x06113423%Z I.

Lemma D_8f514 : decode_any W_8f514 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 104%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f518 : bv 32 := @BV 32 0x06813023%Z I.

Lemma D_8f518 : decode_any W_8f518 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 96%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f51c : bv 32 := @BV 32 0x04913c23%Z I.

Lemma D_8f51c : decode_any W_8f51c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 88%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f520 : bv 32 := @BV 32 0x05213823%Z I.

Lemma D_8f520 : decode_any W_8f520 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 80%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f524 : bv 32 := @BV 32 0x05313423%Z I.

Lemma D_8f524 : decode_any W_8f524 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 19%Z I) (@BV 12 72%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f528 : bv 32 := @BV 32 0x05413023%Z I.

Lemma D_8f528 : decode_any W_8f528 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 20%Z I) (@BV 12 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f52c : bv 32 := @BV 32 0x03513c23%Z I.

Lemma D_8f52c : decode_any W_8f52c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 21%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f530 : bv 32 := @BV 32 0x03613823%Z I.

Lemma D_8f530 : decode_any W_8f530 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 22%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f534 : bv 32 := @BV 32 0x03713423%Z I.

Lemma D_8f534 : decode_any W_8f534 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 23%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f538 : bv 32 := @BV 32 0x03813023%Z I.

Lemma D_8f538 : decode_any W_8f538 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 24%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f53c : bv 32 := @BV 32 0x01913c23%Z I.

Lemma D_8f53c : decode_any W_8f53c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 25%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f540 : bv 32 := @BV 32 0x00068413%Z I.

Lemma D_8f540 : decode_any W_8f540 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f544 : bv 32 := @BV 32 0x00050493%Z I.

Lemma D_8f544 : decode_any W_8f544 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f548 : bv 32 := @BV 32 0x00b13423%Z I.

Lemma D_8f548 : decode_any W_8f548 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 11%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f54c : bv 32 := @BV 32 0x00c13823%Z I.

Lemma D_8f54c : decode_any W_8f54c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 12%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f550 : bv 32 := @BV 32 0x00068463%Z I.

Lemma D_8f550 : decode_any W_8f550 = Some (Branch BC_EQ (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 13 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f554 : bv 32 := @BV 32 0x00040023%Z I.



(* [comment removed for export] *)
Definition W_8f558 : bv 32 := @BV 32 0x0006069b%Z I.

Lemma D_8f558 : decode_any W_8f558 = Some (OpImm32 (@BV 5 13%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f55c : bv 32 := @BV 32 0x00000513%Z I.

Lemma D_8f55c : decode_any W_8f55c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f560 : bv 32 := @BV 32 0x1c068a63%Z I.

Lemma D_8f560 : decode_any W_8f560 = Some (Branch BC_EQ (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 13 468%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f564 : bv 32 := @BV 32 0x1c058863%Z I.

Lemma D_8f564 : decode_any W_8f564 = Some (Branch BC_EQ (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 464%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f568 : bv 32 := @BV 32 0x02065693%Z I.

Lemma D_8f568 : decode_any W_8f568 = Some (ShiftImm ALU_SRL (@BV 5 13%Z I) (@BV 5 12%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f56c : bv 32 := @BV 32 0xfff00513%Z I.

Lemma D_8f56c : decode_any W_8f56c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f570 : bv 32 := @BV 32 0xfff81717%Z I.
Lemma F_8f570 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f570%Z I : word) = Some W_8f570.
Proof. vm_refl. Qed.
Lemma D_8f570 : decode_any W_8f570 = Some (Auipc (@BV 5 14%Z I) (@BV 20 1048449%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f574 : bv 32 := @BV 32 0xfff81797%Z I.
Lemma F_8f574 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f574%Z I : word) = Some W_8f574.
Proof. vm_refl. Qed.
Lemma D_8f574 : decode_any W_8f574 = Some (Auipc (@BV 5 15%Z I) (@BV 20 1048449%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f578 : bv 32 := @BV 32 0x02055513%Z I.

Lemma D_8f578 : decode_any W_8f578 = Some (ShiftImm ALU_SRL (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f57c : bv 32 := @BV 32 0xdd47b783%Z I.
Lemma F_8f57c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f57c%Z I : word) = Some W_8f57c.
Proof. vm_refl. Qed.
Lemma D_8f57c : decode_any W_8f57c = Some (Load SZ8 true (@BV 5 15%Z I) (@BV 5 15%Z I) (@BV 12 3540%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f580 : bv 32 := @BV 32 0x00a67633%Z I.

Lemma D_8f580 : decode_any W_8f580 = Some (Op ALU_AND (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f584 : bv 32 := @BV 32 0xfff81517%Z I.
Lemma F_8f584 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f584%Z I : word) = Some W_8f584.
Proof. vm_refl. Qed.
Lemma D_8f584 : decode_any W_8f584 = Some (Auipc (@BV 5 10%Z I) (@BV 20 1048449%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f588 : bv 32 := @BV 32 0xec453803%Z I.
Lemma F_8f588 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f588%Z I : word) = Some W_8f588.
Proof. vm_refl. Qed.
Lemma D_8f588 : decode_any W_8f588 = Some (Load SZ8 true (@BV 5 16%Z I) (@BV 5 10%Z I) (@BV 12 3780%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f58c : bv 32 := @BV 32 0xda073503%Z I.
Lemma F_8f58c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f58c%Z I : word) = Some W_8f58c.
Proof. vm_refl. Qed.
Lemma D_8f58c : decode_any W_8f58c = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 14%Z I) (@BV 12 3488%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f590 : bv 32 := @BV 32 0x02f60733%Z I.

Lemma D_8f590 : decode_any W_8f590 = Some (Mul M_MUL (@BV 5 14%Z I) (@BV 5 12%Z I) (@BV 5 15%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f594 : bv 32 := @BV 32 0x00361793%Z I.

Lemma D_8f594 : decode_any W_8f594 = Some (ShiftImm ALU_SLL (@BV 5 15%Z I) (@BV 5 12%Z I) (@BV 6 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f598 : bv 32 := @BV 32 0x01074633%Z I.

Lemma D_8f598 : decode_any W_8f598 = Some (Op ALU_XOR (@BV 5 12%Z I) (@BV 5 14%Z I) (@BV 5 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f59c : bv 32 := @BV 32 0x00f58733%Z I.

Lemma D_8f59c : decode_any W_8f59c = Some (Op ALU_ADD (@BV 5 14%Z I) (@BV 5 11%Z I) (@BV 5 15%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5a0 : bv 32 := @BV 32 0x0005b783%Z I.

Lemma D_8f5a0 : decode_any W_8f5a0 = Some (Load SZ8 true (@BV 5 15%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5a4 : bv 32 := @BV 32 0x00858593%Z I.

Lemma D_8f5a4 : decode_any W_8f5a4 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5a8 : bv 32 := @BV 32 0x02a787b3%Z I.

Lemma D_8f5a8 : decode_any W_8f5a8 = Some (Mul M_MUL (@BV 5 15%Z I) (@BV 5 15%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5ac : bv 32 := @BV 32 0x02f7d813%Z I.

Lemma D_8f5ac : decode_any W_8f5ac = Some (ShiftImm ALU_SRL (@BV 5 16%Z I) (@BV 5 15%Z I) (@BV 6 47%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5b0 : bv 32 := @BV 32 0x00f847b3%Z I.

Lemma D_8f5b0 : decode_any W_8f5b0 = Some (Op ALU_XOR (@BV 5 15%Z I) (@BV 5 16%Z I) (@BV 5 15%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5b4 : bv 32 := @BV 32 0x02a787b3%Z I.

Lemma D_8f5b4 : decode_any W_8f5b4 = Some (Mul M_MUL (@BV 5 15%Z I) (@BV 5 15%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5b8 : bv 32 := @BV 32 0x00c7c633%Z I.

Lemma D_8f5b8 : decode_any W_8f5b8 = Some (Op ALU_XOR (@BV 5 12%Z I) (@BV 5 15%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5bc : bv 32 := @BV 32 0x02a60633%Z I.

Lemma D_8f5bc : decode_any W_8f5bc = Some (Mul M_MUL (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5c0 : bv 32 := @BV 32 0xfee590e3%Z I.

Lemma D_8f5c0 : decode_any W_8f5c0 = Some (Branch BC_NE (@BV 5 11%Z I) (@BV 5 14%Z I) (@BV 13 8160%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5c4 : bv 32 := @BV 32 0x00010b37%Z I.

Lemma D_8f5c4 : decode_any W_8f5c4 = Some (Lui (@BV 5 22%Z I) (@BV 20 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5c8 : bv 32 := @BV 32 0x80000bb7%Z I.

Lemma D_8f5c8 : decode_any W_8f5c8 = Some (Lui (@BV 5 23%Z I) (@BV 20 524288%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5cc : bv 32 := @BV 32 0x02a685b3%Z I.

Lemma D_8f5cc : decode_any W_8f5cc = Some (Mul M_MUL (@BV 5 11%Z I) (@BV 5 13%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5d0 : bv 32 := @BV 32 0x004006b7%Z I.

Lemma D_8f5d0 : decode_any W_8f5d0 = Some (Lui (@BV 5 13%Z I) (@BV 20 1024%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5d4 : bv 32 := @BV 32 0xfffb0b1b%Z I.

Lemma D_8f5d4 : decode_any W_8f5d4 = Some (OpImm32 (@BV 5 22%Z I) (@BV 5 22%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5d8 : bv 32 := @BV 32 0xfffb8b9b%Z I.

Lemma D_8f5d8 : decode_any W_8f5d8 = Some (OpImm32 (@BV 5 23%Z I) (@BV 5 23%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5dc : bv 32 := @BV 32 0x02f5d713%Z I.

Lemma D_8f5dc : decode_any W_8f5dc = Some (ShiftImm ALU_SRL (@BV 5 14%Z I) (@BV 5 11%Z I) (@BV 6 47%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5e0 : bv 32 := @BV 32 0x00b745b3%Z I.

Lemma D_8f5e0 : decode_any W_8f5e0 = Some (Op ALU_XOR (@BV 5 11%Z I) (@BV 5 14%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5e4 : bv 32 := @BV 32 0x02a585b3%Z I.

Lemma D_8f5e4 : decode_any W_8f5e4 = Some (Mul M_MUL (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5e8 : bv 32 := @BV 32 0x00c5c5b3%Z I.

Lemma D_8f5e8 : decode_any W_8f5e8 = Some (Op ALU_XOR (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5ec : bv 32 := @BV 32 0x02a585b3%Z I.

Lemma D_8f5ec : decode_any W_8f5ec = Some (Mul M_MUL (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5f0 : bv 32 := @BV 32 0x02f5d613%Z I.

Lemma D_8f5f0 : decode_any W_8f5f0 = Some (ShiftImm ALU_SRL (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 6 47%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5f4 : bv 32 := @BV 32 0x00b645b3%Z I.

Lemma D_8f5f4 : decode_any W_8f5f4 = Some (Op ALU_XOR (@BV 5 11%Z I) (@BV 5 12%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5f8 : bv 32 := @BV 32 0x02a58533%Z I.

Lemma D_8f5f8 : decode_any W_8f5f8 = Some (Mul M_MUL (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5fc : bv 32 := @BV 32 0x02f55593%Z I.

Lemma D_8f5fc : decode_any W_8f5fc = Some (ShiftImm ALU_SRL (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 6 47%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f600 : bv 32 := @BV 32 0x00a5c9b3%Z I.

Lemma D_8f600 : decode_any W_8f600 = Some (Op ALU_XOR (@BV 5 19%Z I) (@BV 5 11%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f604 : bv 32 := @BV 32 0x02c99513%Z I.

Lemma D_8f604 : decode_any W_8f604 = Some (ShiftImm ALU_SLL (@BV 5 10%Z I) (@BV 5 19%Z I) (@BV 6 44%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f608 : bv 32 := @BV 32 0x02a55513%Z I.

Lemma D_8f608 : decode_any W_8f608 = Some (ShiftImm ALU_SRL (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 6 42%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f60c : bv 32 := @BV 32 0x00a48933%Z I.

Lemma D_8f60c : decode_any W_8f60c = Some (Op ALU_ADD (@BV 5 18%Z I) (@BV 5 9%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f610 : bv 32 := @BV 32 0x00092503%Z I.

Lemma D_8f610 : decode_any W_8f610 = Some (Load SZ4 true (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f614 : bv 32 := @BV 32 0x01068c1b%Z I.

Lemma D_8f614 : decode_any W_8f614 = Some (OpImm32 (@BV 5 24%Z I) (@BV 5 13%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f618 : bv 32 := @BV 32 0x01848c33%Z I.

Lemma D_8f618 : decode_any W_8f618 = Some (Op ALU_ADD (@BV 5 24%Z I) (@BV 5 9%Z I) (@BV 5 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f61c : bv 32 := @BV 32 0x0230000f%Z I.

Lemma D_8f61c : decode_any W_8f61c = Some (Fence (@BV 4 0%Z I) (@BV 4 2%Z I) (@BV 4 3%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f620 : bv 32 := @BV 32 0x01757cb3%Z I.

Lemma D_8f620 : decode_any W_8f620 = Some (Op ALU_AND (@BV 5 25%Z I) (@BV 5 10%Z I) (@BV 5 23%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f624 : bv 32 := @BV 32 0x0086869b%Z I.

Lemma D_8f624 : decode_any W_8f624 = Some (OpImm32 (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f628 : bv 32 := @BV 32 0x00d48a33%Z I.

Lemma D_8f628 : decode_any W_8f628 = Some (Op ALU_ADD (@BV 5 20%Z I) (@BV 5 9%Z I) (@BV 5 13%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f62c : bv 32 := @BV 32 0x000c8593%Z I.

Lemma D_8f62c : decode_any W_8f62c = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 25%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f630 : bv 32 := @BV 32 0x04058c63%Z I.

Lemma D_8f630 : decode_any W_8f630 = Some (Branch BC_EQ (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 88%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f634 : bv 32 := @BV 32 0x00058513%Z I.

Lemma D_8f634 : decode_any W_8f634 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f638 : bv 32 := @BV 32 0x0105d59b%Z I.

Lemma D_8f638 : decode_any W_8f638 = Some (ShiftImm32 ALU_SRL (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f63c : bv 32 := @BV 32 0x00359613%Z I.

Lemma D_8f63c : decode_any W_8f63c = Some (ShiftImm ALU_SLL (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 6 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f640 : bv 32 := @BV 32 0x00cc0633%Z I.

Lemma D_8f640 : decode_any W_8f640 = Some (Op ALU_ADD (@BV 5 12%Z I) (@BV 5 24%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f644 : bv 32 := @BV 32 0x00063603%Z I.

Lemma D_8f644 : decode_any W_8f644 = Some (Load SZ8 true (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f648 : bv 32 := @BV 32 0x02060463%Z I.

Lemma D_8f648 : decode_any W_8f648 = Some (Branch BC_EQ (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 13 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f64c : bv 32 := @BV 32 0x02051593%Z I.

Lemma D_8f64c : decode_any W_8f64c = Some (ShiftImm ALU_SLL (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f650 : bv 32 := @BV 32 0x0205d593%Z I.

Lemma D_8f650 : decode_any W_8f650 = Some (ShiftImm ALU_SRL (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f654 : bv 32 := @BV 32 0x0165f5b3%Z I.

Lemma D_8f654 : decode_any W_8f654 = Some (Op ALU_AND (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 22%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f658 : bv 32 := @BV 32 0x00459593%Z I.

Lemma D_8f658 : decode_any W_8f658 = Some (ShiftImm ALU_SLL (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 6 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f65c : bv 32 := @BV 32 0x00b605b3%Z I.

Lemma D_8f65c : decode_any W_8f65c = Some (Op ALU_ADD (@BV 5 11%Z I) (@BV 5 12%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f660 : bv 32 := @BV 32 0x0005b603%Z I.

Lemma D_8f660 : decode_any W_8f660 = Some (Load SZ8 true (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f664 : bv 32 := @BV 32 0x0085a583%Z I.

Lemma D_8f664 : decode_any W_8f664 = Some (Load SZ4 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f668 : bv 32 := @BV 32 0xfcc994e3%Z I.

Lemma D_8f668 : decode_any W_8f668 = Some (Branch BC_NE (@BV 5 19%Z I) (@BV 5 12%Z I) (@BV 13 8136%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f66c : bv 32 := @BV 32 0x0c80006f%Z I.

Lemma D_8f66c : decode_any W_8f66c = Some (Jal (@BV 5 0%Z I) (@BV 21 200%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f670 : bv 32 := @BV 32 0x00050a93%Z I.



(* [comment removed for export] *)
Definition W_8f674 : bv 32 := @BV 32 0x000a0513%Z I.



(* [comment removed for export] *)
Definition W_8f678 : bv 32 := @BV 32 0x69c000ef%Z I.



(* [comment removed for export] *)
Definition W_8f67c : bv 32 := @BV 32 0x00050613%Z I.



(* [comment removed for export] *)
Definition W_8f680 : bv 32 := @BV 32 0x000a8513%Z I.



(* [comment removed for export] *)
Definition W_8f684 : bv 32 := @BV 32 0xfc9ff06f%Z I.



(* [comment removed for export] *)
Definition W_8f688 : bv 32 := @BV 32 0x00090513%Z I.
Lemma F_8f688 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f688%Z I : word) = Some W_8f688.
Proof. vm_refl. Qed.
Lemma D_8f688 : decode_any W_8f688 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f68c : bv 32 := @BV 32 0x5f8000ef%Z I.
Lemma F_8f68c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f68c%Z I : word) = Some W_8f68c.
Proof. vm_refl. Qed.
Lemma D_8f68c : decode_any W_8f68c = Some (Jal (@BV 5 1%Z I) (@BV 21 1528%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f690 : bv 32 := @BV 32 0x00050a93%Z I.
Lemma F_8f690 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f690%Z I : word) = Some W_8f690.
Proof. vm_refl. Qed.
Lemma D_8f690 : decode_any W_8f690 = Some (OpImm ALU_ADD (@BV 5 21%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f694 : bv 32 := @BV 32 0x03950663%Z I.
Lemma F_8f694 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f694%Z I : word) = Some W_8f694.
Proof. vm_refl. Qed.
Lemma D_8f694 : decode_any W_8f694 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 25%Z I) (@BV 13 44%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f698 : bv 32 := @BV 32 0x00813603%Z I.



(* [comment removed for export] *)
Definition W_8f69c : bv 32 := @BV 32 0x01013683%Z I.



(* [comment removed for export] *)
Definition W_8f6a0 : bv 32 := @BV 32 0x00048513%Z I.



(* [comment removed for export] *)
Definition W_8f6a4 : bv 32 := @BV 32 0x000a8593%Z I.



(* [comment removed for export] *)
Definition W_8f6a8 : bv 32 := @BV 32 0x00098713%Z I.



(* [comment removed for export] *)
Definition W_8f6ac : bv 32 := @BV 32 0x524000ef%Z I.



(* [comment removed for export] *)
Definition W_8f6b0 : bv 32 := @BV 32 0x00050863%Z I.



(* [comment removed for export] *)
Definition W_8f6b4 : bv 32 := @BV 32 0x0310000f%Z I.



(* [comment removed for export] *)
Definition W_8f6b8 : bv 32 := @BV 32 0x01592023%Z I.



(* [comment removed for export] *)
Definition W_8f6bc : bv 32 := @BV 32 0x0780006f%Z I.



(* [comment removed for export] *)
Definition W_8f6c0 : bv 32 := @BV 32 0x00400537%Z I.
Lemma F_8f6c0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f6c0%Z I : word) = Some W_8f6c0.
Proof. vm_refl. Qed.
Lemma D_8f6c0 : decode_any W_8f6c0 = Some (Lui (@BV 5 10%Z I) (@BV 20 1024%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6c4 : bv 32 := @BV 32 0x00a48533%Z I.
Lemma F_8f6c4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f6c4%Z I : word) = Some W_8f6c4.
Proof. vm_refl. Qed.
Lemma D_8f6c4 : decode_any W_8f6c4 = Some (Op ALU_ADD (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6c8 : bv 32 := @BV 32 0x00100593%Z I.
Lemma F_8f6c8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f6c8%Z I : word) = Some W_8f6c8.
Proof. vm_refl. Qed.
Lemma D_8f6c8 : decode_any W_8f6c8 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6cc : bv 32 := @BV 32 0x00b5252f%Z I.
Lemma F_8f6cc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f6cc%Z I : word) = Some W_8f6cc.
Proof. vm_refl. Qed.
Lemma D_8f6cc : decode_any W_8f6cc = Some (Amo AMO_ADD AW false false (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6d0 : bv 32 := @BV 32 0x0015051b%Z I.
Lemma F_8f6d0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f6d0%Z I : word) = Some W_8f6d0.
Proof. vm_refl. Qed.
Lemma D_8f6d0 : decode_any W_8f6d0 = Some (OpImm32 (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6d4 : bv 32 := @BV 32 0x02051493%Z I.
Lemma F_8f6d4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f6d4%Z I : word) = Some W_8f6d4.
Proof. vm_refl. Qed.
Lemma D_8f6d4 : decode_any W_8f6d4 = Some (ShiftImm ALU_SLL (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6d8 : bv 32 := @BV 32 0x0204d493%Z I.
Lemma F_8f6d8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f6d8%Z I : word) = Some W_8f6d8.
Proof. vm_refl. Qed.
Lemma D_8f6d8 : decode_any W_8f6d8 = Some (ShiftImm ALU_SRL (@BV 5 9%Z I) (@BV 5 9%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6dc : bv 32 := @BV 32 0x08054663%Z I.
Lemma F_8f6dc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f6dc%Z I : word) = Some W_8f6dc.
Proof. vm_refl. Qed.
Lemma D_8f6dc : decode_any W_8f6dc = Some (Branch BC_LT (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 140%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6e0 : bv 32 := @BV 32 0x00050b93%Z I.
Lemma F_8f6e0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f6e0%Z I : word) = Some W_8f6e0.
Proof. vm_refl. Qed.
Lemma D_8f6e0 : decode_any W_8f6e0 = Some (OpImm ALU_ADD (@BV 5 23%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6e4 : bv 32 := @BV 32 0x0104d593%Z I.
Lemma F_8f6e4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f6e4%Z I : word) = Some W_8f6e4.
Proof. vm_refl. Qed.
Lemma D_8f6e4 : decode_any W_8f6e4 = Some (ShiftImm ALU_SRL (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 6 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6e8 : bv 32 := @BV 32 0x00359513%Z I.
Lemma F_8f6e8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f6e8%Z I : word) = Some W_8f6e8.
Proof. vm_refl. Qed.
Lemma D_8f6e8 : decode_any W_8f6e8 = Some (ShiftImm ALU_SLL (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 6 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6ec : bv 32 := @BV 32 0x00ac0533%Z I.
Lemma F_8f6ec : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f6ec%Z I : word) = Some W_8f6ec.
Proof. vm_refl. Qed.
Lemma D_8f6ec : decode_any W_8f6ec = Some (Op ALU_ADD (@BV 5 10%Z I) (@BV 5 24%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6f0 : bv 32 := @BV 32 0x00053503%Z I.
Lemma F_8f6f0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f6f0%Z I : word) = Some W_8f6f0.
Proof. vm_refl. Qed.
Lemma D_8f6f0 : decode_any W_8f6f0 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6f4 : bv 32 := @BV 32 0x08050a63%Z I.
Lemma F_8f6f4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f6f4%Z I : word) = Some W_8f6f4.
Proof. vm_refl. Qed.
Lemma D_8f6f4 : decode_any W_8f6f4 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 148%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6f8 : bv 32 := @BV 32 0x0164f5b3%Z I.
Lemma F_8f6f8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f6f8%Z I : word) = Some W_8f6f8.
Proof. vm_refl. Qed.
Lemma D_8f6f8 : decode_any W_8f6f8 = Some (Op ALU_AND (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 5 22%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6fc : bv 32 := @BV 32 0x00459593%Z I.
Lemma F_8f6fc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f6fc%Z I : word) = Some W_8f6fc.
Proof. vm_refl. Qed.
Lemma D_8f6fc : decode_any W_8f6fc = Some (ShiftImm ALU_SLL (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 6 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f700 : bv 32 := @BV 32 0x00b504b3%Z I.
Lemma F_8f700 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f700%Z I : word) = Some W_8f700.
Proof. vm_refl. Qed.
Lemma D_8f700 : decode_any W_8f700 = Some (Op ALU_ADD (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f704 : bv 32 := @BV 32 0x00810613%Z I.
Lemma F_8f704 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f704%Z I : word) = Some W_8f704.
Proof. vm_refl. Qed.
Lemma D_8f704 : decode_any W_8f704 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f708 : bv 32 := @BV 32 0x00048513%Z I.
Lemma F_8f708 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f708%Z I : word) = Some W_8f708.
Proof. vm_refl. Qed.
Lemma D_8f708 : decode_any W_8f708 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f70c : bv 32 := @BV 32 0x00000593%Z I.
Lemma F_8f70c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f70c%Z I : word) = Some W_8f70c.
Proof. vm_refl. Qed.
Lemma D_8f70c : decode_any W_8f70c = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f710 : bv 32 := @BV 32 0x00098693%Z I.
Lemma F_8f710 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f710%Z I : word) = Some W_8f710.
Proof. vm_refl. Qed.
Lemma D_8f710 : decode_any W_8f710 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f714 : bv 32 := @BV 32 0xaf5ff0ef%Z I.
Lemma F_8f714 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f714%Z I : word) = Some W_8f714.
Proof. vm_refl. Qed.
Lemma D_8f714 : decode_any W_8f714 = Some (Jal (@BV 5 1%Z I) (@BV 21 2095860%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f718 : bv 32 := @BV 32 0x0154a423%Z I.
Lemma F_8f718 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f718%Z I : word) = Some W_8f718.
Proof. vm_refl. Qed.
Lemma D_8f718 : decode_any W_8f718 = Some (Store SZ4 (@BV 5 9%Z I) (@BV 5 21%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f71c : bv 32 := @BV 32 0x0310000f%Z I.
Lemma F_8f71c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f71c%Z I : word) = Some W_8f71c.
Proof. vm_refl. Qed.
Lemma D_8f71c : decode_any W_8f71c = Some (Fence (@BV 4 0%Z I) (@BV 4 3%Z I) (@BV 4 1%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f720 : bv 32 := @BV 32 0x000b8513%Z I.
Lemma F_8f720 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f720%Z I : word) = Some W_8f720.
Proof. vm_refl. Qed.
Lemma D_8f720 : decode_any W_8f720 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 23%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f724 : bv 32 := @BV 32 0x01792023%Z I.
Lemma F_8f724 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f724%Z I : word) = Some W_8f724.
Proof. vm_refl. Qed.
Lemma D_8f724 : decode_any W_8f724 = Some (Store SZ4 (@BV 5 18%Z I) (@BV 5 23%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f728 : bv 32 := @BV 32 0x00040663%Z I.
Lemma F_8f728 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f728%Z I : word) = Some W_8f728.
Proof. vm_refl. Qed.
Lemma D_8f728 : decode_any W_8f728 = Some (Branch BC_EQ (@BV 5 8%Z I) (@BV 5 0%Z I) (@BV 13 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f72c : bv 32 := @BV 32 0x00100593%Z I.



(* [comment removed for export] *)
Definition W_8f730 : bv 32 := @BV 32 0x00b40023%Z I.



(* [comment removed for export] *)
Definition W_8f734 : bv 32 := @BV 32 0x06813083%Z I.
Lemma F_8f734 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f734%Z I : word) = Some W_8f734.
Proof. vm_refl. Qed.
Lemma D_8f734 : decode_any W_8f734 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 104%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f738 : bv 32 := @BV 32 0x06013403%Z I.
Lemma F_8f738 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f738%Z I : word) = Some W_8f738.
Proof. vm_refl. Qed.
Lemma D_8f738 : decode_any W_8f738 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 96%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f73c : bv 32 := @BV 32 0x05813483%Z I.
Lemma F_8f73c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f73c%Z I : word) = Some W_8f73c.
Proof. vm_refl. Qed.
Lemma D_8f73c : decode_any W_8f73c = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 88%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f740 : bv 32 := @BV 32 0x05013903%Z I.
Lemma F_8f740 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f740%Z I : word) = Some W_8f740.
Proof. vm_refl. Qed.
Lemma D_8f740 : decode_any W_8f740 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 80%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f744 : bv 32 := @BV 32 0x04813983%Z I.
Lemma F_8f744 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f744%Z I : word) = Some W_8f744.
Proof. vm_refl. Qed.
Lemma D_8f744 : decode_any W_8f744 = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 2%Z I) (@BV 12 72%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f748 : bv 32 := @BV 32 0x04013a03%Z I.
Lemma F_8f748 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f748%Z I : word) = Some W_8f748.
Proof. vm_refl. Qed.
Lemma D_8f748 : decode_any W_8f748 = Some (Load SZ8 true (@BV 5 20%Z I) (@BV 5 2%Z I) (@BV 12 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f74c : bv 32 := @BV 32 0x03813a83%Z I.
Lemma F_8f74c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f74c%Z I : word) = Some W_8f74c.
Proof. vm_refl. Qed.
Lemma D_8f74c : decode_any W_8f74c = Some (Load SZ8 true (@BV 5 21%Z I) (@BV 5 2%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f750 : bv 32 := @BV 32 0x03013b03%Z I.
Lemma F_8f750 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f750%Z I : word) = Some W_8f750.
Proof. vm_refl. Qed.
Lemma D_8f750 : decode_any W_8f750 = Some (Load SZ8 true (@BV 5 22%Z I) (@BV 5 2%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f754 : bv 32 := @BV 32 0x02813b83%Z I.
Lemma F_8f754 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f754%Z I : word) = Some W_8f754.
Proof. vm_refl. Qed.
Lemma D_8f754 : decode_any W_8f754 = Some (Load SZ8 true (@BV 5 23%Z I) (@BV 5 2%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f758 : bv 32 := @BV 32 0x02013c03%Z I.
Lemma F_8f758 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f758%Z I : word) = Some W_8f758.
Proof. vm_refl. Qed.
Lemma D_8f758 : decode_any W_8f758 = Some (Load SZ8 true (@BV 5 24%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f75c : bv 32 := @BV 32 0x01813c83%Z I.
Lemma F_8f75c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f75c%Z I : word) = Some W_8f75c.
Proof. vm_refl. Qed.
Lemma D_8f75c : decode_any W_8f75c = Some (Load SZ8 true (@BV 5 25%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f760 : bv 32 := @BV 32 0x07010113%Z I.
Lemma F_8f760 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f760%Z I : word) = Some W_8f760.
Proof. vm_refl. Qed.
Lemma D_8f760 : decode_any W_8f760 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 112%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f764 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_8f764 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f764%Z I : word) = Some W_8f764.
Proof. vm_refl. Qed.
Lemma D_8f764 : decode_any W_8f764 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f768 : bv 32 := @BV 32 0x017576b3%Z I.



(* [comment removed for export] *)
Definition W_8f788 : bv 32 := @BV 32 0x000a0513%Z I.
Lemma F_8f788 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f788%Z I : word) = Some W_8f788.
Proof. vm_refl. Qed.
Lemma D_8f788 : decode_any W_8f788 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 20%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f78c : bv 32 := @BV 32 0x588000ef%Z I.
Lemma F_8f78c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f78c%Z I : word) = Some W_8f78c.
Proof. vm_refl. Qed.
Lemma D_8f78c : decode_any W_8f78c = Some (Jal (@BV 5 1%Z I) (@BV 21 1416%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f790 : bv 32 := @BV 32 0xf69ff06f%Z I.
Lemma F_8f790 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8f790%Z I : word) = Some W_8f790.
Proof. vm_refl. Qed.
Lemma D_8f790 : decode_any W_8f790 = Some (Jal (@BV 5 0%Z I) (@BV 21 2097000%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_8f208_8f794.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupAux.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct Bo_code_8f208_8f794.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGen1.
Context {fx : FPState}.


#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mmM : word := Z_to_bv 64 0xc6a4a7935bd1e995.
Definition mmSEED : word := Z_to_bv 64 0x9747b28c9747b28c.
Definition mmM8 : word := Z_to_bv 64 0x35253c9ade8f4ca8.       (* [comment removed for export] *)
Definition mm_add (h k : word) : word :=
  v_mul (v_xor (v_mul (v_xor (v_srli (v_mul k mmM) 47) (v_mul k mmM)) mmM) h) mmM.
(* [comment removed for export] *)
Definition sd_h0 (sz : Z) : word := v_xor (v_mul (Z_to_bv 64 sz) mmM8) mmSEED.
Fixpoint mm_fold (h : word) (ws : list word) : word := match ws with [] => h | w :: r => mm_fold (mm_add h w) r end.
Definition sd_fin (h : word) (tag : Z) : word :=
  let x1 := mm_add h (Z_to_bv 64 tag) in
  let x2 := v_mul (v_xor (v_srli x1 47) x1) mmM in
  v_xor (v_srli x2 47) x2.
Definition sd_hashN (ws : list word) (tag : Z) : word := sd_fin (mm_fold (sd_h0 (Z.of_nat (length ws))) ws) tag.

Definition sd_bix (h : word) : Z := (bv_unsigned h mod 2 ^ 20)%Z.      (* [comment removed for export] *)

Definition sdput_words : list (option (bv 32)) :=
  [
   Some W_8f4f0; None; None; Some W_8f4fc; Some W_8f500; Some W_8f504; Some W_8f508; Some W_8f50c; Some W_8f510;
   Some W_8f514; Some W_8f518; Some W_8f51c; Some W_8f520; Some W_8f524; Some W_8f528; Some W_8f52c; Some
   W_8f530; Some W_8f534; Some W_8f538; Some W_8f53c; Some W_8f540; Some W_8f544; Some W_8f548; Some W_8f54c;
   Some W_8f550; Some W_8f554; Some W_8f558; Some W_8f55c; Some W_8f560; Some W_8f564; Some W_8f568; Some
   W_8f56c; Some W_8f570; Some W_8f574; Some W_8f578; None; Some W_8f580; Some W_8f584; None; None; Some W_8f590;
   Some W_8f594; Some W_8f598; Some W_8f59c; Some W_8f5a0; Some W_8f5a4; Some W_8f5a8; Some W_8f5ac; Some
   W_8f5b0; Some W_8f5b4; Some W_8f5b8; Some W_8f5bc; Some W_8f5c0; Some W_8f5c4; Some W_8f5c8; Some W_8f5cc;
   Some W_8f5d0; Some W_8f5d4; Some W_8f5d8; Some W_8f5dc; Some W_8f5e0; Some W_8f5e4; Some W_8f5e8; Some
   W_8f5ec; Some W_8f5f0; Some W_8f5f4; Some W_8f5f8; Some W_8f5fc; Some W_8f600; Some W_8f604; Some W_8f608;
   Some W_8f60c; Some W_8f610; Some W_8f614; Some W_8f618; Some W_8f61c; Some W_8f620; Some W_8f624; Some
   W_8f628; Some W_8f62c; Some W_8f630; Some W_8f634; Some W_8f638; Some W_8f63c; Some W_8f640; Some W_8f644;
   Some W_8f648; Some W_8f64c; Some W_8f650; Some W_8f654; Some W_8f658; Some W_8f65c; Some W_8f660; Some
   W_8f664; Some W_8f668; Some W_8f66c; Some W_8f670; Some W_8f674; Some W_8f678; Some W_8f67c; Some W_8f680;
   Some W_8f684; Some W_8f688; Some W_8f68c; Some W_8f690; Some W_8f694; Some W_8f698; Some W_8f69c; Some
   W_8f6a0; Some W_8f6a4; Some W_8f6a8; Some W_8f6ac; Some W_8f6b0; Some W_8f6b4; Some W_8f6b8; Some W_8f6bc;
   Some W_8f6c0; Some W_8f6c4; Some W_8f6c8; Some W_8f6cc; Some W_8f6d0; Some W_8f6d4; Some W_8f6d8; Some
   W_8f6dc; Some W_8f6e0; Some W_8f6e4; Some W_8f6e8; Some W_8f6ec; Some W_8f6f0; Some W_8f6f4; Some W_8f6f8;
   Some W_8f6fc; Some W_8f700; Some W_8f704; Some W_8f708; Some W_8f70c; Some W_8f710; Some W_8f714; Some
   W_8f718; Some W_8f71c; Some W_8f720; Some W_8f724; Some W_8f728; Some W_8f72c; Some W_8f730; Some W_8f734;
   Some W_8f738; Some W_8f73c; Some W_8f740; Some W_8f744; Some W_8f748; Some W_8f74c; Some W_8f750; Some
   W_8f754; Some W_8f758; Some W_8f75c; Some W_8f760; Some W_8f764; Some W_8f768
  ]%list.

Definition sd_clob : list reg := [10; 11; 12; 13; 14; 15; 16; 17].
Definition sd_clobx : list reg := [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 10; 11; 12; 13; 14; 15; 16; 17].

(* [comment removed for export] *)
Definition sd_frame (mem : word -> option byte) (sp : word) (regs : bvmap 5 word) (ra tr a1w : word) : word -> option byte :=
  wbytes (wbytes
  (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ sp (-8)) (LE8 ra)) (at_ sp (-16)) (LE8 (getr regs 8))) (at_ sp (-24)) (LE8 (getr regs 9)))
    (at_ sp (-32)) (LE8 (getr regs 18))) (at_ sp (-40)) (LE8 (getr regs 19))) (at_ sp (-48)) (LE8 (getr regs 20)))
    (at_ sp (-56)) (LE8 (getr regs 21))) (at_ sp (-64)) (LE8 (getr regs 22))) (at_ sp (-72)) (LE8 (getr regs 23)))
    (at_ sp (-80)) (LE8 (getr regs 24))) (at_ sp (-88)) (LE8 (getr regs 25)))
    (at_ sp (-104)) (LE8 tr)) (at_ sp (-96)) (LE8 a1w).

Lemma sd_frame_outside : forall mem sp regs ra tr a1w (x : word),
  (112 <= bv_unsigned sp)%Z ->
  (bv_unsigned x < bv_unsigned sp - 112 \/ bv_unsigned sp <= bv_unsigned x)%Z ->
  sd_frame mem sp regs ra tr a1w x = mem x.
Proof using.
  intros mem sp regs ra tr a1w x Hsp Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold sd_frame in G in change_no_check G' end).
  rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; try reflexivity; (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia.
Qed.

Record sd_tab := SDT { st_base : word; st_depot : word; st_g_m8 : Z; st_g_seed : Z; st_g_m : Z }.
Record sd_tab_ok (segs : list Segment) (t : sd_tab) : Prop := SDTOK {
  sto_code : code_ato segs (st_base t) 0 sdput_words;
  sto_a4 : gaddr2 segs (st_base t) 4 11 11 (st_depot t);
  sto_g128 : gauipc_ld segs (st_base t) 128 156 14 10 (st_g_m t);
  sto_g132 : gauipc_ld segs (st_base t) 132 140 15 15 (st_g_m8 t);
  sto_g148 : gauipc_ld segs (st_base t) 148 152 10 16 (st_g_seed t);
  sto_depot : (bv_unsigned (st_depot t) + 0x500000 < 2 ^ 64)%Z }.

(* [comment removed for export] *)
Lemma skipn_nth_cons : forall {A} (l : list A) (i : nat) (d : A), (i < length l)%nat -> skipn i l = nth i l d :: skipn (S i) l.
Proof using.
  intros A l. induction l as [|x l IH]; intros i d Hi; cbn in Hi; [lia|].
  destruct i as [|i]; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). apply IH. lia.
Qed.
Lemma skipn_nil_len : forall {A} (l : list A) (i : nat), (length l <= i)%nat -> skipn i l = [].
Proof using. intros A l i Hi. apply skipn_all2. exact Hi. Qed.

Section DEPOT.
  Variable segs : list Segment.
  Variables base D : word.
  Variables g_m8 g_seed g_m : Z.
  Hypothesis HC : code_ato segs base 0 sdput_words.
  Hypothesis A4 : gaddr2 segs base 4 11 11 D.
  Hypothesis G128 : gauipc_ld segs base 128 156 14 10 g_m.
  Hypothesis G132 : gauipc_ld segs base 132 140 15 15 g_m8.
  Hypothesis G148 : gauipc_ld segs base 148 152 10 16 g_seed.
  Hypothesis HD : (bv_unsigned D + 0x500000 < 2 ^ 64)%Z.

  Lemma Xf9028 : fetch_word segs (at_ base 0) = Some W_8f4f0.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 0 _ HC eq_refl). Qed.
  Lemma Xf9034 : fetch_word segs (at_ base 12) = Some W_8f4fc.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 3 _ HC eq_refl). Qed.
  Lemma Xf9038 : fetch_word segs (at_ base 16) = Some W_8f500.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 4 _ HC eq_refl). Qed.
  Lemma Xf903c : fetch_word segs (at_ base 20) = Some W_8f504.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 5 _ HC eq_refl). Qed.
  Lemma Xf9040 : fetch_word segs (at_ base 24) = Some W_8f508.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 6 _ HC eq_refl). Qed.
  Lemma Xf9044 : fetch_word segs (at_ base 28) = Some W_8f50c.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 7 _ HC eq_refl). Qed.
  Lemma Xf9048 : fetch_word segs (at_ base 32) = Some W_8f510.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 8 _ HC eq_refl). Qed.
  Lemma Xf904c : fetch_word segs (at_ base 36) = Some W_8f514.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 9 _ HC eq_refl). Qed.
  Lemma Xf9050 : fetch_word segs (at_ base 40) = Some W_8f518.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 10 _ HC eq_refl). Qed.
  Lemma Xf9054 : fetch_word segs (at_ base 44) = Some W_8f51c.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 11 _ HC eq_refl). Qed.
  Lemma Xf9058 : fetch_word segs (at_ base 48) = Some W_8f520.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 12 _ HC eq_refl). Qed.
  Lemma Xf905c : fetch_word segs (at_ base 52) = Some W_8f524.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 13 _ HC eq_refl). Qed.
  Lemma Xf9060 : fetch_word segs (at_ base 56) = Some W_8f528.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 14 _ HC eq_refl). Qed.
  Lemma Xf9064 : fetch_word segs (at_ base 60) = Some W_8f52c.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 15 _ HC eq_refl). Qed.
  Lemma Xf9068 : fetch_word segs (at_ base 64) = Some W_8f530.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 16 _ HC eq_refl). Qed.
  Lemma Xf906c : fetch_word segs (at_ base 68) = Some W_8f534.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 17 _ HC eq_refl). Qed.
  Lemma Xf9070 : fetch_word segs (at_ base 72) = Some W_8f538.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 18 _ HC eq_refl). Qed.
  Lemma Xf9074 : fetch_word segs (at_ base 76) = Some W_8f53c.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 19 _ HC eq_refl). Qed.
  Lemma Xf9078 : fetch_word segs (at_ base 80) = Some W_8f540.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 20 _ HC eq_refl). Qed.
  Lemma Xf907c : fetch_word segs (at_ base 84) = Some W_8f544.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 21 _ HC eq_refl). Qed.
  Lemma Xf9080 : fetch_word segs (at_ base 88) = Some W_8f548.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 22 _ HC eq_refl). Qed.
  Lemma Xf9084 : fetch_word segs (at_ base 92) = Some W_8f54c.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 23 _ HC eq_refl). Qed.
  Lemma Xf9088 : fetch_word segs (at_ base 96) = Some W_8f550.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 24 _ HC eq_refl). Qed.
  Lemma Xf9090 : fetch_word segs (at_ base 104) = Some W_8f558.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 26 _ HC eq_refl). Qed.
  Lemma Xf9094 : fetch_word segs (at_ base 108) = Some W_8f55c.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 27 _ HC eq_refl). Qed.
  Lemma Xf9098 : fetch_word segs (at_ base 112) = Some W_8f560.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 28 _ HC eq_refl). Qed.
  Lemma Xf909c : fetch_word segs (at_ base 116) = Some W_8f564.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 29 _ HC eq_refl). Qed.
  Lemma Xf90a0 : fetch_word segs (at_ base 120) = Some W_8f568.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 30 _ HC eq_refl). Qed.
  Lemma Xf90a4 : fetch_word segs (at_ base 124) = Some W_8f56c.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 31 _ HC eq_refl). Qed.


  Lemma Xf90b0 : fetch_word segs (at_ base 136) = Some W_8f578.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 34 _ HC eq_refl). Qed.
  Lemma Xf90b8 : fetch_word segs (at_ base 144) = Some W_8f580.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 36 _ HC eq_refl). Qed.
  Lemma Xf90c8 : fetch_word segs (at_ base 160) = Some W_8f590.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 40 _ HC eq_refl). Qed.
  Lemma Xf90cc : fetch_word segs (at_ base 164) = Some W_8f594.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 41 _ HC eq_refl). Qed.
  Lemma Xf90d0 : fetch_word segs (at_ base 168) = Some W_8f598.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 42 _ HC eq_refl). Qed.
  Lemma Xf90d4 : fetch_word segs (at_ base 172) = Some W_8f59c.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 43 _ HC eq_refl). Qed.
  Lemma Xf90d8 : fetch_word segs (at_ base 176) = Some W_8f5a0.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 44 _ HC eq_refl). Qed.
  Lemma Xf90dc : fetch_word segs (at_ base 180) = Some W_8f5a4.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 45 _ HC eq_refl). Qed.
  Lemma Xf90e0 : fetch_word segs (at_ base 184) = Some W_8f5a8.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 46 _ HC eq_refl). Qed.
  Lemma Xf90e4 : fetch_word segs (at_ base 188) = Some W_8f5ac.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 47 _ HC eq_refl). Qed.
  Lemma Xf90e8 : fetch_word segs (at_ base 192) = Some W_8f5b0.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 48 _ HC eq_refl). Qed.
  Lemma Xf90ec : fetch_word segs (at_ base 196) = Some W_8f5b4.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 49 _ HC eq_refl). Qed.
  Lemma Xf90f0 : fetch_word segs (at_ base 200) = Some W_8f5b8.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 50 _ HC eq_refl). Qed.
  Lemma Xf90f4 : fetch_word segs (at_ base 204) = Some W_8f5bc.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 51 _ HC eq_refl). Qed.
  Lemma Xf90f8 : fetch_word segs (at_ base 208) = Some W_8f5c0.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 52 _ HC eq_refl). Qed.
  Lemma Xf90fc : fetch_word segs (at_ base 212) = Some W_8f5c4.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 53 _ HC eq_refl). Qed.
  Lemma Xf9100 : fetch_word segs (at_ base 216) = Some W_8f5c8.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 54 _ HC eq_refl). Qed.
  Lemma Xf9104 : fetch_word segs (at_ base 220) = Some W_8f5cc.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 55 _ HC eq_refl). Qed.
  Lemma Xf9108 : fetch_word segs (at_ base 224) = Some W_8f5d0.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 56 _ HC eq_refl). Qed.
  Lemma Xf910c : fetch_word segs (at_ base 228) = Some W_8f5d4.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 57 _ HC eq_refl). Qed.
  Lemma Xf9110 : fetch_word segs (at_ base 232) = Some W_8f5d8.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 58 _ HC eq_refl). Qed.
  Lemma Xf9114 : fetch_word segs (at_ base 236) = Some W_8f5dc.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 59 _ HC eq_refl). Qed.
  Lemma Xf9118 : fetch_word segs (at_ base 240) = Some W_8f5e0.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 60 _ HC eq_refl). Qed.
  Lemma Xf911c : fetch_word segs (at_ base 244) = Some W_8f5e4.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 61 _ HC eq_refl). Qed.
  Lemma Xf9120 : fetch_word segs (at_ base 248) = Some W_8f5e8.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 62 _ HC eq_refl). Qed.
  Lemma Xf9124 : fetch_word segs (at_ base 252) = Some W_8f5ec.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 63 _ HC eq_refl). Qed.
  Lemma Xf9128 : fetch_word segs (at_ base 256) = Some W_8f5f0.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 64 _ HC eq_refl). Qed.
  Lemma Xf912c : fetch_word segs (at_ base 260) = Some W_8f5f4.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 65 _ HC eq_refl). Qed.
  Lemma Xf9130 : fetch_word segs (at_ base 264) = Some W_8f5f8.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 66 _ HC eq_refl). Qed.
  Lemma Xf9134 : fetch_word segs (at_ base 268) = Some W_8f5fc.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 67 _ HC eq_refl). Qed.
  Lemma Xf9138 : fetch_word segs (at_ base 272) = Some W_8f600.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 68 _ HC eq_refl). Qed.
  Lemma Xf913c : fetch_word segs (at_ base 276) = Some W_8f604.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 69 _ HC eq_refl). Qed.
  Lemma Xf9140 : fetch_word segs (at_ base 280) = Some W_8f608.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 70 _ HC eq_refl). Qed.
  Lemma Xf9144 : fetch_word segs (at_ base 284) = Some W_8f60c.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 71 _ HC eq_refl). Qed.
  Lemma Xf9148 : fetch_word segs (at_ base 288) = Some W_8f610.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 72 _ HC eq_refl). Qed.
  Lemma Xf914c : fetch_word segs (at_ base 292) = Some W_8f614.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 73 _ HC eq_refl). Qed.
  Lemma Xf9150 : fetch_word segs (at_ base 296) = Some W_8f618.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 74 _ HC eq_refl). Qed.
  Lemma Xf9154 : fetch_word segs (at_ base 300) = Some W_8f61c.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 75 _ HC eq_refl). Qed.
  Lemma Xf9158 : fetch_word segs (at_ base 304) = Some W_8f620.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 76 _ HC eq_refl). Qed.
  Lemma Xf915c : fetch_word segs (at_ base 308) = Some W_8f624.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 77 _ HC eq_refl). Qed.
  Lemma Xf9160 : fetch_word segs (at_ base 312) = Some W_8f628.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 78 _ HC eq_refl). Qed.
  Lemma Xf9164 : fetch_word segs (at_ base 316) = Some W_8f62c.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 79 _ HC eq_refl). Qed.
  Lemma Xf9168 : fetch_word segs (at_ base 320) = Some W_8f630.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 80 _ HC eq_refl). Qed.
  Lemma Xf916c : fetch_word segs (at_ base 324) = Some W_8f634.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 81 _ HC eq_refl). Qed.
  Lemma Xf9170 : fetch_word segs (at_ base 328) = Some W_8f638.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 82 _ HC eq_refl). Qed.
  Lemma Xf9174 : fetch_word segs (at_ base 332) = Some W_8f63c.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 83 _ HC eq_refl). Qed.
  Lemma Xf9178 : fetch_word segs (at_ base 336) = Some W_8f640.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 84 _ HC eq_refl). Qed.
  Lemma Xf917c : fetch_word segs (at_ base 340) = Some W_8f644.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 85 _ HC eq_refl). Qed.
  Lemma Xf9180 : fetch_word segs (at_ base 344) = Some W_8f648.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 86 _ HC eq_refl). Qed.
  Lemma Xf9184 : fetch_word segs (at_ base 348) = Some W_8f64c.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 87 _ HC eq_refl). Qed.
  Lemma Xf9188 : fetch_word segs (at_ base 352) = Some W_8f650.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 88 _ HC eq_refl). Qed.
  Lemma Xf918c : fetch_word segs (at_ base 356) = Some W_8f654.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 89 _ HC eq_refl). Qed.
  Lemma Xf9190 : fetch_word segs (at_ base 360) = Some W_8f658.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 90 _ HC eq_refl). Qed.
  Lemma Xf9194 : fetch_word segs (at_ base 364) = Some W_8f65c.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 91 _ HC eq_refl). Qed.
  Lemma Xf9198 : fetch_word segs (at_ base 368) = Some W_8f660.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 92 _ HC eq_refl). Qed.
  Lemma Xf919c : fetch_word segs (at_ base 372) = Some W_8f664.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 93 _ HC eq_refl). Qed.
  Lemma Xf91a0 : fetch_word segs (at_ base 376) = Some W_8f668.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 94 _ HC eq_refl). Qed.
  Lemma Xf91a4 : fetch_word segs (at_ base 380) = Some W_8f66c.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 95 _ HC eq_refl). Qed.
  Lemma Xf926c : fetch_word segs (at_ base 580) = Some W_8f734.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 145 _ HC eq_refl). Qed.
  Lemma Xf9270 : fetch_word segs (at_ base 584) = Some W_8f738.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 146 _ HC eq_refl). Qed.
  Lemma Xf9274 : fetch_word segs (at_ base 588) = Some W_8f73c.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 147 _ HC eq_refl). Qed.
  Lemma Xf9278 : fetch_word segs (at_ base 592) = Some W_8f740.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 148 _ HC eq_refl). Qed.
  Lemma Xf927c : fetch_word segs (at_ base 596) = Some W_8f744.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 149 _ HC eq_refl). Qed.
  Lemma Xf9280 : fetch_word segs (at_ base 600) = Some W_8f748.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 150 _ HC eq_refl). Qed.
  Lemma Xf9284 : fetch_word segs (at_ base 604) = Some W_8f74c.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 151 _ HC eq_refl). Qed.
  Lemma Xf9288 : fetch_word segs (at_ base 608) = Some W_8f750.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 152 _ HC eq_refl). Qed.
  Lemma Xf928c : fetch_word segs (at_ base 612) = Some W_8f754.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 153 _ HC eq_refl). Qed.
  Lemma Xf9290 : fetch_word segs (at_ base 616) = Some W_8f758.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 154 _ HC eq_refl). Qed.
  Lemma Xf9294 : fetch_word segs (at_ base 620) = Some W_8f75c.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 155 _ HC eq_refl). Qed.
  Lemma Xf9298 : fetch_word segs (at_ base 624) = Some W_8f760.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 156 _ HC eq_refl). Qed.
  Lemma Xf929c : fetch_word segs (at_ base 628) = Some W_8f764.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 157 _ HC eq_refl). Qed.

  (* [comment removed for export] *)
  Variable mem : word -> option byte.
  Variable rom : word -> option byte.
  Variables tr sp ra : word.
  Variable ws : list word.                 (* [comment removed for export] *)
  Variables sz tag : Z.                     (* [comment removed for export] *)
  Variable NIDS : Z.                        (* [comment removed for export] *)
  Variables (tabf : Z -> Z) (blkf : Z -> word) (hashf : Z -> word) (linkf : Z -> Z).
  #[local] Abbreviation U := bv_unsigned.
  #[local] Abbreviation a1w := (Z_to_bv 64 (sz + tag * 2 ^ 32)).
  #[local] Abbreviation HSH := (sd_hashN ws tag).
  (* [comment removed for export] *)
  Definition nd (id : Z) : word := at_ (blkf (id / 2 ^ 16)) (16 * (id mod 2 ^ 16)).

  Hypothesis Hsz : Z.of_nat (length ws) = sz /\ (1 <= sz < 2 ^ 31)%Z.
  Hypothesis Htag : (0 <= tag < 2 ^ 32)%Z.
  Hypothesis Rws : forall i, (i < length ws)%nat -> rdn segs mem (at_ tr (8 * Z.of_nat i)) 8 = Some (LE8 (nth i ws (Z_to_bv 64 0))).
  Hypothesis Rm8 : rdn segs mem (Z_to_bv 64 g_m8) 8 = Some (LE8 mmM8).
  Hypothesis Rseed : rdn segs mem (Z_to_bv 64 g_seed) 8 = Some (LE8 mmSEED).
  Hypothesis Rm : rdn segs mem (Z_to_bv 64 g_m) 8 = Some (LE8 mmM).
  Hypothesis Hnids : (0 <= NIDS < 2 ^ 31 - 1)%Z.
  Hypothesis Rtab : forall b, (0 <= b < 2 ^ 20)%Z -> rdn segs mem (Z_to_bv 64 (U D + 4 * b)) 4 = Some (LE4 (tabf b)) /\ (0 <= tabf b <= NIDS)%Z.
  Hypothesis Rmap : forall i, (0 <= i <= NIDS / 2 ^ 16)%Z ->
    rdn segs mem (Z_to_bv 64 (U D + 0x400010 + 8 * i)) 8 = Some (LE8 (blkf i)) /\ U (blkf i) <> 0%Z /\ (U (blkf i) + 2 ^ 20 <= 2 ^ 64)%Z.
  Hypothesis Rnode : forall id, (1 <= id <= NIDS)%Z ->
    rdn segs mem (nd id) 8 = Some (LE8 (hashf id)) /\ rdn segs mem (at_ (nd id) 8) 4 = Some (LE4 (linkf id)) /\ (0 <= linkf id < id)%Z.
  (* [comment removed for export] *)
  Hypothesis Hsp : (2 ^ 32 + 112 <= U sp)%Z /\ (U sp < 2 ^ 64)%Z.
  Hypothesis Hstk : store_ok segs mem (at_ sp (-112)) 112 = true.
  Hypothesis Htr : (U tr + 8 * sz <= U sp - 112 \/ U sp <= U tr)%Z /\ (0 < U tr)%Z /\ (U tr + 8 * sz < 2 ^ 64)%Z.
  Hypothesis Hcells : Forall (fun c => 0 <= c /\ c + 8 <= 2 ^ 32)%Z [g_m8; g_seed; g_m].
  Hypothesis HD32 : (U D + 0x500000 <= 2 ^ 32)%Z.
  Hypothesis Hblk : forall i, (0 <= i <= NIDS / 2 ^ 16)%Z -> (U (blkf i) + 2 ^ 20 <= U sp - 112 \/ U sp <= U (blkf i))%Z.
  Hypothesis Hret : ret_ok ra.

  #[local] Abbreviation CL := (fun r => In r sd_clob).
  #[local] Abbreviation CLX := (fun r => In r sd_clobx).

  Lemma X0' : fetch_word segs base = Some W_8f4f0.
  Proof using HC. rewrite <- (at_0 base). exact Xf9028. Qed.

  Ltac cells_split :=
    let HC := fresh "HC" in
    pose proof Hcells as HC;
    repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC; destruct HC as [? HC] end.

  Lemma bix_range : forall h : word, (0 <= sd_bix h < 2 ^ 20)%Z.
  Proof using. intros h. (lazymatch goal with |- ?G => let G' := eval unfold sd_bix in G in change_no_check G' end). apply Z.mod_pos_bound. lia. Qed.
  Lemma id16 : forall id, (0 <= id <= NIDS)%Z -> (0 <= id / 2 ^ 16 <= NIDS / 2 ^ 16)%Z /\ (0 <= id mod 2 ^ 16 < 2 ^ 16)%Z /\ (id / 2 ^ 16 < 2 ^ 15)%Z.
  Proof using Hnids ws.
    intros id Hid. split; [split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia] |].
    split; [apply Z.mod_pos_bound; lia | apply Z.div_lt_upper_bound; lia].
  Qed.
  Lemma Ua1w : U a1w = (sz + tag * 2 ^ 32)%Z.
  Proof using Htag Hsz ws. unorm. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma bix_shift : forall h : word, v_srli (v_slli h 44) 42 = Z_to_bv 64 (4 * sd_bix h).
  Proof using ws.
    intros h. pose proof (u64_range h). (lazymatch goal with |- ?G => let G' := eval unfold v_srli, v_slli, sd_bix in G in change_no_check G' end). f_equal.
    rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. rewrite Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 64) with (2 ^ 44 * 2 ^ 20)%Z.
    rewrite Z.mul_comm. rewrite Z.mul_mod_distr_l by lia.
    replace (2 ^ 44)%Z with (2 ^ 42 * 4)%Z by reflexivity.
    rewrite <- Z.mul_assoc, (Z.mul_comm (2 ^ 42)), Z.div_mul by lia. lia.
  Qed.
  Lemma land_ones_small : forall a k, (0 < k)%Z -> (0 <= a < 2 ^ k)%Z -> Z.land a (Z.ones k) = a.
  Proof using ws. intros a k Hk Ha. rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
  Lemma v_and_bw31 : forall BW, (0 <= BW < 2 ^ 31)%Z -> v_and (Z_to_bv 64 BW) (Z_to_bv 64 2147483647) = Z_to_bv 64 BW.
  Proof using ws. intros BW HBW. (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end). unorm. change 2147483647%Z with (Z.ones 31). rewrite land_ones_small by lia. reflexivity. Qed.
  Lemma v_srliw_bw : forall BW, (0 <= BW < 2 ^ 31)%Z -> v_srliw (Z_to_bv 64 BW) 16 = Z_to_bv 64 (BW / 2 ^ 16).
  Proof using ws.
    intros BW HBW. assert (0 <= BW / 2 ^ 16 < 2 ^ 15)%Z by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    (lazymatch goal with |- ?G => let G' := eval unfold v_srliw in G in change_no_check G' end). f_equal. unorm. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap, bv_swrap in G in change_no_check G' end). change (bv_modulus 32) with (2 ^ 32)%Z.
    change (bv_half_modulus 32) with (2 ^ 31)%Z.
    rewrite (Z.mod_small BW) by lia. rewrite Z.shiftr_div_pow2 by lia. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 32) with (2 ^ 32)%Z.
    rewrite Z.mod_small by lia. lia.
  Qed.
  Lemma v_and_bw16 : forall BW (x : word), (0 <= BW < 2 ^ 31)%Z -> bv_unsigned x = BW -> v_and x (Z_to_bv 64 65535) = Z_to_bv 64 (BW mod 2 ^ 16).
  Proof using. intros BW x HBW Hx. (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end). rewrite Hx. unorm. change 65535%Z with (Z.ones 16). rewrite Z.land_ones by lia. reflexivity. Qed.


  Section WithRegs.
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = tr.
  Hypothesis H11 : getr regs 11 = a1w.

  Definition SM1 : word -> option byte := sd_frame mem sp regs ra tr a1w.

  Lemma SM1_out : forall x : word, (U x < U sp - 112 \/ U sp <= U x)%Z -> SM1 x = mem x.
  Proof using Hsp ws. intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold SM1 in G in change_no_check G' end). apply sd_frame_outside; [lia | exact Hx]. Qed.

  (* [comment removed for export] *)
  Lemma rd_o2 : forall (a : word) k bs,
    (U a + Z.of_nat k <= U sp - 112 \/ U sp <= U a)%Z -> (U a + Z.of_nat k <= 2 ^ 64)%Z ->
    rdn segs mem a k = Some bs -> rdn segs SM1 a k = Some bs.
  Proof using Hsp ws.
    intros a k bs Ha Hnw Hr. rewrite <- Hr. apply rdn_ext; [lia|].
    intros x Hx. apply SM1_out. lia.
  Qed.

  Ltac fsd F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | repeat (eapply store_ok_mono; [apply wbytes_grows|]);
          eapply (store_ok_sub segs mem (at_ sp (-112)) _ 112);
          [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia] ]
      | step_simpl]; vn.
  Ltac addr_n := gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; rewrite ?at_addi; zlit_at;
                 try (progress ((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end)); unorm).
  Ltac rd_close Hr :=
    apply rd_o2;
    [ rewrite ?at_u by lia; first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ]
    | rewrite ?at_u by lia; first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ]
    | first [ exact Hr | rewrite <- Hr; f_equal; apply bv_eq; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; unorm; lia ] ] ].
  Ltac cld F D vv Hr :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D | addr_n; rd_close Hr | apply bytes_le_to_Z_8]
      | step_simpl]; vn.
  Ltac clw F D z Hr :=
    chain_step; [reflexivity
      | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 z)) (v := Z_to_bv 64 z);
        [exact F | reflexivity | exact D | addr_n; rd_close Hr | apply bytes4_small; lia]
      | step_simpl]; rewrite (v_lw_small z) by lia; vn.

  (* [comment removed for export] *)
  Lemma sextw_sz : v_addiw a1w 0 = Z_to_bv 64 sz.
  Proof using Htag Hsz ws.
    (lazymatch goal with |- ?G => let G' := eval unfold v_addiw in G in change_no_check G' end). f_equal. rewrite Ua1w. rewrite Z.add_0_r. (lazymatch goal with |- ?G => let G' := eval unfold bv_swrap, bv_wrap in G in change_no_check G' end).
    change (bv_half_modulus 32) with (2 ^ 31)%Z. change (bv_modulus 32) with (2 ^ 32)%Z.
    rewrite <- (Z.add_assoc), (Z.add_comm (tag * 2 ^ 32)), Z.add_assoc, Z.mod_add by lia.
    rewrite Z.mod_small by lia. lia.
  Qed.
  Lemma srli32_tag : v_srli a1w 32 = Z_to_bv 64 tag.
  Proof using Htag Hsz ws. (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end). f_equal. rewrite Ua1w, Z.shiftr_div_pow2 by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. Qed.
  Lemma and32_sz : v_and a1w (Z_to_bv 64 4294967295) = Z_to_bv 64 sz.
  Proof using Htag Hsz ws.
    (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end). f_equal. rewrite Ua1w. unorm. change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma D1 :
    exists r,
      msteps segs (mkst regs base mem rom) (mkst r (at_ base 160) SM1 rom)
      /\ getr r 2 = at_ sp (-112) /\ getr r 9 = D /\ getr r 11 = tr /\ getr r 12 = Z_to_bv 64 sz /\ getr r 13 = Z_to_bv 64 tag
      /\ getr r 15 = mmM8 /\ getr r 16 = mmSEED /\ getr r 10 = mmM /\ getr r 8 = Z_to_bv 64 0
      /\ regs_agree CLX regs r.
  Proof using H11 H10 H2 H1 Hcells Htr Hstk Hsp Rm Rseed Rm8 Htag Hsz ws G148 G132 G128 A4 HC g_m g_seed g_m8.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range tr) as Htrr. cells_split. destruct Hsz as [Hlen Hsz'].
    destruct A4 as [xa GA]. destruct G128 as [x1 [GA1 GL1]]. destruct G132 as [x2 [GA2 GL2]]. destruct G148 as [x3 [GA3 GL3]].
    wd_eexists. split.
    - an X0' D_8f4f0.                                    (* [comment removed for export] *)
      eapply msteps_trans; [apply GA|]; zlit_at. rewrite regupd_regupd_same.   (* [comment removed for export] *)
      an Xf9034 D_8f4fc.                                 (* [comment removed for export] *)
      an Xf9038 D_8f500.                                 (* [comment removed for export] *)
      an Xf903c D_8f504.                                 (* [comment removed for export] *)
      an Xf9040 D_8f508.                                 (* [comment removed for export] *)
      an Xf9044 D_8f50c.                                 (* [comment removed for export] *)
      an Xf9048 D_8f510.                                 (* [comment removed for export] *)
      fsd Xf904c D_8f514 (at_ sp (-8)).
      fsd Xf9050 D_8f518 (at_ sp (-16)).
      fsd Xf9054 D_8f51c (at_ sp (-24)).
      fsd Xf9058 D_8f520 (at_ sp (-32)).
      fsd Xf905c D_8f524 (at_ sp (-40)).
      fsd Xf9060 D_8f528 (at_ sp (-48)).
      fsd Xf9064 D_8f52c (at_ sp (-56)).
      fsd Xf9068 D_8f530 (at_ sp (-64)).
      fsd Xf906c D_8f534 (at_ sp (-72)).
      fsd Xf9070 D_8f538 (at_ sp (-80)).
      fsd Xf9074 D_8f53c (at_ sp (-88)).
      an Xf9078 D_8f540.                                 (* [comment removed for export] *)
      an Xf907c D_8f544.                                 (* [comment removed for export] *)
      fsd Xf9080 D_8f548 (at_ sp (-104)).                (* [comment removed for export] *)
      fsd Xf9084 D_8f54c (at_ sp (-96)).                 (* [comment removed for export] *)
      change (wbytes _ _ _) with SM1.
      ab_tk Xf9088 D_8f550 ltac:(condz).               (* [comment removed for export] *)
      av Xf9090 D_8f558 (Z_to_bv 64 sz) ltac:(apply sextw_sz).   (* [comment removed for export] *)
      an Xf9094 D_8f55c.                                 (* [comment removed for export] *)
      ab_ft Xf9098 D_8f560 ltac:(condz).               (* [comment removed for export] *)
      ab_ft Xf909c D_8f564 ltac:(condz).               (* [comment removed for export] *)
      av Xf90a0 D_8f568 (Z_to_bv 64 tag) ltac:(apply srli32_tag).   (* [comment removed for export] *)
      an Xf90a4 D_8f56c.                                 (* [comment removed for export] *)
      eapply msteps_trans; [apply GA1|]; zlit_at.        (* [comment removed for export] *)
      eapply msteps_trans; [apply GA2|]; zlit_at.        (* [comment removed for export] *)
      an Xf90b0 D_8f578.                                 (* [comment removed for export] *)
      eapply msteps_trans; [ eapply GL2; [gres; reflexivity | apply rd_o2; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia | exact Rm8]] | ]; zlit_at.  (* [comment removed for export] *)
      an Xf90b8 D_8f580.                                 (* [comment removed for export] *)
      first [ rewrite and32_sz
            | match goal with |- context [v_and a1w ?m] => replace (v_and a1w m) with (Z_to_bv 64 sz) by (symmetry; etransitivity; [|apply and32_sz]; f_equal; apply bv_eq; reflexivity) end ].
      eapply msteps_trans; [apply GA3|]; zlit_at.        (* [comment removed for export] *)
      eapply msteps_trans; [ eapply GL3; [gres; reflexivity | apply rd_o2; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia | exact Rseed]] | ]; zlit_at.  (* [comment removed for export] *)
      eapply msteps_trans; [ eapply GL1; [gres; reflexivity | apply rd_o2; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia | exact Rm]] | ]; zlit_at.      (* [comment removed for export] *)
      wd_refl.
    - post; rewrite ?at_0; try reflexivity. (lazymatch goal with |- ?G => let G' := eval unfold sd_clobx in G in change_no_check G' end). ra_solve.
  Qed.

  #[local] Abbreviation SM := SM1.
  Ltac cld2 F D vv Hr :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D | addr_n; rewrite ?at_add_0_r, ?Z.add_0_r; Hr | apply bytes_le_to_Z_8]
      | step_simpl]; vn.
  Ltac clw2 F D z Hr :=
    chain_step; [reflexivity
      | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 z)) (v := Z_to_bv 64 z);
        [exact F | reflexivity | exact D | addr_n; rewrite ?at_add_0_r, ?Z.add_0_r; Hr | apply bytes4_small; lia]
      | step_simpl]; rewrite (v_lw_small z) by lia; vn.

  (* [comment removed for export] *)
  Lemma D2loop : forall (k : nat) r0 (i : nat) (h : word),
    (i + S k = length ws)%nat ->
    getr r0 11 = at_ tr (8 * Z.of_nat i) -> getr r0 14 = at_ tr (8 * sz) -> getr r0 12 = h -> getr r0 10 = mmM ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 176) SM rom) (mkst r (at_ base 212) SM rom)
      /\ getr r 12 = mm_fold h (skipn i ws) /\ getr r 11 = at_ tr (8 * sz) /\ getr r 10 = mmM
      /\ (forall x : reg, In x [2; 8; 9; 13] -> getr r x = getr r0 x)
      /\ regs_agree CLX regs r.
  Proof using Htr Hsp Rws Hsz HC.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range tr) as Htrr. destruct Hsz as [Hlen Hsz'].
    induction k as [|k IH]; intros r0 i h Hi R11 R14 R12 R10 AG0.
    - (* [comment removed for export] *)
      assert (Hw : rdn segs SM (at_ tr (8 * Z.of_nat i)) 8 = Some (LE8 (nth i ws (Z_to_bv 64 0)))).
      { apply rd_o2; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | apply Rws; lia]. }
      wd_eexists. split.
      + cld2 Xf90d8 D_8f5a0 (nth i ws (Z_to_bv 64 0)) ltac:(exact Hw).   (* [comment removed for export] *)
        an Xf90dc D_8f5a4.                               (* [comment removed for export] *)
        an Xf90e0 D_8f5a8. an Xf90e4 D_8f5ac. an Xf90e8 D_8f5b0. an Xf90ec D_8f5b4. an Xf90f0 D_8f5b8. an Xf90f4 D_8f5bc.
        ab_ft Xf90f8 D_8f5c0 ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, bv_eqb in G in change_no_check G' end); apply Z.eqb_eq; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ]).   (* [comment removed for export] *)
        wd_refl.
      + post.
        * rewrite (skipn_nth_cons ws i (Z_to_bv 64 0)) by lia. rewrite skipn_nil_len by lia. reflexivity.
        * intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]); destruct Hx.
        * (lazymatch goal with |- ?G => let G' := eval unfold sd_clobx in G in change_no_check G' end). ra_chain.
    - assert (Hw : rdn segs SM (at_ tr (8 * Z.of_nat i)) 8 = Some (LE8 (nth i ws (Z_to_bv 64 0)))).
      { apply rd_o2; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | apply Rws; lia]. }
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 176) SM rom)
               (fun r => getr r 11 = at_ tr (8 * Z.of_nat (S i)) /\ getr r 14 = at_ tr (8 * sz) /\ getr r 12 = mm_add h (nth i ws (Z_to_bv 64 0)) /\ getr r 10 = mmM
                         /\ (forall x : reg, In x [2; 8; 9; 13] -> getr r x = getr r0 x) /\ regs_agree CLX regs r)).
      + wd_eexists. split.
        * cld2 Xf90d8 D_8f5a0 (nth i ws (Z_to_bv 64 0)) ltac:(exact Hw).
          an Xf90dc D_8f5a4.
          an Xf90e0 D_8f5a8. an Xf90e4 D_8f5ac. an Xf90e8 D_8f5b0. an Xf90ec D_8f5b4. an Xf90f0 D_8f5b8. an Xf90f4 D_8f5bc.
          ab_tk Xf90f8 D_8f5c0 ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, bv_eqb in G in change_no_check G' end); apply Z.eqb_neq; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ]).   (* [comment removed for export] *)
          wd_refl.
        * post.
          all: lazymatch goal with
               | |- regs_agree _ _ _ => (lazymatch goal with |- ?G => let G' := eval unfold sd_clobx in G in change_no_check G' end); ra_chain
               | |- forall x : reg, In x _ -> _ => intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]); destruct Hx
               | |- _ => rewrite ?at_addi; f_equal; lia
               end.
      + cbv beta. intros r1 (Q11 & Q14 & Q12 & Q10 & QK & QAG).
        destruct (IH r1 (S i) _ ltac:(lia) Q11 Q14 Q12 Q10 QAG) as (r2 & RUN & P12 & P11 & P10 & PK & PAG).
        exists r2. split; [exact RUN|]. split; [| split; [exact P11 | split; [exact P10 | split; [| exact PAG]]]].
        * rewrite P12. rewrite (skipn_nth_cons ws i (Z_to_bv 64 0)) by lia. reflexivity.
        * intros x Hx. rewrite (PK x Hx). apply QK. exact Hx.
  Qed.

  #[local] Abbreviation BIX := (sd_bix HSH).
  #[local] Abbreviation MAP1 := (Z_to_bv 64 (U D + 4194320)).

  (* [comment removed for export] *)
  Lemma D2 : forall r0,
    getr r0 9 = D -> getr r0 11 = tr -> getr r0 12 = Z_to_bv 64 sz -> getr r0 13 = Z_to_bv 64 tag ->
    getr r0 15 = mmM8 -> getr r0 16 = mmSEED -> getr r0 10 = mmM ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 160) SM rom) (mkst r (at_ base 320) SM rom)
      /\ getr r 11 = Z_to_bv 64 (tabf BIX) /\ getr r 19 = HSH /\ getr r 24 = MAP1 /\ getr r 22 = Z_to_bv 64 65535
      /\ getr r 18 = Z_to_bv 64 (U D + 4 * BIX) /\ getr r 25 = Z_to_bv 64 (tabf BIX) /\ getr r 23 = Z_to_bv 64 2147483647
      /\ getr r 20 = Z_to_bv 64 (U D + 4194312) /\ getr r 8 = getr r0 8
      /\ (forall x : reg, In x [2; 9] -> getr r x = getr r0 x)
      /\ regs_agree CLX regs r.
  Proof using HC HD32 Hcells Hnids Hsp Hsz Htag Htr Rtab Rws.
    intros r0 R9 R11 R12 R13 R15 R16 R10 AG0.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range tr) as Htrr. pose proof (u64_range D) as HDr. pose proof (bix_range HSH) as Hbix.
    destruct Hsz as [Hlen Hsz']. destruct (Rtab BIX Hbix) as [Rbucket Hbw].
    cells_split.
    (* [comment removed for export] *)
    assert (W1 : exists r1, msteps segs (mkst r0 (at_ base 160) SM rom) (mkst r1 (at_ base 176) SM rom)
                 /\ getr r1 11 = at_ tr (8 * Z.of_nat 0) /\ getr r1 14 = at_ tr (8 * sz) /\ getr r1 12 = sd_h0 sz /\ getr r1 10 = mmM
                 /\ getr r1 13 = Z_to_bv 64 tag /\ getr r1 8 = getr r0 8 /\ (forall x : reg, In x [2; 9] -> getr r1 x = getr r0 x) /\ regs_agree CLX regs r1).
    { wd_eexists. split.
      { an Xf90c8 D_8f590.                                (* [comment removed for export] *)
        av Xf90cc D_8f594 (Z_to_bv 64 (8 * sz)) ltac:(rewrite v_slli_mul by lia; unorm; f_equal; lia).   (* [comment removed for export] *)
        an Xf90d0 D_8f598.                                (* [comment removed for export] *)
        av Xf90d4 D_8f59c (at_ tr (8 * sz)) ltac:(apply v_add_at; lia).   (* [comment removed for export] *)
        wd_refl. }
      post. all: try (rewrite Z.mul_0_r, at_0; reflexivity).
      all: lazymatch goal with
           | |- regs_agree _ _ _ => (lazymatch goal with |- ?G => let G' := eval unfold sd_clobx in G in change_no_check G' end); ra_chain
           | |- forall x : reg, In x _ -> _ => intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]); destruct Hx
           | |- _ => try reflexivity
           end. }
    destruct W1 as (r1 & RUN1 & A11 & A14 & A12 & A10 & A13 & A8 & AK & AG1).
    destruct (D2loop (length ws - 1) r1 0 (sd_h0 sz) ltac:(lia) A11 A14 A12 A10 AG1) as (r2 & RUN2 & B12 & B11 & B10 & BK & AG2).
    cbn [skipn] in B12.
    assert (B13 : getr r2 13 = Z_to_bv 64 tag) by (rewrite (BK 13) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact A13).
    assert (B9 : getr r2 9 = D) by (rewrite (BK 9) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); rewrite (AK 9) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact R9).
    (* [comment removed for export] *)
    assert (EH : sd_fin (mm_fold (sd_h0 sz) ws) tag = HSH) by ((lazymatch goal with |- ?G => let G' := eval unfold sd_hashN in G in change_no_check G' end); rewrite Hlen; reflexivity).
    eapply (runs_trans segs _ (fun r => mkst r (at_ base 212) SM rom) (fun r => r = r2)); [exists r2; split; [|reflexivity]; eapply msteps_trans; [exact RUN1 | exact RUN2] |].
    intros r2' ->.
    wd_eexists. split.
    - an Xf90fc D_8f5c4. an Xf9100 D_8f5c8.           (* [comment removed for export] *)
      an Xf9104 D_8f5cc.                                 (* [comment removed for export] *)
      an Xf9108 D_8f5d0.                                 (* [comment removed for export] *)
      an Xf910c D_8f5d4. an Xf9110 D_8f5d8.           (* [comment removed for export] *)
      an Xf9114 D_8f5dc. an Xf9118 D_8f5e0. an Xf911c D_8f5e4.   (* [comment removed for export] *)
      an Xf9120 D_8f5e8. an Xf9124 D_8f5ec.           (* [comment removed for export] *)
      an Xf9128 D_8f5f0. an Xf912c D_8f5f4. an Xf9130 D_8f5f8.   (* [comment removed for export] *)
      an Xf9134 D_8f5fc. an Xf9138 D_8f600.           (* [comment removed for export] *)
      match goal with |- context [regupd _ 19 ?hv] => replace hv with HSH by (rewrite <- EH; reflexivity) end.
      an Xf913c D_8f604.                                 (* [comment removed for export] *)
      av Xf9140 D_8f608 (Z_to_bv 64 (4 * BIX)) ltac:(apply bix_shift).   (* [comment removed for export] *)
      av Xf9144 D_8f60c (Z_to_bv 64 (U D + 4 * BIX)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
      clw Xf9148 D_8f610 (tabf BIX) Rbucket.            (* [comment removed for export] *)
      an Xf914c D_8f614.                                 (* [comment removed for export] *)
      av Xf9150 D_8f618 (Z_to_bv 64 (U D + 4194320)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); imm_norm; unorm; reflexivity).   (* [comment removed for export] *)
      afence Xf9154 D_8f61c.                             (* [comment removed for export] *)
      an Xf9158 D_8f620. rewrite v_and_bw31 by lia.       (* [comment removed for export] *)
      an Xf915c D_8f624.                                 (* [comment removed for export] *)
      av Xf9160 D_8f628 (Z_to_bv 64 (U D + 4194312)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); imm_norm; unorm; reflexivity).   (* [comment removed for export] *)
      an Xf9164 D_8f62c.                                 (* [comment removed for export] *)
      wd_refl.
    - post.
      all: lazymatch goal with
           | |- regs_agree _ _ _ => (lazymatch goal with |- ?G => let G' := eval unfold sd_clobx in G in change_no_check G' end); ra_chain
           | |- forall x : reg, In x _ -> _ => intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; rewrite (BK _) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); apply AK; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]|]); destruct Hx
           | |- _ => idtac
           end.
      + rewrite (BK 8) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]). exact A8.
  Qed.

  (* [comment removed for export] *)
  Lemma rdS : forall (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19); (-48, getr regs 20);
               (-56, getr regs 21); (-64, getr regs 22); (-72, getr regs 23); (-80, getr regs 24); (-88, getr regs 25)]%Z ->
    rdn segs SM (at_ sp k) 8 = Some (LE8 v).
  Proof using Hsp ws.
    intros k v Hin. pose proof (u64_range sp).
    (lazymatch goal with |- ?G => let G' := eval unfold SM1, sd_frame in G in change_no_check G' end). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
  Qed.

  (* [comment removed for export] *)
  Lemma D3 : forall r0,
    getr r0 2 = at_ sp (-112) -> regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 580) SM rom) (mkst r ra SM rom)
      /\ getr r 10 = getr r0 10 /\ regs_agree CL regs r.
  Proof using H1 H10 H11 H2 HC Hnids Hret Hsp Hsz Htag Htr.
    intros r0 R2 AG0. pose proof (u64_range sp) as Hspr.
    Ltac fldM F D vv :=
      chain_step; [reflexivity
        | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
          [exact F | reflexivity | exact D
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; apply rdS; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]
          | apply bytes_le_to_Z_8]
        | step_simpl]; vn.
    wd_eexists. split; [|split].
    - fldM Xf926c D_8f734 ra.
      fldM Xf9270 D_8f738 (getr regs 8).
      fldM Xf9274 D_8f73c (getr regs 9).
      fldM Xf9278 D_8f740 (getr regs 18).
      fldM Xf927c D_8f744 (getr regs 19).
      fldM Xf9280 D_8f748 (getr regs 20).
      fldM Xf9284 D_8f74c (getr regs 21).
      fldM Xf9288 D_8f750 (getr regs 22).
      fldM Xf928c D_8f754 (getr regs 23).
      fldM Xf9290 D_8f758 (getr regs 24).
      fldM Xf9294 D_8f75c (getr regs 25).
      an Xf9298 D_8f760.                                 (* [comment removed for export] *)
      aret Xf929c D_8f764 ra.                            (* [comment removed for export] *)
      wd_refl.
    - gres. reflexivity.
    - apply (regs_agree_strengthen sd_clob sd_clobx regs).
      + (lazymatch goal with |- ?G => let G' := eval unfold sd_clobx in G in change_no_check G' end). ra_solve.
      + intros i Hi Hni. cbn [sd_clobx In] in Hi.
        repeat (destruct Hi as [<-|Hi]; [gres; rwH; rewrite ?at_addi, ?at_0; first [reflexivity | symmetry; assumption | f_equal; lia | exfalso; apply Hni; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]] |]).
        destruct Hi.
  Qed.

  (* [comment removed for export] *)
  Lemma D2chain : forall (n : nat) r0 (cur : Z),
    (Z.to_nat cur < n)%nat -> (0 <= cur <= NIDS)%Z ->
    getr r0 11 = Z_to_bv 64 cur -> getr r0 19 = HSH -> getr r0 24 = MAP1 -> getr r0 22 = Z_to_bv 64 65535 ->
    regs_agree CLX regs r0 ->
    (exists r id, msteps segs (mkst r0 (at_ base 320) SM rom) (mkst r (at_ base 580) SM rom)
        /\ getr r 10 = Z_to_bv 64 id /\ (1 <= id <= NIDS)%Z /\ hashf id = HSH
        /\ (forall x : reg, In x [2; 8; 9; 18; 19; 20; 21; 23; 24; 25] -> getr r x = getr r0 x) /\ regs_agree CLX regs r)
    \/ (exists r, msteps segs (mkst r0 (at_ base 320) SM rom) (mkst r (at_ base 408) SM rom)
        /\ getr r 11 = Z_to_bv 64 0
        /\ (forall x : reg, In x [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25] -> getr r x = getr r0 x) /\ regs_agree CLX regs r).
  Proof using HC HD HD32 Hblk Hnids Hsp Hsz Htag Htr Rmap Rnode.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range D) as HDr.
    induction n as [|n IH]; intros r0 cur Hn Hcur R11 R19 R24 R22 AG0; [lia|].
    destruct (Z.eq_dec cur 0) as [-> | NZ].
    { right. wd_eexists. split.
      - ab_tk Xf9168 D_8f630 ltac:(condz).              (* [comment removed for export] *)
        wd_refl.
      - post.
        all: first [ exact AG0 | (lazymatch goal with |- ?G => let G' := eval unfold sd_clobx in G in change_no_check G' end); ra_chain
                   | intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]); destruct Hx ]. }
    destruct (id16 cur Hcur) as (I1 & I2 & I3).
    destruct (Rmap (cur / 2 ^ 16) ltac:(lia)) as (Rblk & BNZ & BRNG). pose proof (Hblk (cur / 2 ^ 16) ltac:(lia)) as BPL.
    destruct (Rnode cur ltac:(lia)) as (Rh & Rl & Hl).
    set (blk := blkf (cur / 2 ^ 16)) in *. pose proof (u64_range blk) as Hblkr.
    assert (Rblk' : rdn segs SM (Z_to_bv 64 (U D + 4194320 + 8 * (cur / 2 ^ 16))) 8 = Some (LE8 blk)).
    { apply rd_o2; [wd_ulia_c | wd_ulia_c | exact Rblk]. }
    assert (Rh' : rdn segs SM (nd cur) 8 = Some (LE8 (hashf cur))).
    { apply rd_o2; [(lazymatch goal with |- ?G => let G' := eval unfold nd in G in change_no_check G' end); fold blk; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | (lazymatch goal with |- ?G => let G' := eval unfold nd in G in change_no_check G' end); fold blk; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Rh]. }
    assert (Rl' : rdn segs SM (at_ (nd cur) 8) 4 = Some (LE4 (linkf cur))).
    { apply rd_o2; [(lazymatch goal with |- ?G => let G' := eval unfold nd in G in change_no_check G' end); fold blk; rewrite at_at, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval unfold nd in G in change_no_check G' end); fold blk; rewrite at_at, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rl]. }
    (* [comment removed for export] *)
    assert (W : exists r1, msteps segs (mkst r0 (at_ base 320) SM rom) (mkst r1 (at_ base 376) SM rom)
                 /\ getr r1 10 = Z_to_bv 64 cur /\ getr r1 12 = hashf cur /\ getr r1 11 = Z_to_bv 64 (linkf cur)
                 /\ getr r1 19 = HSH /\ getr r1 24 = MAP1 /\ getr r1 22 = Z_to_bv 64 65535
                 /\ (forall x : reg, In x [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25] -> getr r1 x = getr r0 x) /\ regs_agree CLX regs r1).
    { wd_eexists. split.
      { ab_ft Xf9168 D_8f630 ltac:(condz).              (* [comment removed for export] *)
        an Xf916c D_8f634.                               (* [comment removed for export] *)
        an Xf9170 D_8f638. rewrite v_srliw_bw by lia.     (* [comment removed for export] *)
        av Xf9174 D_8f63c (Z_to_bv 64 (8 * (cur / 2 ^ 16))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); rewrite Z.shiftl_mul_pow2 by lia; unorm; f_equal; lia).  (* [comment removed for export] *)
        av Xf9178 D_8f640 (Z_to_bv 64 (U D + 4194320 + 8 * (cur / 2 ^ 16))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
        cld2 Xf917c D_8f644 blk ltac:(exact Rblk').        (* [comment removed for export] *)
        ab_ft Xf9180 D_8f648 ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, bv_eqb in G in change_no_check G' end); apply Z.eqb_neq; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); fold blk; exact BNZ || (unorm; exact BNZ)).   (* [comment removed for export] *)
        av Xf9184 D_8f64c (Z_to_bv 64 (cur * 2 ^ 32)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); rewrite Z.shiftl_mul_pow2 by lia; unorm; reflexivity).  (* [comment removed for export] *)
        av Xf9188 D_8f650 (Z_to_bv 64 cur) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; unorm; rewrite Z.div_mul by lia; reflexivity).  (* [comment removed for export] *)
        an Xf918c D_8f654. rewrite (v_and_bw16 cur (Z_to_bv 64 cur)) by (lia || (unorm; reflexivity)).   (* [comment removed for export] *)
        av Xf9190 D_8f658 (Z_to_bv 64 (16 * (cur mod 2 ^ 16))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); rewrite Z.shiftl_mul_pow2 by lia; unorm; f_equal; lia).  (* [comment removed for export] *)
        av Xf9194 D_8f65c (nd cur) ltac:((lazymatch goal with |- ?G => let G' := eval unfold nd in G in change_no_check G' end); fold blk; apply v_add_at; lia).   (* [comment removed for export] *)
        cld2 Xf9198 D_8f660 (hashf cur) ltac:(exact Rh').   (* [comment removed for export] *)
        clw2 Xf919c D_8f664 (linkf cur) ltac:(exact Rl').  (* [comment removed for export] *)
        wd_refl. }
      post.
      all: lazymatch goal with
           | |- regs_agree _ _ _ => (lazymatch goal with |- ?G => let G' := eval unfold sd_clobx in G in change_no_check G' end); ra_chain
           | |- forall x : reg, In x _ -> _ => intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]); destruct Hx
           | |- _ => idtac
           end. }
    destruct W as (r1 & RUN1 & A10 & A12 & A11 & A19 & A24 & A22 & AK & AG1).
    destruct (decide (hashf cur = HSH)) as [EQ | NE].
    - (* [comment removed for export] *)
      left. exists r1, cur. 
      assert (W2 : msteps segs (mkst r1 (at_ base 376) SM rom) (mkst r1 (at_ base 580) SM rom)).
      { ab_ft Xf91a0 D_8f668 ltac:(rwH; rewrite EQ; (lazymatch goal with |- ?G => let G' := eval unfold c_eq in G in change_no_check G' end); rewrite bv_eqb_refl; reflexivity).   (* [comment removed for export] *)
        an Xf91a4 D_8f66c.                               (* [comment removed for export] *)
        wd_refl. }
      all: try (split; [eapply msteps_trans; [exact RUN1 | exact W2] |]; split; [exact A10|]; split; [lia|]; split; [exact EQ|]; split; [| exact AG1];
                intros x Hx; apply AK; cbn [In] in Hx |- *; clear - Hx; tauto).
    - (* [comment removed for export] *)
      assert (W2 : msteps segs (mkst r1 (at_ base 376) SM rom) (mkst r1 (at_ base 320) SM rom)).
      { ab_tk Xf91a0 D_8f668 ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, bv_eqb in G in change_no_check G' end); apply Z.eqb_neq; intros E; apply NE; apply bv_eq; lia).   (* [comment removed for export] *)
        wd_refl. }
      destruct (IH r1 (linkf cur) ltac:(lia) ltac:(lia) A11 A19 A24 A22 AG1) as [(r & id & RUN & P10 & Pid & PH & PK & PAG) | (r & RUN & P11 & PK & PAG)].
      + left. exists r, id. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact W2 | exact RUN] |].
        split; [exact P10|]. split; [exact Pid|]. split; [exact PH|]. split; [| exact PAG].
        intros x Hx. rewrite (PK x Hx). apply AK. cbn [In] in Hx |- *; clear - Hx; tauto.
      + right. exists r. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact W2 | exact RUN] |].
        split; [exact P11|]. split; [| exact PAG].
        intros x Hx. rewrite (PK x Hx). apply AK. exact Hx.
  Qed.

  (* [comment removed for export] *)
  Theorem sd_probe :
    (exists r id,
        msteps segs (mkst regs base mem rom) (mkst r ra SM rom)
        /\ getr r 10 = Z_to_bv 64 id /\ (1 <= id <= NIDS)%Z /\ hashf id = HSH
        /\ regs_agree CL regs r)
    \/ (exists r,
        msteps segs (mkst regs base mem rom) (mkst r (at_ base 408) SM rom)
        /\ getr r 2 = at_ sp (-112) /\ getr r 8 = Z_to_bv 64 0 /\ getr r 9 = D /\ getr r 11 = Z_to_bv 64 0
        /\ getr r 18 = Z_to_bv 64 (U D + 4 * BIX) /\ getr r 19 = HSH /\ getr r 20 = Z_to_bv 64 (U D + 4194312)
        /\ getr r 22 = Z_to_bv 64 65535 /\ getr r 23 = Z_to_bv 64 2147483647 /\ getr r 24 = MAP1 /\ getr r 25 = Z_to_bv 64 (tabf BIX)
        /\ regs_agree CLX regs r).
  Proof using A4 G128 G132 G148 H1 H10 H11 H2 HC HD HD32 Hblk Hcells Hnids Hret Hsp Hstk Hsz Htag Htr Rm Rm8 Rmap Rnode Rseed Rtab Rws.
    pose proof (bix_range HSH) as Hbix. destruct (Rtab BIX Hbix) as [_ Hbw].
    destruct D1 as (r1 & M1 & A2 & A9 & A11 & A12 & A13 & A15 & A16 & A10 & A8 & AG1).
    destruct (D2 r1 A9 A11 A12 A13 A15 A16 A10 AG1) as (r2 & M2 & B11 & B19 & B24 & B22 & B18 & B25 & B23 & B20 & B8 & BK & AG2).
    destruct (D2chain (S (Z.to_nat (tabf BIX))) r2 (tabf BIX) ltac:(lia) ltac:(lia) B11 B19 B24 B22 AG2)
      as [(r3 & id & M3 & C10 & Cid & CH & CK & AG3) | (r3 & M3 & C11 & CK & AG3)].
    - left.
      destruct (D3 r3 ltac:(rewrite (CK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); rewrite (BK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact A2) AG3) as (r4 & M4 & E10 & AG4).
      exists r4, id. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact M2|]; eapply msteps_trans; [exact M3 | exact M4] |].
      split; [rewrite E10; exact C10|]. split; [exact Cid|]. split; [exact CH | exact AG4].
    - right. exists r3. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact M2 | exact M3] |].

      split; [rewrite (CK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); rewrite (BK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact A2|].
      split; [rewrite (CK 8) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); rewrite B8; exact A8|].
      split; [rewrite (CK 9) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); rewrite (BK 9) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact A9|].
      split; [exact C11|].
      split; [rewrite (CK 18) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact B18|]. split; [rewrite (CK 19) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact B19|]. split; [rewrite (CK 20) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact B20|]. split; [rewrite (CK 22) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact B22|].
      split; [rewrite (CK 23) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact B23|]. split; [rewrite (CK 24) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact B24|]. split; [rewrite (CK 25) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact B25|]. exact AG3.
  Qed.
  End WithRegs.
End DEPOT.
End FPGen1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
#[local] Unset Lia Cache.
Section FPGen2.
Context {fx : FPState}.
#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Definition both_sd_tab : sd_tab := SDT (Z_to_bv 64 0x8f4f0) (Z_to_bv 64 0x1f0098) 0x10348 0x10448 0x10310.

Lemma both_sd_tab_ok : sd_tab_ok BSEGS both_sd_tab.
Proof using.
  split; (lazymatch goal with |- ?G => let G' := eval cbn [st_base st_depot st_g_m8 st_g_seed st_g_m both_sd_tab] in G in change_no_check G' end).
  - (lazymatch goal with |- ?G => let G' := eval unfold sdput_words in G in change_no_check G' end). code_ato_vm.
  - gaddr2_tac F_8f4f4 D_8f4f4 F_8f4f8 D_8f4f8.
  - gauipc_ld_tac F_8f570 D_8f570 F_8f58c D_8f58c.
  - gauipc_ld_tac F_8f574 D_8f574 F_8f57c D_8f57c.
  - gauipc_ld_tac F_8f584 D_8f584 F_8f588 D_8f588.
  - vm_compute. exact eq_refl.
Qed.

End FPGen2.
