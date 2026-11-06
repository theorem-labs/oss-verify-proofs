(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.InstrEnc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Bo_code_fbe98_fc490.
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
Definition W_fbe98 : bv 32 := @BV 32 0x0ff5f593%Z I.
Lemma F_fbe98 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbe8c%Z I : word) = Some W_fbe98.
Proof. vm_refl. Qed.
Lemma D_fbe98 : decode_any W_fbe98 = Some (OpImm ALU_AND (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 255%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbe9c : bv 32 := @BV 32 0x00757693%Z I.
Lemma F_fbe9c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbe90%Z I : word) = Some W_fbe9c.
Proof. vm_refl. Qed.
Lemma D_fbe9c : decode_any W_fbe9c = Some (OpImm ALU_AND (@BV 5 13%Z I) (@BV 5 10%Z I) (@BV 12 7%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbea0 : bv 32 := @BV 32 0x00c03733%Z I.
Lemma F_fbea0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbe94%Z I : word) = Some W_fbea0.
Proof. vm_refl. Qed.
Lemma D_fbea0 : decode_any W_fbea0 = Some (Op ALU_SLTU (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbea4 : bv 32 := @BV 32 0x02068c63%Z I.
Lemma F_fbea4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbe98%Z I : word) = Some W_fbea4.
Proof. vm_refl. Qed.
Lemma D_fbea4 : decode_any W_fbea4 = Some (Branch BC_EQ (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 13 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbea8 : bv 32 := @BV 32 0x02060a63%Z I.
Lemma F_fbea8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbe9c%Z I : word) = Some W_fbea8.
Proof. vm_refl. Qed.
Lemma D_fbea8 : decode_any W_fbea8 = Some (Branch BC_EQ (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 13 52%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbeac : bv 32 := @BV 32 0x00150793%Z I.
Lemma F_fbeac : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbea0%Z I : word) = Some W_fbeac.
Proof. vm_refl. Qed.
Lemma D_fbeac : decode_any W_fbeac = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 10%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbeb0 : bv 32 := @BV 32 0x00100813%Z I.
Lemma F_fbeb0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbea4%Z I : word) = Some W_fbeb0.
Proof. vm_refl. Qed.
Lemma D_fbeb0 : decode_any W_fbeb0 = Some (OpImm ALU_ADD (@BV 5 16%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbeb4 : bv 32 := @BV 32 0x00054703%Z I.
Lemma F_fbeb4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbea8%Z I : word) = Some W_fbeb4.
Proof. vm_refl. Qed.
Lemma D_fbeb4 : decode_any W_fbeb4 = Some (Load SZ1 false (@BV 5 14%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbeb8 : bv 32 := @BV 32 0x00060693%Z I.
Lemma F_fbeb8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbeac%Z I : word) = Some W_fbeb8.
Proof. vm_refl. Qed.
Lemma D_fbeb8 : decode_any W_fbeb8 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbebc : bv 32 := @BV 32 0x06b70e63%Z I.
Lemma F_fbebc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbeb0%Z I : word) = Some W_fbebc.
Proof. vm_refl. Qed.
Lemma D_fbebc : decode_any W_fbebc = Some (Branch BC_EQ (@BV 5 14%Z I) (@BV 5 11%Z I) (@BV 13 124%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbec0 : bv 32 := @BV 32 0x00150513%Z I.
Lemma F_fbec0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbeb4%Z I : word) = Some W_fbec0.
Proof. vm_refl. Qed.
Lemma D_fbec0 : decode_any W_fbec0 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbec4 : bv 32 := @BV 32 0xfff68613%Z I.
Lemma F_fbec4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbeb8%Z I : word) = Some W_fbec4.
Proof. vm_refl. Qed.
Lemma D_fbec4 : decode_any W_fbec4 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 13%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbec8 : bv 32 := @BV 32 0x0077f893%Z I.
Lemma F_fbec8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbebc%Z I : word) = Some W_fbec8.
Proof. vm_refl. Qed.
Lemma D_fbec8 : decode_any W_fbec8 = Some (OpImm ALU_AND (@BV 5 17%Z I) (@BV 5 15%Z I) (@BV 12 7%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbecc : bv 32 := @BV 32 0x00c03733%Z I.
Lemma F_fbecc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbec0%Z I : word) = Some W_fbecc.
Proof. vm_refl. Qed.
Lemma D_fbecc : decode_any W_fbecc = Some (Op ALU_SLTU (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbed0 : bv 32 := @BV 32 0x00088663%Z I.
Lemma F_fbed0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbec4%Z I : word) = Some W_fbed0.
Proof. vm_refl. Qed.
Lemma D_fbed0 : decode_any W_fbed0 = Some (Branch BC_EQ (@BV 5 17%Z I) (@BV 5 0%Z I) (@BV 13 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbed4 : bv 32 := @BV 32 0x00178793%Z I.
Lemma F_fbed4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbec8%Z I : word) = Some W_fbed4.
Proof. vm_refl. Qed.
Lemma D_fbed4 : decode_any W_fbed4 = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 15%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbed8 : bv 32 := @BV 32 0xfd069ee3%Z I.
Lemma F_fbed8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbecc%Z I : word) = Some W_fbed8.
Proof. vm_refl. Qed.
Lemma D_fbed8 : decode_any W_fbed8 = Some (Branch BC_NE (@BV 5 13%Z I) (@BV 5 16%Z I) (@BV 13 8156%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbedc : bv 32 := @BV 32 0x06070863%Z I.
Lemma F_fbedc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbed0%Z I : word) = Some W_fbedc.
Proof. vm_refl. Qed.
Lemma D_fbedc : decode_any W_fbedc = Some (Branch BC_EQ (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 13 112%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbee0 : bv 32 := @BV 32 0x00054683%Z I.
Lemma F_fbee0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbed4%Z I : word) = Some W_fbee0.
Proof. vm_refl. Qed.
Lemma D_fbee0 : decode_any W_fbee0 = Some (Load SZ1 false (@BV 5 13%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbee4 : bv 32 := @BV 32 0x04b68663%Z I.
Lemma F_fbee4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbed8%Z I : word) = Some W_fbee4.
Proof. vm_refl. Qed.
Lemma D_fbee4 : decode_any W_fbee4 = Some (Branch BC_EQ (@BV 5 13%Z I) (@BV 5 11%Z I) (@BV 13 76%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbee8 : bv 32 := @BV 32 0x00800693%Z I.
Lemma F_fbee8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbedc%Z I : word) = Some W_fbee8.
Proof. vm_refl. Qed.
Lemma D_fbee8 : decode_any W_fbee8 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbeec : bv 32 := @BV 32 0x04d66263%Z I.
Lemma F_fbeec : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbee0%Z I : word) = Some W_fbeec.
Proof. vm_refl. Qed.
Lemma D_fbeec : decode_any W_fbeec = Some (Branch BC_LTU (@BV 5 12%Z I) (@BV 5 13%Z I) (@BV 13 68%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbef0 : bv 32 := @BV 32 0xfff14697%Z I.
Lemma F_fbef0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbee4%Z I : word) = Some W_fbef0.
Proof. vm_refl. Qed.
Lemma D_fbef0 : decode_any W_fbef0 = Some (Auipc (@BV 5 13%Z I) (@BV 20 1048340%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbef4 : bv 32 := @BV 32 0x51c6b683%Z I.
Lemma F_fbef4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbee8%Z I : word) = Some W_fbef4.
Proof. vm_refl. Qed.
Lemma D_fbef4 : decode_any W_fbef4 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 1308%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbef8 : bv 32 := @BV 32 0xfff14717%Z I.
Lemma F_fbef8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbeec%Z I : word) = Some W_fbef8.
Proof. vm_refl. Qed.
Lemma D_fbef8 : decode_any W_fbef8 = Some (Auipc (@BV 5 14%Z I) (@BV 20 1048340%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbefc : bv 32 := @BV 32 0x4f473703%Z I.
Lemma F_fbefc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbef0%Z I : word) = Some W_fbefc.
Proof. vm_refl. Qed.
Lemma D_fbefc : decode_any W_fbefc = Some (Load SZ8 true (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 12 1268%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbf00 : bv 32 := @BV 32 0x00168793%Z I.
Lemma F_fbf00 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbef4%Z I : word) = Some W_fbf00.
Proof. vm_refl. Qed.
Lemma D_fbf00 : decode_any W_fbf00 = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 13%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbf04 : bv 32 := @BV 32 0x02f587b3%Z I.
Lemma F_fbf04 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbef8%Z I : word) = Some W_fbf04.
Proof. vm_refl. Qed.
Lemma D_fbf04 : decode_any W_fbf04 = Some (Mul M_MUL (@BV 5 15%Z I) (@BV 5 11%Z I) (@BV 5 15%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbf08 : bv 32 := @BV 32 0x00700813%Z I.
Lemma F_fbf08 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbefc%Z I : word) = Some W_fbf08.
Proof. vm_refl. Qed.
Lemma D_fbf08 : decode_any W_fbf08 = Some (OpImm ALU_ADD (@BV 5 16%Z I) (@BV 5 0%Z I) (@BV 12 7%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbf0c : bv 32 := @BV 32 0x00053883%Z I.
Lemma F_fbf0c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbf00%Z I : word) = Some W_fbf0c.
Proof. vm_refl. Qed.
Lemma D_fbf0c : decode_any W_fbf0c = Some (Load SZ8 true (@BV 5 17%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbf10 : bv 32 := @BV 32 0x00f8c8b3%Z I.
Lemma F_fbf10 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbf04%Z I : word) = Some W_fbf10.
Proof. vm_refl. Qed.
Lemma D_fbf10 : decode_any W_fbf10 = Some (Op ALU_XOR (@BV 5 17%Z I) (@BV 5 17%Z I) (@BV 5 15%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbf14 : bv 32 := @BV 32 0x411682b3%Z I.
Lemma F_fbf14 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbf08%Z I : word) = Some W_fbf14.
Proof. vm_refl. Qed.
Lemma D_fbf14 : decode_any W_fbf14 = Some (Op ALU_SUB (@BV 5 5%Z I) (@BV 5 13%Z I) (@BV 5 17%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbf18 : bv 32 := @BV 32 0x0112e8b3%Z I.
Lemma F_fbf18 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbf0c%Z I : word) = Some W_fbf18.
Proof. vm_refl. Qed.
Lemma D_fbf18 : decode_any W_fbf18 = Some (Op ALU_OR (@BV 5 17%Z I) (@BV 5 5%Z I) (@BV 5 17%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbf1c : bv 32 := @BV 32 0x00e8f8b3%Z I.
Lemma F_fbf1c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbf10%Z I : word) = Some W_fbf1c.
Proof. vm_refl. Qed.
Lemma D_fbf1c : decode_any W_fbf1c = Some (Op ALU_AND (@BV 5 17%Z I) (@BV 5 17%Z I) (@BV 5 14%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbf20 : bv 32 := @BV 32 0x02e89a63%Z I.
Lemma F_fbf20 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbf14%Z I : word) = Some W_fbf20.
Proof. vm_refl. Qed.
Lemma D_fbf20 : decode_any W_fbf20 = Some (Branch BC_NE (@BV 5 17%Z I) (@BV 5 14%Z I) (@BV 13 52%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbf24 : bv 32 := @BV 32 0xff860613%Z I.
Lemma F_fbf24 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbf18%Z I : word) = Some W_fbf24.
Proof. vm_refl. Qed.
Lemma D_fbf24 : decode_any W_fbf24 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 4088%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbf28 : bv 32 := @BV 32 0x00850513%Z I.
Lemma F_fbf28 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbf1c%Z I : word) = Some W_fbf28.
Proof. vm_refl. Qed.
Lemma D_fbf28 : decode_any W_fbf28 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbf2c : bv 32 := @BV 32 0xfec860e3%Z I.
Lemma F_fbf2c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbf20%Z I : word) = Some W_fbf2c.
Proof. vm_refl. Qed.
Lemma D_fbf2c : decode_any W_fbf2c = Some (Branch BC_LTU (@BV 5 16%Z I) (@BV 5 12%Z I) (@BV 13 8160%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbf30 : bv 32 := @BV 32 0x00060693%Z I.
Lemma F_fbf30 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbf24%Z I : word) = Some W_fbf30.
Proof. vm_refl. Qed.
Lemma D_fbf30 : decode_any W_fbf30 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbf34 : bv 32 := @BV 32 0x00060c63%Z I.
Lemma F_fbf34 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbf28%Z I : word) = Some W_fbf34.
Proof. vm_refl. Qed.
Lemma D_fbf34 : decode_any W_fbf34 = Some (Branch BC_EQ (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 13 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbf38 : bv 32 := @BV 32 0x00054603%Z I.
Lemma F_fbf38 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbf2c%Z I : word) = Some W_fbf38.
Proof. vm_refl. Qed.
Lemma D_fbf38 : decode_any W_fbf38 = Some (Load SZ1 false (@BV 5 12%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbf3c : bv 32 := @BV 32 0x00b60a63%Z I.
Lemma F_fbf3c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbf30%Z I : word) = Some W_fbf3c.
Proof. vm_refl. Qed.
Lemma D_fbf3c : decode_any W_fbf3c = Some (Branch BC_EQ (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 13 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbf40 : bv 32 := @BV 32 0xfff68693%Z I.
Lemma F_fbf40 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbf34%Z I : word) = Some W_fbf40.
Proof. vm_refl. Qed.
Lemma D_fbf40 : decode_any W_fbf40 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbf44 : bv 32 := @BV 32 0x00150513%Z I.
Lemma F_fbf44 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbf38%Z I : word) = Some W_fbf44.
Proof. vm_refl. Qed.
Lemma D_fbf44 : decode_any W_fbf44 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbf48 : bv 32 := @BV 32 0xfe0698e3%Z I.
Lemma F_fbf48 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbf3c%Z I : word) = Some W_fbf48.
Proof. vm_refl. Qed.
Lemma D_fbf48 : decode_any W_fbf48 = Some (Branch BC_NE (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 13 8176%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbf50 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_fbf50 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbf44%Z I : word) = Some W_fbf50.
Proof. vm_refl. Qed.
Lemma D_fbf50 : decode_any W_fbf50 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbf54 : bv 32 := @BV 32 0x00060693%Z I.
Lemma F_fbf54 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbf48%Z I : word) = Some W_fbf54.
Proof. vm_refl. Qed.
Lemma D_fbf54 : decode_any W_fbf54 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbf58 : bv 32 := @BV 32 0x00054603%Z I.
Lemma F_fbf58 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbf4c%Z I : word) = Some W_fbf58.
Proof. vm_refl. Qed.
Lemma D_fbf58 : decode_any W_fbf58 = Some (Load SZ1 false (@BV 5 12%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbf5c : bv 32 := @BV 32 0xfeb612e3%Z I.
Lemma F_fbf5c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbf50%Z I : word) = Some W_fbf5c.
Proof. vm_refl. Qed.
Lemma D_fbf5c : decode_any W_fbf5c = Some (Branch BC_NE (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 13 8164%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbf60 : bv 32 := @BV 32 0xff1ff06f%Z I.
Lemma F_fbf60 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xfbf54%Z I : word) = Some W_fbf60.
Proof. vm_refl. Qed.
Lemma D_fbf60 : decode_any W_fbf60 = Some (Jal (@BV 5 0%Z I) (@BV 21 2097136%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fbf94 : bv 32 := @BV 32 0x0035f693%Z I.



(* [comment removed for export] *)
Definition W_fbf98 : bv 32 := @BV 32 0x10068863%Z I.



(* [comment removed for export] *)
Definition W_fbf9c : bv 32 := @BV 32 0x02060e63%Z I.



(* [comment removed for export] *)
Definition W_fbfa0 : bv 32 := @BV 32 0x00158713%Z I.



(* [comment removed for export] *)
Definition W_fbfa4 : bv 32 := @BV 32 0x00100793%Z I.



(* [comment removed for export] *)
Definition W_fbfa8 : bv 32 := @BV 32 0x00050693%Z I.



(* [comment removed for export] *)
Definition W_fbfac : bv 32 := @BV 32 0x0005c883%Z I.



(* [comment removed for export] *)
Definition W_fbfb0 : bv 32 := @BV 32 0x00060813%Z I.



(* [comment removed for export] *)
Definition W_fbfb4 : bv 32 := @BV 32 0x00158593%Z I.



(* [comment removed for export] *)
Definition W_fbfb8 : bv 32 := @BV 32 0x00377293%Z I.



(* [comment removed for export] *)
Definition W_fbfbc : bv 32 := @BV 32 0x01168023%Z I.



(* [comment removed for export] *)
Definition W_fbfc0 : bv 32 := @BV 32 0x00168693%Z I.



(* [comment removed for export] *)
Definition W_fbfc4 : bv 32 := @BV 32 0xfff60613%Z I.



(* [comment removed for export] *)
Definition W_fbfc8 : bv 32 := @BV 32 0x00028a63%Z I.



(* [comment removed for export] *)
Definition W_fbfcc : bv 32 := @BV 32 0x00170713%Z I.



(* [comment removed for export] *)
Definition W_fbfd0 : bv 32 := @BV 32 0xfcf81ee3%Z I.



(* [comment removed for export] *)
Definition W_fbfd4 : bv 32 := @BV 32 0x0080006f%Z I.



(* [comment removed for export] *)
Definition W_fbfd8 : bv 32 := @BV 32 0x00050693%Z I.



(* [comment removed for export] *)
Definition W_fbfdc : bv 32 := @BV 32 0x0036f793%Z I.



(* [comment removed for export] *)
Definition W_fbfe0 : bv 32 := @BV 32 0x0c078a63%Z I.



(* [comment removed for export] *)
Definition W_fbfe4 : bv 32 := @BV 32 0x02000713%Z I.



(* [comment removed for export] *)
Definition W_fbfe8 : bv 32 := @BV 32 0x02e67063%Z I.



(* [comment removed for export] *)
Definition W_fbfec : bv 32 := @BV 32 0x01000713%Z I.



(* [comment removed for export] *)
Definition W_fbff0 : bv 32 := @BV 32 0x24e67863%Z I.



(* [comment removed for export] *)
Definition W_fbff4 : bv 32 := @BV 32 0x00867713%Z I.



(* [comment removed for export] *)
Definition W_fbff8 : bv 32 := @BV 32 0x2c071e63%Z I.



(* [comment removed for export] *)
Definition W_fbffc : bv 32 := @BV 32 0x00467713%Z I.



(* [comment removed for export] *)
Definition W_fc000 : bv 32 := @BV 32 0x32071463%Z I.



(* [comment removed for export] *)
Definition W_fc004 : bv 32 := @BV 32 0x3500006f%Z I.



(* [comment removed for export] *)
Definition W_fc008 : bv 32 := @BV 32 0x0005a703%Z I.



(* [comment removed for export] *)
Definition W_fc00c : bv 32 := @BV 32 0x00300813%Z I.



(* [comment removed for export] *)
Definition W_fc010 : bv 32 := @BV 32 0x11078e63%Z I.



(* [comment removed for export] *)
Definition W_fc014 : bv 32 := @BV 32 0x00200813%Z I.



(* [comment removed for export] *)
Definition W_fc018 : bv 32 := @BV 32 0x19079c63%Z I.



(* [comment removed for export] *)
Definition W_fc01c : bv 32 := @BV 32 0x00875793%Z I.



(* [comment removed for export] *)
Definition W_fc020 : bv 32 := @BV 32 0xffe60613%Z I.



(* [comment removed for export] *)
Definition W_fc024 : bv 32 := @BV 32 0x00e68023%Z I.



(* [comment removed for export] *)
Definition W_fc028 : bv 32 := @BV 32 0x00f680a3%Z I.



(* [comment removed for export] *)
Definition W_fc02c : bv 32 := @BV 32 0x00268693%Z I.



(* [comment removed for export] *)
Definition W_fc030 : bv 32 := @BV 32 0x01058593%Z I.



(* [comment removed for export] *)
Definition W_fc034 : bv 32 := @BV 32 0x01100793%Z I.



(* [comment removed for export] *)
Definition W_fc038 : bv 32 := @BV 32 0x0107581b%Z I.



(* [comment removed for export] *)
Definition W_fc03c : bv 32 := @BV 32 0xff45a883%Z I.



(* [comment removed for export] *)
Definition W_fc040 : bv 32 := @BV 32 0xff85a283%Z I.



(* [comment removed for export] *)
Definition W_fc044 : bv 32 := @BV 32 0xffc5a303%Z I.



(* [comment removed for export] *)
Definition W_fc048 : bv 32 := @BV 32 0x0005a703%Z I.



(* [comment removed for export] *)
Definition W_fc04c : bv 32 := @BV 32 0x01089393%Z I.



(* [comment removed for export] *)
Definition W_fc050 : bv 32 := @BV 32 0x0108d89b%Z I.



(* [comment removed for export] *)
Definition W_fc054 : bv 32 := @BV 32 0x0103e833%Z I.



(* [comment removed for export] *)
Definition W_fc058 : bv 32 := @BV 32 0x01029393%Z I.



(* [comment removed for export] *)
Definition W_fc05c : bv 32 := @BV 32 0x0102d29b%Z I.



(* [comment removed for export] *)
Definition W_fc060 : bv 32 := @BV 32 0x0113e8b3%Z I.



(* [comment removed for export] *)
Definition W_fc064 : bv 32 := @BV 32 0x01031393%Z I.



(* [comment removed for export] *)
Definition W_fc068 : bv 32 := @BV 32 0x0103531b%Z I.



(* [comment removed for export] *)
Definition W_fc06c : bv 32 := @BV 32 0x0053e2b3%Z I.



(* [comment removed for export] *)
Definition W_fc070 : bv 32 := @BV 32 0x01071393%Z I.



(* [comment removed for export] *)
Definition W_fc074 : bv 32 := @BV 32 0x0063e333%Z I.



(* [comment removed for export] *)
Definition W_fc078 : bv 32 := @BV 32 0xff060613%Z I.



(* [comment removed for export] *)
Definition W_fc07c : bv 32 := @BV 32 0x0106a023%Z I.



(* [comment removed for export] *)
Definition W_fc080 : bv 32 := @BV 32 0x0116a223%Z I.



(* [comment removed for export] *)
Definition W_fc084 : bv 32 := @BV 32 0x0056a423%Z I.



(* [comment removed for export] *)
Definition W_fc088 : bv 32 := @BV 32 0x0066a623%Z I.



(* [comment removed for export] *)
Definition W_fc08c : bv 32 := @BV 32 0x01068693%Z I.



(* [comment removed for export] *)
Definition W_fc090 : bv 32 := @BV 32 0x01058593%Z I.



(* [comment removed for export] *)
Definition W_fc094 : bv 32 := @BV 32 0xfac7e2e3%Z I.



(* [comment removed for export] *)
Definition W_fc098 : bv 32 := @BV 32 0xff258593%Z I.



(* [comment removed for export] *)
Definition W_fc09c : bv 32 := @BV 32 0x01000713%Z I.



(* [comment removed for export] *)
Definition W_fc0a0 : bv 32 := @BV 32 0xf4e66ae3%Z I.



(* [comment removed for export] *)
Definition W_fc0a4 : bv 32 := @BV 32 0x19c0006f%Z I.



(* [comment removed for export] *)
Definition W_fc0a8 : bv 32 := @BV 32 0x00050693%Z I.



(* [comment removed for export] *)
Definition W_fc0ac : bv 32 := @BV 32 0x00357793%Z I.



(* [comment removed for export] *)
Definition W_fc0b0 : bv 32 := @BV 32 0xf2079ae3%Z I.



(* [comment removed for export] *)
Definition W_fc0b4 : bv 32 := @BV 32 0x01000713%Z I.



(* [comment removed for export] *)
Definition W_fc0b8 : bv 32 := @BV 32 0x02e66c63%Z I.



(* [comment removed for export] *)
Definition W_fc0bc : bv 32 := @BV 32 0x00f00713%Z I.



(* [comment removed for export] *)
Definition W_fc0c0 : bv 32 := @BV 32 0x0005a783%Z I.



(* [comment removed for export] *)
Definition W_fc0c4 : bv 32 := @BV 32 0x0045a803%Z I.



(* [comment removed for export] *)
Definition W_fc0c8 : bv 32 := @BV 32 0x0085a883%Z I.



(* [comment removed for export] *)
Definition W_fc0cc : bv 32 := @BV 32 0x00c5a283%Z I.



(* [comment removed for export] *)
Definition W_fc0d0 : bv 32 := @BV 32 0x01058593%Z I.



(* [comment removed for export] *)
Definition W_fc0d4 : bv 32 := @BV 32 0xff060613%Z I.



(* [comment removed for export] *)
Definition W_fc0d8 : bv 32 := @BV 32 0x00f6a023%Z I.



(* [comment removed for export] *)
Definition W_fc0dc : bv 32 := @BV 32 0x0106a223%Z I.



(* [comment removed for export] *)
Definition W_fc0e0 : bv 32 := @BV 32 0x0116a423%Z I.



(* [comment removed for export] *)
Definition W_fc0e4 : bv 32 := @BV 32 0x0056a623%Z I.



(* [comment removed for export] *)
Definition W_fc0e8 : bv 32 := @BV 32 0x01068693%Z I.



(* [comment removed for export] *)
Definition W_fc0ec : bv 32 := @BV 32 0xfcc76ae3%Z I.



(* [comment removed for export] *)
Definition W_fc0f0 : bv 32 := @BV 32 0x00800713%Z I.



(* [comment removed for export] *)
Definition W_fc0f4 : bv 32 := @BV 32 0x00e66e63%Z I.



(* [comment removed for export] *)
Definition W_fc0f8 : bv 32 := @BV 32 0x0005a703%Z I.



(* [comment removed for export] *)
Definition W_fc0fc : bv 32 := @BV 32 0x0045a783%Z I.



(* [comment removed for export] *)
Definition W_fc100 : bv 32 := @BV 32 0x00e6a023%Z I.



(* [comment removed for export] *)
Definition W_fc104 : bv 32 := @BV 32 0x00f6a223%Z I.



(* [comment removed for export] *)
Definition W_fc108 : bv 32 := @BV 32 0x00868693%Z I.



(* [comment removed for export] *)
Definition W_fc10c : bv 32 := @BV 32 0x00858593%Z I.



(* [comment removed for export] *)
Definition W_fc110 : bv 32 := @BV 32 0x00467713%Z I.



(* [comment removed for export] *)
Definition W_fc114 : bv 32 := @BV 32 0x24070063%Z I.



(* [comment removed for export] *)
Definition W_fc118 : bv 32 := @BV 32 0x0005a703%Z I.



(* [comment removed for export] *)
Definition W_fc11c : bv 32 := @BV 32 0x00458593%Z I.



(* [comment removed for export] *)
Definition W_fc120 : bv 32 := @BV 32 0x00e6a023%Z I.



(* [comment removed for export] *)
Definition W_fc124 : bv 32 := @BV 32 0x00468693%Z I.



(* [comment removed for export] *)
Definition W_fc128 : bv 32 := @BV 32 0x22c0006f%Z I.



(* [comment removed for export] *)
Definition W_fc12c : bv 32 := @BV 32 0x00e68023%Z I.



(* [comment removed for export] *)
Definition W_fc130 : bv 32 := @BV 32 0x00168693%Z I.



(* [comment removed for export] *)
Definition W_fc134 : bv 32 := @BV 32 0xfff60613%Z I.



(* [comment removed for export] *)
Definition W_fc138 : bv 32 := @BV 32 0x01058593%Z I.



(* [comment removed for export] *)
Definition W_fc13c : bv 32 := @BV 32 0x01200793%Z I.



(* [comment removed for export] *)
Definition W_fc140 : bv 32 := @BV 32 0x0087581b%Z I.



(* [comment removed for export] *)
Definition W_fc144 : bv 32 := @BV 32 0xff45a883%Z I.



(* [comment removed for export] *)
Definition W_fc148 : bv 32 := @BV 32 0xff85a283%Z I.



(* [comment removed for export] *)
Definition W_fc14c : bv 32 := @BV 32 0xffc5a303%Z I.



(* [comment removed for export] *)
Definition W_fc150 : bv 32 := @BV 32 0x0005a703%Z I.



(* [comment removed for export] *)
Definition W_fc154 : bv 32 := @BV 32 0x01889393%Z I.



(* [comment removed for export] *)
Definition W_fc158 : bv 32 := @BV 32 0x0088d89b%Z I.



(* [comment removed for export] *)
Definition W_fc15c : bv 32 := @BV 32 0x0103e833%Z I.



(* [comment removed for export] *)
Definition W_fc160 : bv 32 := @BV 32 0x01829393%Z I.



(* [comment removed for export] *)
Definition W_fc164 : bv 32 := @BV 32 0x0082d29b%Z I.



(* [comment removed for export] *)
Definition W_fc168 : bv 32 := @BV 32 0x0113e8b3%Z I.



(* [comment removed for export] *)
Definition W_fc16c : bv 32 := @BV 32 0x01831393%Z I.



(* [comment removed for export] *)
Definition W_fc170 : bv 32 := @BV 32 0x0083531b%Z I.



(* [comment removed for export] *)
Definition W_fc174 : bv 32 := @BV 32 0x0053e2b3%Z I.



(* [comment removed for export] *)
Definition W_fc178 : bv 32 := @BV 32 0x01871393%Z I.



(* [comment removed for export] *)
Definition W_fc17c : bv 32 := @BV 32 0x0063e333%Z I.



(* [comment removed for export] *)
Definition W_fc180 : bv 32 := @BV 32 0xff060613%Z I.



(* [comment removed for export] *)
Definition W_fc184 : bv 32 := @BV 32 0x0106a023%Z I.



(* [comment removed for export] *)
Definition W_fc188 : bv 32 := @BV 32 0x0116a223%Z I.



(* [comment removed for export] *)
Definition W_fc18c : bv 32 := @BV 32 0x0056a423%Z I.



(* [comment removed for export] *)
Definition W_fc190 : bv 32 := @BV 32 0x0066a623%Z I.



(* [comment removed for export] *)
Definition W_fc194 : bv 32 := @BV 32 0x01068693%Z I.



(* [comment removed for export] *)
Definition W_fc198 : bv 32 := @BV 32 0x01058593%Z I.



(* [comment removed for export] *)
Definition W_fc19c : bv 32 := @BV 32 0xfac7e2e3%Z I.



(* [comment removed for export] *)
Definition W_fc1a0 : bv 32 := @BV 32 0xff158593%Z I.



(* [comment removed for export] *)
Definition W_fc1a4 : bv 32 := @BV 32 0x01000713%Z I.



(* [comment removed for export] *)
Definition W_fc1a8 : bv 32 := @BV 32 0xe4e666e3%Z I.



(* [comment removed for export] *)
Definition W_fc1ac : bv 32 := @BV 32 0x0940006f%Z I.



(* [comment removed for export] *)
Definition W_fc1b0 : bv 32 := @BV 32 0x00875793%Z I.



(* [comment removed for export] *)
Definition W_fc1b4 : bv 32 := @BV 32 0x01075813%Z I.



(* [comment removed for export] *)
Definition W_fc1b8 : bv 32 := @BV 32 0xffd60613%Z I.



(* [comment removed for export] *)
Definition W_fc1bc : bv 32 := @BV 32 0x00e68023%Z I.



(* [comment removed for export] *)
Definition W_fc1c0 : bv 32 := @BV 32 0x00f680a3%Z I.



(* [comment removed for export] *)
Definition W_fc1c4 : bv 32 := @BV 32 0x01068123%Z I.



(* [comment removed for export] *)
Definition W_fc1c8 : bv 32 := @BV 32 0x00368693%Z I.



(* [comment removed for export] *)
Definition W_fc1cc : bv 32 := @BV 32 0x01058593%Z I.



(* [comment removed for export] *)
Definition W_fc1d0 : bv 32 := @BV 32 0x01000793%Z I.



(* [comment removed for export] *)
Definition W_fc1d4 : bv 32 := @BV 32 0x0187581b%Z I.



(* [comment removed for export] *)
Definition W_fc1d8 : bv 32 := @BV 32 0xff45a883%Z I.



(* [comment removed for export] *)
Definition W_fc1dc : bv 32 := @BV 32 0xff85a283%Z I.



(* [comment removed for export] *)
Definition W_fc1e0 : bv 32 := @BV 32 0xffc5a303%Z I.



(* [comment removed for export] *)
Definition W_fc1e4 : bv 32 := @BV 32 0x0005a703%Z I.



(* [comment removed for export] *)
Definition W_fc1e8 : bv 32 := @BV 32 0x00889393%Z I.



(* [comment removed for export] *)
Definition W_fc1ec : bv 32 := @BV 32 0x0188d89b%Z I.



(* [comment removed for export] *)
Definition W_fc1f0 : bv 32 := @BV 32 0x0103e833%Z I.



(* [comment removed for export] *)
Definition W_fc1f4 : bv 32 := @BV 32 0x00829393%Z I.



(* [comment removed for export] *)
Definition W_fc1f8 : bv 32 := @BV 32 0x0182d29b%Z I.



(* [comment removed for export] *)
Definition W_fc1fc : bv 32 := @BV 32 0x0113e8b3%Z I.



(* [comment removed for export] *)
Definition W_fc200 : bv 32 := @BV 32 0x00831393%Z I.



(* [comment removed for export] *)
Definition W_fc204 : bv 32 := @BV 32 0x0183531b%Z I.



(* [comment removed for export] *)
Definition W_fc208 : bv 32 := @BV 32 0x0053e2b3%Z I.



(* [comment removed for export] *)
Definition W_fc20c : bv 32 := @BV 32 0x00871393%Z I.



(* [comment removed for export] *)
Definition W_fc210 : bv 32 := @BV 32 0x0063e333%Z I.



(* [comment removed for export] *)
Definition W_fc214 : bv 32 := @BV 32 0xff060613%Z I.



(* [comment removed for export] *)
Definition W_fc218 : bv 32 := @BV 32 0x0106a023%Z I.



(* [comment removed for export] *)
Definition W_fc21c : bv 32 := @BV 32 0x0116a223%Z I.



(* [comment removed for export] *)
Definition W_fc220 : bv 32 := @BV 32 0x0056a423%Z I.



(* [comment removed for export] *)
Definition W_fc224 : bv 32 := @BV 32 0x0066a623%Z I.



(* [comment removed for export] *)
Definition W_fc228 : bv 32 := @BV 32 0x01068693%Z I.



(* [comment removed for export] *)
Definition W_fc22c : bv 32 := @BV 32 0x01058593%Z I.



(* [comment removed for export] *)
Definition W_fc230 : bv 32 := @BV 32 0xfac7e2e3%Z I.



(* [comment removed for export] *)
Definition W_fc234 : bv 32 := @BV 32 0xff358593%Z I.



(* [comment removed for export] *)
Definition W_fc238 : bv 32 := @BV 32 0x01000713%Z I.



(* [comment removed for export] *)
Definition W_fc23c : bv 32 := @BV 32 0xdae66ce3%Z I.



(* [comment removed for export] *)
Definition W_fc240 : bv 32 := @BV 32 0x0005c703%Z I.



(* [comment removed for export] *)
Definition W_fc244 : bv 32 := @BV 32 0x0015c783%Z I.



(* [comment removed for export] *)
Definition W_fc248 : bv 32 := @BV 32 0x0025c803%Z I.



(* [comment removed for export] *)
Definition W_fc24c : bv 32 := @BV 32 0x0035c883%Z I.



(* [comment removed for export] *)
Definition W_fc250 : bv 32 := @BV 32 0x0045c283%Z I.



(* [comment removed for export] *)
Definition W_fc254 : bv 32 := @BV 32 0x0055c303%Z I.



(* [comment removed for export] *)
Definition W_fc258 : bv 32 := @BV 32 0x0065c383%Z I.



(* [comment removed for export] *)
Definition W_fc25c : bv 32 := @BV 32 0x0075ce03%Z I.



(* [comment removed for export] *)
Definition W_fc260 : bv 32 := @BV 32 0x00e68023%Z I.



(* [comment removed for export] *)
Definition W_fc264 : bv 32 := @BV 32 0x00f680a3%Z I.



(* [comment removed for export] *)
Definition W_fc268 : bv 32 := @BV 32 0x01068123%Z I.



(* [comment removed for export] *)
Definition W_fc26c : bv 32 := @BV 32 0x011681a3%Z I.



(* [comment removed for export] *)
Definition W_fc270 : bv 32 := @BV 32 0x0085c703%Z I.



(* [comment removed for export] *)
Definition W_fc274 : bv 32 := @BV 32 0x0095c783%Z I.



(* [comment removed for export] *)
Definition W_fc278 : bv 32 := @BV 32 0x00a5c803%Z I.



(* [comment removed for export] *)
Definition W_fc27c : bv 32 := @BV 32 0x00b5c883%Z I.



(* [comment removed for export] *)
Definition W_fc280 : bv 32 := @BV 32 0x00568223%Z I.



(* [comment removed for export] *)
Definition W_fc284 : bv 32 := @BV 32 0x006682a3%Z I.



(* [comment removed for export] *)
Definition W_fc288 : bv 32 := @BV 32 0x00768323%Z I.



(* [comment removed for export] *)
Definition W_fc28c : bv 32 := @BV 32 0x01c683a3%Z I.



(* [comment removed for export] *)
Definition W_fc290 : bv 32 := @BV 32 0x00c5c283%Z I.



(* [comment removed for export] *)
Definition W_fc294 : bv 32 := @BV 32 0x00d5c303%Z I.



(* [comment removed for export] *)
Definition W_fc298 : bv 32 := @BV 32 0x00e5c383%Z I.



(* [comment removed for export] *)
Definition W_fc29c : bv 32 := @BV 32 0x00f5ce03%Z I.



(* [comment removed for export] *)
Definition W_fc2a0 : bv 32 := @BV 32 0x01058593%Z I.



(* [comment removed for export] *)
Definition W_fc2a4 : bv 32 := @BV 32 0x00e68423%Z I.



(* [comment removed for export] *)
Definition W_fc2a8 : bv 32 := @BV 32 0x00f684a3%Z I.



(* [comment removed for export] *)
Definition W_fc2ac : bv 32 := @BV 32 0x01068523%Z I.



(* [comment removed for export] *)
Definition W_fc2b0 : bv 32 := @BV 32 0x011685a3%Z I.



(* [comment removed for export] *)
Definition W_fc2b4 : bv 32 := @BV 32 0x01068713%Z I.



(* [comment removed for export] *)
Definition W_fc2b8 : bv 32 := @BV 32 0x00568623%Z I.



(* [comment removed for export] *)
Definition W_fc2bc : bv 32 := @BV 32 0x006686a3%Z I.



(* [comment removed for export] *)
Definition W_fc2c0 : bv 32 := @BV 32 0x00768723%Z I.



(* [comment removed for export] *)
Definition W_fc2c4 : bv 32 := @BV 32 0x01c687a3%Z I.



(* [comment removed for export] *)
Definition W_fc2c8 : bv 32 := @BV 32 0x00070693%Z I.



(* [comment removed for export] *)
Definition W_fc2cc : bv 32 := @BV 32 0x00867713%Z I.



(* [comment removed for export] *)
Definition W_fc2d0 : bv 32 := @BV 32 0xd20706e3%Z I.



(* [comment removed for export] *)
Definition W_fc2d4 : bv 32 := @BV 32 0x0005c703%Z I.



(* [comment removed for export] *)
Definition W_fc2d8 : bv 32 := @BV 32 0x0015c783%Z I.



(* [comment removed for export] *)
Definition W_fc2dc : bv 32 := @BV 32 0x0025c803%Z I.



(* [comment removed for export] *)
Definition W_fc2e0 : bv 32 := @BV 32 0x0035c883%Z I.



(* [comment removed for export] *)
Definition W_fc2e4 : bv 32 := @BV 32 0x0045c283%Z I.



(* [comment removed for export] *)
Definition W_fc2e8 : bv 32 := @BV 32 0x0055c303%Z I.



(* [comment removed for export] *)
Definition W_fc2ec : bv 32 := @BV 32 0x0065c383%Z I.



(* [comment removed for export] *)
Definition W_fc2f0 : bv 32 := @BV 32 0x0075ce03%Z I.



(* [comment removed for export] *)
Definition W_fc2f4 : bv 32 := @BV 32 0x00858593%Z I.



(* [comment removed for export] *)
Definition W_fc2f8 : bv 32 := @BV 32 0x00e68023%Z I.



(* [comment removed for export] *)
Definition W_fc2fc : bv 32 := @BV 32 0x00f680a3%Z I.



(* [comment removed for export] *)
Definition W_fc300 : bv 32 := @BV 32 0x01068123%Z I.



(* [comment removed for export] *)
Definition W_fc304 : bv 32 := @BV 32 0x011681a3%Z I.



(* [comment removed for export] *)
Definition W_fc308 : bv 32 := @BV 32 0x00868713%Z I.



(* [comment removed for export] *)
Definition W_fc30c : bv 32 := @BV 32 0x00568223%Z I.



(* [comment removed for export] *)
Definition W_fc310 : bv 32 := @BV 32 0x006682a3%Z I.



(* [comment removed for export] *)
Definition W_fc314 : bv 32 := @BV 32 0x00768323%Z I.



(* [comment removed for export] *)
Definition W_fc318 : bv 32 := @BV 32 0x01c683a3%Z I.



(* [comment removed for export] *)
Definition W_fc31c : bv 32 := @BV 32 0x00070693%Z I.



(* [comment removed for export] *)
Definition W_fc320 : bv 32 := @BV 32 0x00467713%Z I.



(* [comment removed for export] *)
Definition W_fc324 : bv 32 := @BV 32 0x02070863%Z I.



(* [comment removed for export] *)
Definition W_fc328 : bv 32 := @BV 32 0x0005c703%Z I.



(* [comment removed for export] *)
Definition W_fc32c : bv 32 := @BV 32 0x0015c783%Z I.



(* [comment removed for export] *)
Definition W_fc330 : bv 32 := @BV 32 0x0025c803%Z I.



(* [comment removed for export] *)
Definition W_fc334 : bv 32 := @BV 32 0x0035c883%Z I.



(* [comment removed for export] *)
Definition W_fc338 : bv 32 := @BV 32 0x00458593%Z I.



(* [comment removed for export] *)
Definition W_fc33c : bv 32 := @BV 32 0x00468293%Z I.



(* [comment removed for export] *)
Definition W_fc340 : bv 32 := @BV 32 0x00e68023%Z I.



(* [comment removed for export] *)
Definition W_fc344 : bv 32 := @BV 32 0x00f680a3%Z I.



(* [comment removed for export] *)
Definition W_fc348 : bv 32 := @BV 32 0x01068123%Z I.



(* [comment removed for export] *)
Definition W_fc34c : bv 32 := @BV 32 0x011681a3%Z I.



(* [comment removed for export] *)
Definition W_fc350 : bv 32 := @BV 32 0x00028693%Z I.



(* [comment removed for export] *)
Definition W_fc354 : bv 32 := @BV 32 0x00267713%Z I.



(* [comment removed for export] *)
Definition W_fc358 : bv 32 := @BV 32 0x00071863%Z I.



(* [comment removed for export] *)
Definition W_fc35c : bv 32 := @BV 32 0x00167613%Z I.



(* [comment removed for export] *)
Definition W_fc360 : bv 32 := @BV 32 0x02061663%Z I.



(* [comment removed for export] *)
Definition W_fc364 : bv 32 := @BV 32 0x00008067%Z I.



(* [comment removed for export] *)
Definition W_fc368 : bv 32 := @BV 32 0x0005c703%Z I.



(* [comment removed for export] *)
Definition W_fc36c : bv 32 := @BV 32 0x0015c783%Z I.



(* [comment removed for export] *)
Definition W_fc370 : bv 32 := @BV 32 0x00258593%Z I.



(* [comment removed for export] *)
Definition W_fc374 : bv 32 := @BV 32 0x00268813%Z I.



(* [comment removed for export] *)
Definition W_fc378 : bv 32 := @BV 32 0x00e68023%Z I.



(* [comment removed for export] *)
Definition W_fc37c : bv 32 := @BV 32 0x00f680a3%Z I.



(* [comment removed for export] *)
Definition W_fc380 : bv 32 := @BV 32 0x00080693%Z I.



(* [comment removed for export] *)
Definition W_fc384 : bv 32 := @BV 32 0x00167613%Z I.



(* [comment removed for export] *)
Definition W_fc388 : bv 32 := @BV 32 0xfc060ee3%Z I.



(* [comment removed for export] *)
Definition W_fc38c : bv 32 := @BV 32 0x0005c583%Z I.



(* [comment removed for export] *)
Definition W_fc390 : bv 32 := @BV 32 0x00b68023%Z I.



(* [comment removed for export] *)
Definition W_fc394 : bv 32 := @BV 32 0x00008067%Z I.


End Bo_code_fbe98_fc490.
Module Bo_code_fc4cc_fc674.
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












End Bo_code_fc4cc_fc674.
Module Bo_code_fc820_fc864.
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
End Bo_code_fc820_fc864.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct Bo_code_fbe98_fc490 Bo_code_fc4cc_fc674 Bo_code_fc820_fc864.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.


(* [comment removed for export] *)
Section FPGen1.
Context {fx : FPState}.

Definition mmemcpy_words : list (bv 32) :=
  [W_fbf94; W_fbf98; W_fbf9c; W_fbfa0; W_fbfa4; W_fbfa8; W_fbfac; W_fbfb0; W_fbfb4; W_fbfb8; W_fbfbc; W_fbfc0; W_fbfc4; W_fbfc8; W_fbfcc; W_fbfd0; W_fbfd4; W_fbfd8; W_fbfdc; W_fbfe0; W_fbfe4; W_fbfe8; W_fbfec; W_fbff0; W_fbff4; W_fbff8; W_fbffc; W_fc000; W_fc004; W_fc008; W_fc00c; W_fc010; W_fc014; W_fc018; W_fc01c; W_fc020; W_fc024; W_fc028; W_fc02c; W_fc030; W_fc034; W_fc038; W_fc03c; W_fc040; W_fc044; W_fc048; W_fc04c; W_fc050; W_fc054; W_fc058; W_fc05c; W_fc060; W_fc064; W_fc068; W_fc06c; W_fc070; W_fc074; W_fc078; W_fc07c; W_fc080; W_fc084; W_fc088; W_fc08c; W_fc090; W_fc094; W_fc098; W_fc09c; W_fc0a0; W_fc0a4; W_fc0a8; W_fc0ac; W_fc0b0; W_fc0b4; W_fc0b8; W_fc0bc; W_fc0c0; W_fc0c4; W_fc0c8; W_fc0cc; W_fc0d0; W_fc0d4; W_fc0d8; W_fc0dc; W_fc0e0; W_fc0e4; W_fc0e8; W_fc0ec; W_fc0f0; W_fc0f4; W_fc0f8; W_fc0fc; W_fc100; W_fc104; W_fc108; W_fc10c; W_fc110; W_fc114; W_fc118; W_fc11c; W_fc120; W_fc124; W_fc128; W_fc12c; W_fc130; W_fc134; W_fc138; W_fc13c; W_fc140; W_fc144; W_fc148; W_fc14c; W_fc150; W_fc154; W_fc158; W_fc15c; W_fc160; W_fc164; W_fc168; W_fc16c; W_fc170; W_fc174; W_fc178; W_fc17c; W_fc180; W_fc184; W_fc188; W_fc18c; W_fc190; W_fc194; W_fc198; W_fc19c; W_fc1a0; W_fc1a4; W_fc1a8; W_fc1ac; W_fc1b0; W_fc1b4; W_fc1b8; W_fc1bc; W_fc1c0; W_fc1c4; W_fc1c8; W_fc1cc; W_fc1d0; W_fc1d4; W_fc1d8; W_fc1dc; W_fc1e0; W_fc1e4; W_fc1e8; W_fc1ec; W_fc1f0; W_fc1f4; W_fc1f8; W_fc1fc; W_fc200; W_fc204; W_fc208; W_fc20c; W_fc210; W_fc214; W_fc218; W_fc21c; W_fc220; W_fc224; W_fc228; W_fc22c; W_fc230; W_fc234; W_fc238; W_fc23c; W_fc240; W_fc244; W_fc248; W_fc24c; W_fc250; W_fc254; W_fc258; W_fc25c; W_fc260; W_fc264; W_fc268; W_fc26c; W_fc270; W_fc274; W_fc278; W_fc27c; W_fc280; W_fc284; W_fc288; W_fc28c; W_fc290; W_fc294; W_fc298; W_fc29c; W_fc2a0; W_fc2a4; W_fc2a8; W_fc2ac; W_fc2b0; W_fc2b4; W_fc2b8; W_fc2bc; W_fc2c0; W_fc2c4; W_fc2c8; W_fc2cc; W_fc2d0; W_fc2d4; W_fc2d8; W_fc2dc; W_fc2e0; W_fc2e4; W_fc2e8; W_fc2ec; W_fc2f0; W_fc2f4; W_fc2f8; W_fc2fc; W_fc300; W_fc304; W_fc308; W_fc30c; W_fc310; W_fc314; W_fc318; W_fc31c; W_fc320; W_fc324; W_fc328; W_fc32c; W_fc330; W_fc334; W_fc338; W_fc33c; W_fc340; W_fc344; W_fc348; W_fc34c; W_fc350; W_fc354; W_fc358; W_fc35c; W_fc360; W_fc364; W_fc368; W_fc36c; W_fc370; W_fc374; W_fc378; W_fc37c; W_fc380; W_fc384; W_fc388; W_fc38c; W_fc390; W_fc394]%list.

(* [comment removed for export] *)
Record mcH (segs : list Segment) (mem0 : word -> option byte) (dst src : word) (n : Z) (bs : list byte) : Prop := MCH {
  Hn : (0 <= n < 2 ^ 64)%Z;
  Hlen : length bs = Z.to_nat n;
  Hsrc : rdn segs mem0 src (length bs) = Some bs;
  Hdst : store_ok segs mem0 dst (length bs) = true;
  Hdisj : (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst)%Z;
  Hnws : (bv_unsigned src + n < 2 ^ 64)%Z;
  Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z }.

Section MC.
  Variable segs : list Segment.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Hypothesis HOK : mcH segs mem0 dst src n bs.

  Let Hn := Hn _ _ _ _ _ _ HOK.
  Let Hlen := Hlen _ _ _ _ _ _ HOK.
  Let Hsrc := Hsrc _ _ _ _ _ _ HOK.
  Let Hdst := Hdst _ _ _ _ _ _ HOK.
  Let Hdisj := Hdisj _ _ _ _ _ _ HOK.
  Let Hnws := Hnws _ _ _ _ _ _ HOK.
  Let Hnwd := Hnwd _ _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Definition sb_ (j : Z) (m : nat) : list byte := sub bs (Z.to_nat j) m.
  (* [comment removed for export] *)
  Definition b_ (j : Z) : byte := nth (Z.to_nat j) bs (Z_to_bv 8 0).




  Lemma sb_len : forall j m, (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z -> length (sb_ j m) = m.
  Proof using Hlen Hn HOK src dst mem0 segs. intros j m Hj Hm. (lazymatch goal with |- ?G => let G' := eval unfold sb_ in G in change_no_check G' end). apply sub_length. rewrite Hlen. lia. Qed.

























End MC.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End FPGen1.

Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.

(* [comment removed for export] *)
Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.

(* [comment removed for export] *)
Ltac mnorm := gres; imm_norm; rewrite ?v_addi_0; rwH; rewrite ?at_addi; vals_lit.

(* [comment removed for export] *)
Ltac cond_lia :=
  rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_ltu, c_eq, bv_ltu, bv_eqb in G in change_no_check G' end); imm_norm; unorm;
  first [ apply Z.ltb_lt | apply Z.ltb_ge | apply Z.eqb_eq | apply Z.eqb_neq ]; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPGen2.
Context {fx : FPState}.


Lemma u_andi : forall (x : word) imm, (0 <= imm < 2 ^ 64)%Z ->
  bv_unsigned (v_andi x imm) = Z.land (bv_unsigned x) imm.
Proof using.
  intros x imm Hi. (lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end). rewrite Z_to_bv_unsigned.
  replace (bv_wrap 64 imm) with imm by (symmetry; apply bv_wrap_small; change (bv_modulus 64) with (2^64)%Z; lia).
  apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. apply Z_land_range; [apply u64_range|lia].
Qed.





(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MF.
  Variable segs : list Segment.
  Variable base : word.
  Hypothesis HCODE : code_at segs base 0 mmemcpy_words.

































































































































































































































































End MF.
End FPGen2.


