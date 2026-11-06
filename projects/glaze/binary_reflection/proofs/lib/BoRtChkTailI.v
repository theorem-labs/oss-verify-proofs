(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.InstrEnc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Bo_code_5d2ec_5d34c.
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
Definition W_5d304 : bv 32 := @BV 32 0x0eb67863%Z I.
Lemma F_5d304 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5d304%Z I : word) = Some W_5d304.
Proof. vm_refl. Qed.
Lemma D_5d304 : decode_any W_5d304 = Some (Branch BC_GEU (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 13 240%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d308 : bv 32 := @BV 32 0x000a9597%Z I.
Lemma F_5d308 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5d308%Z I : word) = Some W_5d308.
Proof. vm_refl. Qed.
Lemma D_5d308 : decode_any W_5d308 = Some (Auipc (@BV 5 11%Z I) (@BV 20 169%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d30c : bv 32 := @BV 32 0xc105b583%Z I.
Lemma F_5d30c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5d30c%Z I : word) = Some W_5d30c.
Proof. vm_refl. Qed.
Lemma D_5d30c : decode_any W_5d30c = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 3088%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d340 : bv 32 := @BV 32 0x0a071e63%Z I.
Lemma F_5d340 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5d340%Z I : word) = Some W_5d340.
Proof. vm_refl. Qed.
Lemma D_5d340 : decode_any W_5d340 = Some (Branch BC_NE (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 13 188%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_5d2ec_5d34c.
Module Bo_code_5e7ac_5e7fc.
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
Definition W_5e7b4 : bv 32 := @BV 32 0x12b67663%Z I.
Lemma F_5e7b4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5e7b4%Z I : word) = Some W_5e7b4.
Proof. vm_refl. Qed.
Lemma D_5e7b4 : decode_any W_5e7b4 = Some (Branch BC_GEU (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 13 300%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e7b8 : bv 32 := @BV 32 0x000a7597%Z I.
Lemma F_5e7b8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5e7b8%Z I : word) = Some W_5e7b8.
Proof. vm_refl. Qed.
Lemma D_5e7b8 : decode_any W_5e7b8 = Some (Auipc (@BV 5 11%Z I) (@BV 20 167%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e7bc : bv 32 := @BV 32 0x7605b583%Z I.
Lemma F_5e7bc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5e7bc%Z I : word) = Some W_5e7bc.
Proof. vm_refl. Qed.
Lemma D_5e7bc : decode_any W_5e7bc = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 1888%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e7f0 : bv 32 := @BV 32 0x0e071c63%Z I.
Lemma F_5e7f0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5e7f0%Z I : word) = Some W_5e7f0.
Proof. vm_refl. Qed.
Lemma D_5e7f0 : decode_any W_5e7f0 = Some (Branch BC_NE (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 13 248%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_5e7ac_5e7fc.
Module Bo_code_5fe1c_5fe6c.
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
Definition W_5fe24 : bv 32 := @BV 32 0x2ca5f063%Z I.
Lemma F_5fe24 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5fe24%Z I : word) = Some W_5fe24.
Proof. vm_refl. Qed.
Lemma D_5fe24 : decode_any W_5fe24 = Some (Branch BC_GEU (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 13 704%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe28 : bv 32 := @BV 32 0x000a6517%Z I.
Lemma F_5fe28 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5fe28%Z I : word) = Some W_5fe28.
Proof. vm_refl. Qed.
Lemma D_5fe28 : decode_any W_5fe28 = Some (Auipc (@BV 5 10%Z I) (@BV 20 166%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe2c : bv 32 := @BV 32 0x0f053503%Z I.
Lemma F_5fe2c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5fe2c%Z I : word) = Some W_5fe2c.
Proof. vm_refl. Qed.
Lemma D_5fe2c : decode_any W_5fe2c = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 240%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe60 : bv 32 := @BV 32 0xf00688e3%Z I.
Lemma F_5fe60 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5fe60%Z I : word) = Some W_5fe60.
Proof. vm_refl. Qed.
Lemma D_5fe60 : decode_any W_5fe60 = Some (Branch BC_EQ (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 13 7952%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_5fe1c_5fe6c.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtChkTail. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct Bo_code_5d2ec_5d34c Bo_code_5e7ac_5e7fc Bo_code_5fe1c_5fe6c OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtChkTail.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Section FPGen1.
Context {fx : FPState}.
Ltac lit b o v := replace (at_ b o) with v by (apply bv_eq; vm_compute; reflexivity).

(* [comment removed for export] *)
Lemma both_ct_strnlen_code : code_ato BSEGS (0x5d2fc : word) 0 ctB_words.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold ctB_words in G in change_no_check G' end). code_ato_vm. Qed.
Lemma both_ct_strnlen_B8 : gbgeu BSEGS (at_ (0x5d2fc : word) 8) 12 11 (0x5d3f4 : word).
Proof using. lit (0x5d2fc : word) 8%Z (0x5d304 : word). eapply (gbgeu_of BSEGS _ _ _ _ _ _ F_5d304 eq_refl D_5d304). apply bv_eq; vm_compute; reflexivity. Qed.
Lemma both_ct_strnlen_G12 : gload BSEGS (0x5d2fc : word) 12 11 0x105f18.
Proof using. gload_tac F_5d308 D_5d308 F_5d30c D_5d30c. Qed.
Lemma both_ct_strnlen_B68 : gbnez BSEGS (at_ (0x5d2fc : word) 68) 14 (0x5d3fc : word).
Proof using. lit (0x5d2fc : word) 68%Z (0x5d340 : word). eapply (gbnez_of BSEGS _ _ _ _ _ F_5d340 eq_refl D_5d340). apply bv_eq; vm_compute; reflexivity. Qed.
Definition both_chk_tail_strnlen :=
  chk_tail_B BSEGS (0x5d2fc : word) 0x105f18 0x10e1b8 (0x5d3f4 : word) (0x5d3fc : word)
             both_ct_strnlen_code both_ct_strnlen_B8 both_ct_strnlen_G12 both_ct_strnlen_B68.

(* [comment removed for export] *)
Lemma both_ct_memchr_code : code_ato BSEGS (0x5e7ac : word) 0 ctB_words.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold ctB_words in G in change_no_check G' end). code_ato_vm. Qed.
Lemma both_ct_memchr_B8 : gbgeu BSEGS (at_ (0x5e7ac : word) 8) 12 11 (0x5e8e0 : word).
Proof using. lit (0x5e7ac : word) 8%Z (0x5e7b4 : word). eapply (gbgeu_of BSEGS _ _ _ _ _ _ F_5e7b4 eq_refl D_5e7b4). apply bv_eq; vm_compute; reflexivity. Qed.
Lemma both_ct_memchr_G12 : gload BSEGS (0x5e7ac : word) 12 11 0x105f18.
Proof using. gload_tac F_5e7b8 D_5e7b8 F_5e7bc D_5e7bc. Qed.
Lemma both_ct_memchr_B68 : gbnez BSEGS (at_ (0x5e7ac : word) 68) 14 (0x5e8e8 : word).
Proof using. lit (0x5e7ac : word) 68%Z (0x5e7f0 : word). eapply (gbnez_of BSEGS _ _ _ _ _ F_5e7f0 eq_refl D_5e7f0). apply bv_eq; vm_compute; reflexivity. Qed.
Definition both_chk_tail_memchr :=
  chk_tail_B BSEGS (0x5e7ac : word) 0x105f18 0x10e1b8 (0x5e8e0 : word) (0x5e8e8 : word)
             both_ct_memchr_code both_ct_memchr_B8 both_ct_memchr_G12 both_ct_memchr_B68.

(* [comment removed for export] *)
Lemma both_ct_printf_code : code_ato BSEGS (0x5fe1c : word) 0 ctA_words.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold ctA_words in G in change_no_check G' end). code_ato_vm. Qed.
Lemma both_ct_printf_B8 : gbgeu BSEGS (at_ (0x5fe1c : word) 8) 11 10 (0x600e4 : word).
Proof using. lit (0x5fe1c : word) 8%Z (0x5fe24 : word). eapply (gbgeu_of BSEGS _ _ _ _ _ _ F_5fe24 eq_refl D_5fe24). apply bv_eq; vm_compute; reflexivity. Qed.
Lemma both_ct_printf_G12 : gload BSEGS (0x5fe1c : word) 12 10 0x105f18.
Proof using. gload_tac F_5fe28 D_5fe28 F_5fe2c D_5fe2c. Qed.
Lemma both_ct_printf_B68 : gbeqz BSEGS (at_ (0x5fe1c : word) 68) 13 (0x5fd70 : word).
Proof using. lit (0x5fe1c : word) 68%Z (0x5fe60 : word). eapply (gbeqz_of BSEGS _ _ _ _ _ F_5fe60 eq_refl D_5fe60). apply bv_eq; vm_compute; reflexivity. Qed.
Definition both_chk_tail_printf :=
  chk_tail_A BSEGS (0x5fe1c : word) 0x105f18 0x10e1b8 (0x600e4 : word) (0x5fd70 : word)
             both_ct_printf_code both_ct_printf_B8 both_ct_printf_G12 both_ct_printf_B68.
End FPGen1.
