(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.InstrEnc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Bo_code_5a8b8_5ae84.
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
Definition W_5a8f4 : bv 32 := @BV 32 0x000ab597%Z I.
Lemma F_5a8f4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5a8f4%Z I : word) = Some W_5a8f4.
Proof. vm_refl. Qed.
Lemma D_5a8f4 : decode_any W_5a8f4 = Some (Auipc (@BV 5 11%Z I) (@BV 20 171%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a8f8 : bv 32 := @BV 32 0x61c5bc83%Z I.
Lemma F_5a8f8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5a8f8%Z I : word) = Some W_5a8f8.
Proof. vm_refl. Qed.
Lemma D_5a8f8 : decode_any W_5a8f8 = Some (Load SZ8 true (@BV 5 25%Z I) (@BV 5 11%Z I) (@BV 12 1564%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a90c : bv 32 := @BV 32 0x000b1617%Z I.
Lemma F_5a90c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5a90c%Z I : word) = Some W_5a90c.
Proof. vm_refl. Qed.
Lemma D_5a90c : decode_any W_5a90c = Some (Auipc (@BV 5 12%Z I) (@BV 20 177%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a91c : bv 32 := @BV 32 0x12460b13%Z I.
Lemma F_5a91c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5a91c%Z I : word) = Some W_5a91c.
Proof. vm_refl. Qed.
Lemma D_5a91c : decode_any W_5a91c = Some (OpImm ALU_ADD (@BV 5 22%Z I) (@BV 5 12%Z I) (@BV 12 292%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a9f0 : bv 32 := @BV 32 0x000ab517%Z I.
Lemma F_5a9f0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5a9f0%Z I : word) = Some W_5a9f0.
Proof. vm_refl. Qed.
Lemma D_5a9f0 : decode_any W_5a9f0 = Some (Auipc (@BV 5 10%Z I) (@BV 20 171%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a9f4 : bv 32 := @BV 32 0x000ab597%Z I.
Lemma F_5a9f4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5a9f4%Z I : word) = Some W_5a9f4.
Proof. vm_refl. Qed.
Lemma D_5a9f4 : decode_any W_5a9f4 = Some (Auipc (@BV 5 11%Z I) (@BV 20 171%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a9f8 : bv 32 := @BV 32 0x000ab617%Z I.
Lemma F_5a9f8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5a9f8%Z I : word) = Some W_5a9f8.
Proof. vm_refl. Qed.
Lemma D_5a9f8 : decode_any W_5a9f8 = Some (Auipc (@BV 5 12%Z I) (@BV 20 171%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a9fc : bv 32 := @BV 32 0x000ab697%Z I.
Lemma F_5a9fc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5a9fc%Z I : word) = Some W_5a9fc.
Proof. vm_refl. Qed.
Lemma D_5a9fc : decode_any W_5a9fc = Some (Auipc (@BV 5 13%Z I) (@BV 20 171%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa00 : bv 32 := @BV 32 0x000ab717%Z I.
Lemma F_5aa00 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5aa00%Z I : word) = Some W_5aa00.
Proof. vm_refl. Qed.
Lemma D_5aa00 : decode_any W_5aa00 = Some (Auipc (@BV 5 14%Z I) (@BV 20 171%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa04 : bv 32 := @BV 32 0x000ab797%Z I.
Lemma F_5aa04 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5aa04%Z I : word) = Some W_5aa04.
Proof. vm_refl. Qed.
Lemma D_5aa04 : decode_any W_5aa04 = Some (Auipc (@BV 5 15%Z I) (@BV 20 171%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa08 : bv 32 := @BV 32 0x000ab817%Z I.
Lemma F_5aa08 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5aa08%Z I : word) = Some W_5aa08.
Proof. vm_refl. Qed.
Lemma D_5aa08 : decode_any W_5aa08 = Some (Auipc (@BV 5 16%Z I) (@BV 20 171%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa0c : bv 32 := @BV 32 0x52853d03%Z I.
Lemma F_5aa0c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5aa0c%Z I : word) = Some W_5aa0c.
Proof. vm_refl. Qed.
Lemma D_5aa0c : decode_any W_5aa0c = Some (Load SZ8 true (@BV 5 26%Z I) (@BV 5 10%Z I) (@BV 12 1320%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa10 : bv 32 := @BV 32 0x52c5b503%Z I.
Lemma F_5aa10 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5aa10%Z I : word) = Some W_5aa10.
Proof. vm_refl. Qed.
Lemma D_5aa10 : decode_any W_5aa10 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 1324%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa18 : bv 32 := @BV 32 0x53063503%Z I.
Lemma F_5aa18 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5aa18%Z I : word) = Some W_5aa18.
Proof. vm_refl. Qed.
Lemma D_5aa18 : decode_any W_5aa18 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 12%Z I) (@BV 12 1328%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa20 : bv 32 := @BV 32 0x5346b503%Z I.
Lemma F_5aa20 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5aa20%Z I : word) = Some W_5aa20.
Proof. vm_refl. Qed.
Lemma D_5aa20 : decode_any W_5aa20 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 13%Z I) (@BV 12 1332%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa28 : bv 32 := @BV 32 0x50873483%Z I.
Lemma F_5aa28 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5aa28%Z I : word) = Some W_5aa28.
Proof. vm_refl. Qed.
Lemma D_5aa28 : decode_any W_5aa28 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 14%Z I) (@BV 12 1288%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa2c : bv 32 := @BV 32 0x5347bb83%Z I.
Lemma F_5aa2c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5aa2c%Z I : word) = Some W_5aa2c.
Proof. vm_refl. Qed.
Lemma D_5aa2c : decode_any W_5aa2c = Some (Load SZ8 true (@BV 5 23%Z I) (@BV 5 15%Z I) (@BV 12 1332%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa30 : bv 32 := @BV 32 0x4f083503%Z I.
Lemma F_5aa30 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5aa30%Z I : word) = Some W_5aa30.
Proof. vm_refl. Qed.
Lemma D_5aa30 : decode_any W_5aa30 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 16%Z I) (@BV 12 1264%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa3c : bv 32 := @BV 32 0xfffc2517%Z I.
Lemma F_5aa3c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5aa3c%Z I : word) = Some W_5aa3c.
Proof. vm_refl. Qed.
Lemma D_5aa3c : decode_any W_5aa3c = Some (Auipc (@BV 5 10%Z I) (@BV 20 1048514%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa40 : bv 32 := @BV 32 0xac750993%Z I.
Lemma F_5aa40 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5aa40%Z I : word) = Some W_5aa40.
Proof. vm_refl. Qed.
Lemma D_5aa40 : decode_any W_5aa40 = Some (OpImm ALU_ADD (@BV 5 19%Z I) (@BV 5 10%Z I) (@BV 12 2759%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aca8 : bv 32 := @BV 32 0xfffb5697%Z I.
Lemma F_5aca8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5aca8%Z I : word) = Some W_5aca8.
Proof. vm_refl. Qed.
Lemma D_5aca8 : decode_any W_5aca8 = Some (Auipc (@BV 5 13%Z I) (@BV 20 1048501%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5acb8 : bv 32 := @BV 32 0x7c06b683%Z I.
Lemma F_5acb8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x5acb8%Z I : word) = Some W_5acb8.
Proof. vm_refl. Qed.
Lemma D_5acb8 : decode_any W_5acb8 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 1984%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_5a8b8_5ae84.
Module Bo_code_c5cd0_c5d00.
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
Definition W_c5cd8 : bv 32 := @BV 32 0x00041517%Z I.
Lemma F_c5cd8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xc5cd8%Z I : word) = Some W_c5cd8.
Proof. vm_refl. Qed.
Lemma D_c5cd8 : decode_any W_c5cd8 = Some (Auipc (@BV 5 10%Z I) (@BV 20 65%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5cdc : bv 32 := @BV 32 0x00041617%Z I.
Lemma F_c5cdc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xc5cdc%Z I : word) = Some W_c5cdc.
Proof. vm_refl. Qed.
Lemma D_c5cdc : decode_any W_c5cdc = Some (Auipc (@BV 5 12%Z I) (@BV 20 65%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5ce0 : bv 32 := @BV 32 0xed053583%Z I.
Lemma F_c5ce0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xc5ce0%Z I : word) = Some W_c5ce0.
Proof. vm_refl. Qed.
Lemma D_c5ce0 : decode_any W_c5ce0 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 3792%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5ce4 : bv 32 := @BV 32 0xed463603%Z I.
Lemma F_c5ce4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xc5ce4%Z I : word) = Some W_c5ce4.
Proof. vm_refl. Qed.
Lemma D_c5ce4 : decode_any W_c5ce4 = Some (Load SZ8 true (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 3796%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5ce8 : bv 32 := @BV 32 0x00045517%Z I.
Lemma F_c5ce8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xc5ce8%Z I : word) = Some W_c5ce8.
Proof. vm_refl. Qed.
Lemma D_c5ce8 : decode_any W_c5ce8 = Some (Auipc (@BV 5 10%Z I) (@BV 20 69%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5cec : bv 32 := @BV 32 0xe1850513%Z I.
Lemma F_c5cec : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xc5cec%Z I : word) = Some W_c5cec.
Proof. vm_refl. Qed.
Lemma D_c5cec : decode_any W_c5cec = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 3608%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5cf0 : bv 32 := @BV 32 0xa00950ef%Z I.
Lemma F_c5cf0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xc5cf0%Z I : word) = Some W_c5cf0.
Proof. vm_refl. Qed.
Lemma D_c5cf0 : decode_any W_c5cf0 = Some (Jal (@BV 5 1%Z I) (@BV 21 1659392%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_c5cd0_c5d00.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnreg OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnregI. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct Bo_code_5a8b8_5ae84 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI.Bo_code_7006c_706b8 Bo_code_c5cd0_c5d00 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA.AsRtXStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnreg OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnregI.AsRtUnregChk.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Definition both_unreg_globs : list (Z * Z) :=
  [(0x22ae0, 0x20); (0x22b00, 0x20); (0x22b20, 0x40); (0x22b60, 0x20); (0x26940, 0x60);
   (0x269a0, 0x60); (0x26a00, 0x20); (0x26a20, 0x60); (0x26a80, 0x40)]%Z.

Definition both_unreg_tab : unreg_tab :=
  {| ut_dtor := 0xc5cd0; ut_base := 0x5a8b8; ut_pt := both_poison_tab;
     ut_g_start := 0x106ba8; ut_g_stop := 0x106bb0; ut_p_start := 0x10a8c0; ut_globs := both_unreg_globs;
     ut_p_flag := 0x10ab00; ut_g_aflags := 0x105f10; ut_p_aflags := 0x10b9b8; ut_p_mu := 0x10ba70;
     ut_g_pgsz := 0x105ef8; ut_c_inited := 0x10ee98; ut_c_ro := 0x10468; ut_str := 0x1c503 |}.

Section FPGen1.
Context {fx : FPState}.

Ltac lit a v := replace (at_ (0x5a8b8 : word) a) with v by (apply bv_eq; vm_compute; reflexivity).
Ltac litd a v := replace (at_ (0xc5cd0 : word) a) with v by (apply bv_eq; vm_compute; reflexivity).

(* [comment removed for export] *)
Ltac gapaddi_tac Fa Da Fb Db :=
  let regs := fresh "regs" in let mem := fresh "mem" in let rom := fresh "rom" in
  let Hx := fresh "Hx" in
  wd_eexists; split;
  [ intros regs mem rom; lit_pc;
    (chain_step; [ reflexivity | eapply step_auipc; [exact Fa | reflexivity | exact Da] | step_simpl ]);
    gres; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_auipc in G in change_no_check G' end); vals_lit; close_eq
  | intros regs mem rom Hx; lit_pc;
    (chain_step; [ reflexivity | eapply step_addi; [exact Fb | reflexivity | exact Db] | step_simpl ]);
    gres; rewrite Hx; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); vals_lit; close_eq ].

(* [comment removed for export] *)
Ltac gjal_tac Fa Da :=
  let regs := fresh "regs" in let mem := fresh "mem" in let rom := fresh "rom" in
  intros regs mem rom; lit_pc;
  (chain_step; [ reflexivity | exact (step_jal_link _ _ _ _ _ _ _ _ Fa eq_refl Da) | step_simpl ]);
  gres; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold btgt in G in change_no_check G' end); vals_lit; close_eq.

(* [comment removed for export] *)
Lemma both_cpm_run : cpm_call BSEGS (0x7006c : word) 0x10da1c.
Proof using.
  intros regs mem rom ra cpm Rd Hnz Hret H1.
  (chain_step; [ reflexivity | eapply step_auipc; [exact F_7006c | reflexivity | exact D_7006c] | step_simpl ]).
  gres; imm_norm; vals_lit.
  (chain_step;
   [ reflexivity
   | eapply step_lb; [exact F_70070 | reflexivity | exact D_70070 | ];
     gres; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_auipc, v_addi in G in change_no_check G' end); vals_lit; rdn_lit_exact Rd
   | step_simpl ]).
  gres.
  afence F_70074 D_70074.
  an F_70078 D_70078.                                   (* [comment removed for export] *)
  aret F_7007c D_7007c ra.                              (* [comment removed for export] *)
  rewrite ?regupd_regupd_same.
  lazymatch goal with |- msteps _ (mkst (regupd _ 10 ?v) _ _ _) _ =>
    replace v with (Z_to_bv 64 1 : word) end.
  - wd_refl.
  - pose proof (u_v_lb_nz cpm Hnz) as Hl. pose proof (u64_range (v_lb cpm)).
    (lazymatch goal with |- ?G => let G' := eval unfold v_sltu, c_ltu, bv_ltu in G in change_no_check G' end). rewrite u_Z2bv by lia.
    destruct (Z.ltb_spec 0 (bv_unsigned (v_lb cpm))); [reflexivity | lia].
Qed.

Lemma both_unreg_tab_ok : unreg_tab_ok BSEGS both_unreg_tab.
Proof using.
  split; (lazymatch goal with |- ?G => let G' := eval cbn [ut_dtor ut_base ut_pt ut_g_start ut_g_stop ut_p_start ut_globs ut_p_flag ut_g_aflags ut_p_aflags ut_p_mu ut_g_pgsz
              ut_c_inited ut_c_ro ut_str both_unreg_tab pt_base pt_g_shoff pt_g_midbeg pt_g_midend pt_g_hiend pt_g_rms pt_g_cfl pt_c_cpm
              both_poison_tab] in G in change_no_check G' end).
  - (lazymatch goal with |- ?G => let G' := eval unfold unreg_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold dtor_words in G in change_no_check G' end). code_ato_vm.
  - exact both_poison_tab_ok.
  - apply bv_eq; vm_compute; reflexivity.
  - lit 110180%Z (0x7571c : word). exact both_inited_run.
  - lit 87988%Z (0x7006c : word). exact both_cpm_run.
  - gload_tac F_5a8f4 D_5a8f4 F_5a8f8 D_5a8f8.
  - gapaddi_tac F_5a90c D_5a90c F_5a91c D_5a91c.
  - gauipc_ld_tac F_5a9f0 D_5a9f0 F_5aa0c D_5aa0c.
  - gauipc_ld_tac F_5a9f4 D_5a9f4 F_5aa10 D_5aa10.
  - gauipc_ld_tac F_5a9f8 D_5a9f8 F_5aa18 D_5aa18.
  - gauipc_ld_tac F_5a9fc D_5a9fc F_5aa20 D_5aa20.
  - gauipc_ld_tac F_5aa00 D_5aa00 F_5aa28 D_5aa28.
  - gauipc_ld_tac F_5aa04 D_5aa04 F_5aa2c D_5aa2c.
  - gauipc_ld_tac F_5aa08 D_5aa08 F_5aa30 D_5aa30.
  - gaddr2_tac F_5aa3c D_5aa3c F_5aa40 D_5aa40.
  - gauipc_ld_tac F_5aca8 D_5aca8 F_5acb8 D_5acb8.
  - gauipc_ld_tac F_c5cd8 D_c5cd8 F_c5ce0 D_c5ce0.
  - gauipc_ld_tac F_c5cdc D_c5cdc F_c5ce4 D_c5ce4.
  - gaddr2_tac F_c5ce8 D_c5ce8 F_c5cec D_c5cec.
  - litd 32%Z (0xc5cf0 : word). lit 1592%Z (0x5aef0 : word). gjal_tac F_c5cf0 D_c5cf0.
  - imm_norm. split; [vm_compute; reflexivity | lia].
  - imm_norm. split; [vm_compute; reflexivity | lia].
Qed.




End FPGen1.

