(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation BSEGS_I := ImgB.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_11d2f0 : bv 32 := 0x0053e2b3.
Lemma F_11d2f0 : fetch_word BSEGS_I (0x11d2f0 : word) = Some W_11d2f0.
Proof. vm_refl. Qed.
Lemma D_11d2f0 : decode_any W_11d2f0 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d2f4 : bv 32 := 0x00871393.
Lemma F_11d2f4 : fetch_word BSEGS_I (0x11d2f4 : word) = Some W_11d2f4.
Proof. vm_refl. Qed.
Lemma D_11d2f4 : decode_any W_11d2f4 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d2f8 : bv 32 := 0x0063e333.
Lemma F_11d2f8 : fetch_word BSEGS_I (0x11d2f8 : word) = Some W_11d2f8.
Proof. vm_refl. Qed.
Lemma D_11d2f8 : decode_any W_11d2f8 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d2fc : bv 32 := 0xff060613.
Lemma F_11d2fc : fetch_word BSEGS_I (0x11d2fc : word) = Some W_11d2fc.
Proof. vm_refl. Qed.
Lemma D_11d2fc : decode_any W_11d2fc = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d300 : bv 32 := 0x0106a023.
Lemma F_11d300 : fetch_word BSEGS_I (0x11d300 : word) = Some W_11d300.
Proof. vm_refl. Qed.
Lemma D_11d300 : decode_any W_11d300 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d304 : bv 32 := 0x0116a223.
Lemma F_11d304 : fetch_word BSEGS_I (0x11d304 : word) = Some W_11d304.
Proof. vm_refl. Qed.
Lemma D_11d304 : decode_any W_11d304 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d308 : bv 32 := 0x0056a423.
Lemma F_11d308 : fetch_word BSEGS_I (0x11d308 : word) = Some W_11d308.
Proof. vm_refl. Qed.
Lemma D_11d308 : decode_any W_11d308 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d30c : bv 32 := 0x0066a623.
Lemma F_11d30c : fetch_word BSEGS_I (0x11d30c : word) = Some W_11d30c.
Proof. vm_refl. Qed.
Lemma D_11d30c : decode_any W_11d30c = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d310 : bv 32 := 0x01068693.
Lemma F_11d310 : fetch_word BSEGS_I (0x11d310 : word) = Some W_11d310.
Proof. vm_refl. Qed.
Lemma D_11d310 : decode_any W_11d310 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d314 : bv 32 := 0x01058593.
Lemma F_11d314 : fetch_word BSEGS_I (0x11d314 : word) = Some W_11d314.
Proof. vm_refl. Qed.
Lemma D_11d314 : decode_any W_11d314 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d318 : bv 32 := 0xfac7e2e3.
Lemma F_11d318 : fetch_word BSEGS_I (0x11d318 : word) = Some W_11d318.
Proof. vm_refl. Qed.
Lemma D_11d318 : decode_any W_11d318 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d31c : bv 32 := 0xff358593.
Lemma F_11d31c : fetch_word BSEGS_I (0x11d31c : word) = Some W_11d31c.
Proof. vm_refl. Qed.
Lemma D_11d31c : decode_any W_11d31c = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d320 : bv 32 := 0x01000713.
Lemma F_11d320 : fetch_word BSEGS_I (0x11d320 : word) = Some W_11d320.
Proof. vm_refl. Qed.
Lemma D_11d320 : decode_any W_11d320 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d324 : bv 32 := 0xdae66ce3.
Lemma F_11d324 : fetch_word BSEGS_I (0x11d324 : word) = Some W_11d324.
Proof. vm_refl. Qed.
Lemma D_11d324 : decode_any W_11d324 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d328 : bv 32 := 0x0005c703.
Lemma F_11d328 : fetch_word BSEGS_I (0x11d328 : word) = Some W_11d328.
Proof. vm_refl. Qed.
Lemma D_11d328 : decode_any W_11d328 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d32c : bv 32 := 0x0015c783.
Lemma F_11d32c : fetch_word BSEGS_I (0x11d32c : word) = Some W_11d32c.
Proof. vm_refl. Qed.
Lemma D_11d32c : decode_any W_11d32c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d330 : bv 32 := 0x0025c803.
Lemma F_11d330 : fetch_word BSEGS_I (0x11d330 : word) = Some W_11d330.
Proof. vm_refl. Qed.
Lemma D_11d330 : decode_any W_11d330 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d334 : bv 32 := 0x0035c883.
Lemma F_11d334 : fetch_word BSEGS_I (0x11d334 : word) = Some W_11d334.
Proof. vm_refl. Qed.
Lemma D_11d334 : decode_any W_11d334 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d338 : bv 32 := 0x0045c283.
Lemma F_11d338 : fetch_word BSEGS_I (0x11d338 : word) = Some W_11d338.
Proof. vm_refl. Qed.
Lemma D_11d338 : decode_any W_11d338 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d33c : bv 32 := 0x0055c303.
Lemma F_11d33c : fetch_word BSEGS_I (0x11d33c : word) = Some W_11d33c.
Proof. vm_refl. Qed.
Lemma D_11d33c : decode_any W_11d33c = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d340 : bv 32 := 0x0065c383.
Lemma F_11d340 : fetch_word BSEGS_I (0x11d340 : word) = Some W_11d340.
Proof. vm_refl. Qed.
Lemma D_11d340 : decode_any W_11d340 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d344 : bv 32 := 0x0075ce03.
Lemma F_11d344 : fetch_word BSEGS_I (0x11d344 : word) = Some W_11d344.
Proof. vm_refl. Qed.
Lemma D_11d344 : decode_any W_11d344 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d348 : bv 32 := 0x00e68023.
Lemma F_11d348 : fetch_word BSEGS_I (0x11d348 : word) = Some W_11d348.
Proof. vm_refl. Qed.
Lemma D_11d348 : decode_any W_11d348 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d34c : bv 32 := 0x00f680a3.
Lemma F_11d34c : fetch_word BSEGS_I (0x11d34c : word) = Some W_11d34c.
Proof. vm_refl. Qed.
Lemma D_11d34c : decode_any W_11d34c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d350 : bv 32 := 0x01068123.
Lemma F_11d350 : fetch_word BSEGS_I (0x11d350 : word) = Some W_11d350.
Proof. vm_refl. Qed.
Lemma D_11d350 : decode_any W_11d350 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d354 : bv 32 := 0x011681a3.
Lemma F_11d354 : fetch_word BSEGS_I (0x11d354 : word) = Some W_11d354.
Proof. vm_refl. Qed.
Lemma D_11d354 : decode_any W_11d354 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d358 : bv 32 := 0x0085c703.
Lemma F_11d358 : fetch_word BSEGS_I (0x11d358 : word) = Some W_11d358.
Proof. vm_refl. Qed.
Lemma D_11d358 : decode_any W_11d358 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d35c : bv 32 := 0x0095c783.
Lemma F_11d35c : fetch_word BSEGS_I (0x11d35c : word) = Some W_11d35c.
Proof. vm_refl. Qed.
Lemma D_11d35c : decode_any W_11d35c = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d360 : bv 32 := 0x00a5c803.
Lemma F_11d360 : fetch_word BSEGS_I (0x11d360 : word) = Some W_11d360.
Proof. vm_refl. Qed.
Lemma D_11d360 : decode_any W_11d360 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d364 : bv 32 := 0x00b5c883.
Lemma F_11d364 : fetch_word BSEGS_I (0x11d364 : word) = Some W_11d364.
Proof. vm_refl. Qed.
Lemma D_11d364 : decode_any W_11d364 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d368 : bv 32 := 0x00568223.
Lemma F_11d368 : fetch_word BSEGS_I (0x11d368 : word) = Some W_11d368.
Proof. vm_refl. Qed.
Lemma D_11d368 : decode_any W_11d368 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d36c : bv 32 := 0x006682a3.
Lemma F_11d36c : fetch_word BSEGS_I (0x11d36c : word) = Some W_11d36c.
Proof. vm_refl. Qed.
Lemma D_11d36c : decode_any W_11d36c = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d370 : bv 32 := 0x00768323.
Lemma F_11d370 : fetch_word BSEGS_I (0x11d370 : word) = Some W_11d370.
Proof. vm_refl. Qed.
Lemma D_11d370 : decode_any W_11d370 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d374 : bv 32 := 0x01c683a3.
Lemma F_11d374 : fetch_word BSEGS_I (0x11d374 : word) = Some W_11d374.
Proof. vm_refl. Qed.
Lemma D_11d374 : decode_any W_11d374 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d378 : bv 32 := 0x00c5c283.
Lemma F_11d378 : fetch_word BSEGS_I (0x11d378 : word) = Some W_11d378.
Proof. vm_refl. Qed.
Lemma D_11d378 : decode_any W_11d378 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d37c : bv 32 := 0x00d5c303.
Lemma F_11d37c : fetch_word BSEGS_I (0x11d37c : word) = Some W_11d37c.
Proof. vm_refl. Qed.
Lemma D_11d37c : decode_any W_11d37c = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d380 : bv 32 := 0x00e5c383.
Lemma F_11d380 : fetch_word BSEGS_I (0x11d380 : word) = Some W_11d380.
Proof. vm_refl. Qed.
Lemma D_11d380 : decode_any W_11d380 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d384 : bv 32 := 0x00f5ce03.
Lemma F_11d384 : fetch_word BSEGS_I (0x11d384 : word) = Some W_11d384.
Proof. vm_refl. Qed.
Lemma D_11d384 : decode_any W_11d384 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d388 : bv 32 := 0x01058593.
Lemma F_11d388 : fetch_word BSEGS_I (0x11d388 : word) = Some W_11d388.
Proof. vm_refl. Qed.
Lemma D_11d388 : decode_any W_11d388 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d38c : bv 32 := 0x00e68423.
Lemma F_11d38c : fetch_word BSEGS_I (0x11d38c : word) = Some W_11d38c.
Proof. vm_refl. Qed.
Lemma D_11d38c : decode_any W_11d38c = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d390 : bv 32 := 0x00f684a3.
Lemma F_11d390 : fetch_word BSEGS_I (0x11d390 : word) = Some W_11d390.
Proof. vm_refl. Qed.
Lemma D_11d390 : decode_any W_11d390 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d394 : bv 32 := 0x01068523.
Lemma F_11d394 : fetch_word BSEGS_I (0x11d394 : word) = Some W_11d394.
Proof. vm_refl. Qed.
Lemma D_11d394 : decode_any W_11d394 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d398 : bv 32 := 0x011685a3.
Lemma F_11d398 : fetch_word BSEGS_I (0x11d398 : word) = Some W_11d398.
Proof. vm_refl. Qed.
Lemma D_11d398 : decode_any W_11d398 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d39c : bv 32 := 0x01068713.
Lemma F_11d39c : fetch_word BSEGS_I (0x11d39c : word) = Some W_11d39c.
Proof. vm_refl. Qed.
Lemma D_11d39c : decode_any W_11d39c = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d3a0 : bv 32 := 0x00568623.
Lemma F_11d3a0 : fetch_word BSEGS_I (0x11d3a0 : word) = Some W_11d3a0.
Proof. vm_refl. Qed.
Lemma D_11d3a0 : decode_any W_11d3a0 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d3a4 : bv 32 := 0x006686a3.
Lemma F_11d3a4 : fetch_word BSEGS_I (0x11d3a4 : word) = Some W_11d3a4.
Proof. vm_refl. Qed.
Lemma D_11d3a4 : decode_any W_11d3a4 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d3a8 : bv 32 := 0x00768723.
Lemma F_11d3a8 : fetch_word BSEGS_I (0x11d3a8 : word) = Some W_11d3a8.
Proof. vm_refl. Qed.
Lemma D_11d3a8 : decode_any W_11d3a8 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d3ac : bv 32 := 0x01c687a3.
Lemma F_11d3ac : fetch_word BSEGS_I (0x11d3ac : word) = Some W_11d3ac.
Proof. vm_refl. Qed.
Lemma D_11d3ac : decode_any W_11d3ac = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d3b0 : bv 32 := 0x00070693.
Lemma F_11d3b0 : fetch_word BSEGS_I (0x11d3b0 : word) = Some W_11d3b0.
Proof. vm_refl. Qed.
Lemma D_11d3b0 : decode_any W_11d3b0 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d3b4 : bv 32 := 0x00867713.
Lemma F_11d3b4 : fetch_word BSEGS_I (0x11d3b4 : word) = Some W_11d3b4.
Proof. vm_refl. Qed.
Lemma D_11d3b4 : decode_any W_11d3b4 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d3b8 : bv 32 := 0xd20706e3.
Lemma F_11d3b8 : fetch_word BSEGS_I (0x11d3b8 : word) = Some W_11d3b8.
Proof. vm_refl. Qed.
Lemma D_11d3b8 : decode_any W_11d3b8 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d3bc : bv 32 := 0x0005c703.
Lemma F_11d3bc : fetch_word BSEGS_I (0x11d3bc : word) = Some W_11d3bc.
Proof. vm_refl. Qed.
Lemma D_11d3bc : decode_any W_11d3bc = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d3c0 : bv 32 := 0x0015c783.
Lemma F_11d3c0 : fetch_word BSEGS_I (0x11d3c0 : word) = Some W_11d3c0.
Proof. vm_refl. Qed.
Lemma D_11d3c0 : decode_any W_11d3c0 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d3c4 : bv 32 := 0x0025c803.
Lemma F_11d3c4 : fetch_word BSEGS_I (0x11d3c4 : word) = Some W_11d3c4.
Proof. vm_refl. Qed.
Lemma D_11d3c4 : decode_any W_11d3c4 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d3c8 : bv 32 := 0x0035c883.
Lemma F_11d3c8 : fetch_word BSEGS_I (0x11d3c8 : word) = Some W_11d3c8.
Proof. vm_refl. Qed.
Lemma D_11d3c8 : decode_any W_11d3c8 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d3cc : bv 32 := 0x0045c283.
Lemma F_11d3cc : fetch_word BSEGS_I (0x11d3cc : word) = Some W_11d3cc.
Proof. vm_refl. Qed.
Lemma D_11d3cc : decode_any W_11d3cc = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d3d0 : bv 32 := 0x0055c303.
Lemma F_11d3d0 : fetch_word BSEGS_I (0x11d3d0 : word) = Some W_11d3d0.
Proof. vm_refl. Qed.
Lemma D_11d3d0 : decode_any W_11d3d0 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d3d4 : bv 32 := 0x0065c383.
Lemma F_11d3d4 : fetch_word BSEGS_I (0x11d3d4 : word) = Some W_11d3d4.
Proof. vm_refl. Qed.
Lemma D_11d3d4 : decode_any W_11d3d4 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d3d8 : bv 32 := 0x0075ce03.
Lemma F_11d3d8 : fetch_word BSEGS_I (0x11d3d8 : word) = Some W_11d3d8.
Proof. vm_refl. Qed.
Lemma D_11d3d8 : decode_any W_11d3d8 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d3dc : bv 32 := 0x00858593.
Lemma F_11d3dc : fetch_word BSEGS_I (0x11d3dc : word) = Some W_11d3dc.
Proof. vm_refl. Qed.
Lemma D_11d3dc : decode_any W_11d3dc = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d3e0 : bv 32 := 0x00e68023.
Lemma F_11d3e0 : fetch_word BSEGS_I (0x11d3e0 : word) = Some W_11d3e0.
Proof. vm_refl. Qed.
Lemma D_11d3e0 : decode_any W_11d3e0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d3e4 : bv 32 := 0x00f680a3.
Lemma F_11d3e4 : fetch_word BSEGS_I (0x11d3e4 : word) = Some W_11d3e4.
Proof. vm_refl. Qed.
Lemma D_11d3e4 : decode_any W_11d3e4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d3e8 : bv 32 := 0x01068123.
Lemma F_11d3e8 : fetch_word BSEGS_I (0x11d3e8 : word) = Some W_11d3e8.
Proof. vm_refl. Qed.
Lemma D_11d3e8 : decode_any W_11d3e8 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d3ec : bv 32 := 0x011681a3.
Lemma F_11d3ec : fetch_word BSEGS_I (0x11d3ec : word) = Some W_11d3ec.
Proof. vm_refl. Qed.
Lemma D_11d3ec : decode_any W_11d3ec = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d3f0 : bv 32 := 0x00868713.
Lemma F_11d3f0 : fetch_word BSEGS_I (0x11d3f0 : word) = Some W_11d3f0.
Proof. vm_refl. Qed.
Lemma D_11d3f0 : decode_any W_11d3f0 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d3f4 : bv 32 := 0x00568223.
Lemma F_11d3f4 : fetch_word BSEGS_I (0x11d3f4 : word) = Some W_11d3f4.
Proof. vm_refl. Qed.
Lemma D_11d3f4 : decode_any W_11d3f4 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d3f8 : bv 32 := 0x006682a3.
Lemma F_11d3f8 : fetch_word BSEGS_I (0x11d3f8 : word) = Some W_11d3f8.
Proof. vm_refl. Qed.
Lemma D_11d3f8 : decode_any W_11d3f8 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d3fc : bv 32 := 0x00768323.
Lemma F_11d3fc : fetch_word BSEGS_I (0x11d3fc : word) = Some W_11d3fc.
Proof. vm_refl. Qed.
Lemma D_11d3fc : decode_any W_11d3fc = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d400 : bv 32 := 0x01c683a3.
Lemma F_11d400 : fetch_word BSEGS_I (0x11d400 : word) = Some W_11d400.
Proof. vm_refl. Qed.
Lemma D_11d400 : decode_any W_11d400 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d404 : bv 32 := 0x00070693.
Lemma F_11d404 : fetch_word BSEGS_I (0x11d404 : word) = Some W_11d404.
Proof. vm_refl. Qed.
Lemma D_11d404 : decode_any W_11d404 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d408 : bv 32 := 0x00467713.
Lemma F_11d408 : fetch_word BSEGS_I (0x11d408 : word) = Some W_11d408.
Proof. vm_refl. Qed.
Lemma D_11d408 : decode_any W_11d408 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d40c : bv 32 := 0x02070863.
Lemma F_11d40c : fetch_word BSEGS_I (0x11d40c : word) = Some W_11d40c.
Proof. vm_refl. Qed.
Lemma D_11d40c : decode_any W_11d40c = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d410 : bv 32 := 0x0005c703.
Lemma F_11d410 : fetch_word BSEGS_I (0x11d410 : word) = Some W_11d410.
Proof. vm_refl. Qed.
Lemma D_11d410 : decode_any W_11d410 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d414 : bv 32 := 0x0015c783.
Lemma F_11d414 : fetch_word BSEGS_I (0x11d414 : word) = Some W_11d414.
Proof. vm_refl. Qed.
Lemma D_11d414 : decode_any W_11d414 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d418 : bv 32 := 0x0025c803.
Lemma F_11d418 : fetch_word BSEGS_I (0x11d418 : word) = Some W_11d418.
Proof. vm_refl. Qed.
Lemma D_11d418 : decode_any W_11d418 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d41c : bv 32 := 0x0035c883.
Lemma F_11d41c : fetch_word BSEGS_I (0x11d41c : word) = Some W_11d41c.
Proof. vm_refl. Qed.
Lemma D_11d41c : decode_any W_11d41c = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d420 : bv 32 := 0x00458593.
Lemma F_11d420 : fetch_word BSEGS_I (0x11d420 : word) = Some W_11d420.
Proof. vm_refl. Qed.
Lemma D_11d420 : decode_any W_11d420 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d424 : bv 32 := 0x00468293.
Lemma F_11d424 : fetch_word BSEGS_I (0x11d424 : word) = Some W_11d424.
Proof. vm_refl. Qed.
Lemma D_11d424 : decode_any W_11d424 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d428 : bv 32 := 0x00e68023.
Lemma F_11d428 : fetch_word BSEGS_I (0x11d428 : word) = Some W_11d428.
Proof. vm_refl. Qed.
Lemma D_11d428 : decode_any W_11d428 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d42c : bv 32 := 0x00f680a3.
Lemma F_11d42c : fetch_word BSEGS_I (0x11d42c : word) = Some W_11d42c.
Proof. vm_refl. Qed.
Lemma D_11d42c : decode_any W_11d42c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d430 : bv 32 := 0x01068123.
Lemma F_11d430 : fetch_word BSEGS_I (0x11d430 : word) = Some W_11d430.
Proof. vm_refl. Qed.
Lemma D_11d430 : decode_any W_11d430 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d434 : bv 32 := 0x011681a3.
Lemma F_11d434 : fetch_word BSEGS_I (0x11d434 : word) = Some W_11d434.
Proof. vm_refl. Qed.
Lemma D_11d434 : decode_any W_11d434 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d438 : bv 32 := 0x00028693.
Lemma F_11d438 : fetch_word BSEGS_I (0x11d438 : word) = Some W_11d438.
Proof. vm_refl. Qed.
Lemma D_11d438 : decode_any W_11d438 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d43c : bv 32 := 0x00267713.
Lemma F_11d43c : fetch_word BSEGS_I (0x11d43c : word) = Some W_11d43c.
Proof. vm_refl. Qed.
Lemma D_11d43c : decode_any W_11d43c = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d440 : bv 32 := 0x00071863.
Lemma F_11d440 : fetch_word BSEGS_I (0x11d440 : word) = Some W_11d440.
Proof. vm_refl. Qed.
Lemma D_11d440 : decode_any W_11d440 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d444 : bv 32 := 0x00167613.
Lemma F_11d444 : fetch_word BSEGS_I (0x11d444 : word) = Some W_11d444.
Proof. vm_refl. Qed.
Lemma D_11d444 : decode_any W_11d444 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d448 : bv 32 := 0x02061663.
Lemma F_11d448 : fetch_word BSEGS_I (0x11d448 : word) = Some W_11d448.
Proof. vm_refl. Qed.
Lemma D_11d448 : decode_any W_11d448 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d44c : bv 32 := 0x00008067.
Lemma F_11d44c : fetch_word BSEGS_I (0x11d44c : word) = Some W_11d44c.
Proof. vm_refl. Qed.
Lemma D_11d44c : decode_any W_11d44c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d450 : bv 32 := 0x0005c703.
Lemma F_11d450 : fetch_word BSEGS_I (0x11d450 : word) = Some W_11d450.
Proof. vm_refl. Qed.
Lemma D_11d450 : decode_any W_11d450 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d454 : bv 32 := 0x0015c783.
Lemma F_11d454 : fetch_word BSEGS_I (0x11d454 : word) = Some W_11d454.
Proof. vm_refl. Qed.
Lemma D_11d454 : decode_any W_11d454 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d458 : bv 32 := 0x00258593.
Lemma F_11d458 : fetch_word BSEGS_I (0x11d458 : word) = Some W_11d458.
Proof. vm_refl. Qed.
Lemma D_11d458 : decode_any W_11d458 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d45c : bv 32 := 0x00268813.
Lemma F_11d45c : fetch_word BSEGS_I (0x11d45c : word) = Some W_11d45c.
Proof. vm_refl. Qed.
Lemma D_11d45c : decode_any W_11d45c = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d460 : bv 32 := 0x00e68023.
Lemma F_11d460 : fetch_word BSEGS_I (0x11d460 : word) = Some W_11d460.
Proof. vm_refl. Qed.
Lemma D_11d460 : decode_any W_11d460 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d464 : bv 32 := 0x00f680a3.
Lemma F_11d464 : fetch_word BSEGS_I (0x11d464 : word) = Some W_11d464.
Proof. vm_refl. Qed.
Lemma D_11d464 : decode_any W_11d464 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d468 : bv 32 := 0x00080693.
Lemma F_11d468 : fetch_word BSEGS_I (0x11d468 : word) = Some W_11d468.
Proof. vm_refl. Qed.
Lemma D_11d468 : decode_any W_11d468 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d46c : bv 32 := 0x00167613.
Lemma F_11d46c : fetch_word BSEGS_I (0x11d46c : word) = Some W_11d46c.
Proof. vm_refl. Qed.
Lemma D_11d46c : decode_any W_11d46c = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d470 : bv 32 := 0xfc060ee3.
Lemma F_11d470 : fetch_word BSEGS_I (0x11d470 : word) = Some W_11d470.
Proof. vm_refl. Qed.
Lemma D_11d470 : decode_any W_11d470 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d474 : bv 32 := 0x0005c583.
Lemma F_11d474 : fetch_word BSEGS_I (0x11d474 : word) = Some W_11d474.
Proof. vm_refl. Qed.
Lemma D_11d474 : decode_any W_11d474 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d478 : bv 32 := 0x00b68023.
Lemma F_11d478 : fetch_word BSEGS_I (0x11d478 : word) = Some W_11d478.
Proof. vm_refl. Qed.
Lemma D_11d478 : decode_any W_11d478 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d47c : bv 32 := 0x00008067.
Lemma F_11d47c : fetch_word BSEGS_I (0x11d47c : word) = Some W_11d47c.
Proof. vm_refl. Qed.
Lemma D_11d47c : decode_any W_11d47c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d480 : bv 32 := 0x0e060a63.
Lemma F_11d480 : fetch_word BSEGS_I (0x11d480 : word) = Some W_11d480.
Proof. vm_refl. Qed.
Lemma D_11d480 : decode_any W_11d480 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d484 : bv 32 := 0x00b50023.
Lemma F_11d484 : fetch_word BSEGS_I (0x11d484 : word) = Some W_11d484.
Proof. vm_refl. Qed.
Lemma D_11d484 : decode_any W_11d484 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d488 : bv 32 := 0x00c506b3.
Lemma F_11d488 : fetch_word BSEGS_I (0x11d488 : word) = Some W_11d488.
Proof. vm_refl. Qed.
Lemma D_11d488 : decode_any W_11d488 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d48c : bv 32 := 0x00300713.
Lemma F_11d48c : fetch_word BSEGS_I (0x11d48c : word) = Some W_11d48c.
Proof. vm_refl. Qed.
Lemma D_11d48c : decode_any W_11d48c = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d490 : bv 32 := 0xfeb68fa3.
Lemma F_11d490 : fetch_word BSEGS_I (0x11d490 : word) = Some W_11d490.
Proof. vm_refl. Qed.
Lemma D_11d490 : decode_any W_11d490 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d494 : bv 32 := 0x0ee66063.
Lemma F_11d494 : fetch_word BSEGS_I (0x11d494 : word) = Some W_11d494.
Proof. vm_refl. Qed.
Lemma D_11d494 : decode_any W_11d494 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d498 : bv 32 := 0x00b500a3.
Lemma F_11d498 : fetch_word BSEGS_I (0x11d498 : word) = Some W_11d498.
Proof. vm_refl. Qed.
Lemma D_11d498 : decode_any W_11d498 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d49c : bv 32 := 0x00b50123.
Lemma F_11d49c : fetch_word BSEGS_I (0x11d49c : word) = Some W_11d49c.
Proof. vm_refl. Qed.
Lemma D_11d49c : decode_any W_11d49c = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d4a0 : bv 32 := 0x00700713.
Lemma F_11d4a0 : fetch_word BSEGS_I (0x11d4a0 : word) = Some W_11d4a0.
Proof. vm_refl. Qed.
Lemma D_11d4a0 : decode_any W_11d4a0 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d4a4 : bv 32 := 0xfeb68ea3.
Lemma F_11d4a4 : fetch_word BSEGS_I (0x11d4a4 : word) = Some W_11d4a4.
Proof. vm_refl. Qed.
Lemma D_11d4a4 : decode_any W_11d4a4 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d4a8 : bv 32 := 0xfeb68f23.
Lemma F_11d4a8 : fetch_word BSEGS_I (0x11d4a8 : word) = Some W_11d4a8.
Proof. vm_refl. Qed.
Lemma D_11d4a8 : decode_any W_11d4a8 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d4ac : bv 32 := 0x0ce66463.
Lemma F_11d4ac : fetch_word BSEGS_I (0x11d4ac : word) = Some W_11d4ac.
Proof. vm_refl. Qed.
Lemma D_11d4ac : decode_any W_11d4ac = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d4b0 : bv 32 := 0x00b501a3.
Lemma F_11d4b0 : fetch_word BSEGS_I (0x11d4b0 : word) = Some W_11d4b0.
Proof. vm_refl. Qed.
Lemma D_11d4b0 : decode_any W_11d4b0 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d4b4 : bv 32 := 0x00900793.
Lemma F_11d4b4 : fetch_word BSEGS_I (0x11d4b4 : word) = Some W_11d4b4.
Proof. vm_refl. Qed.
Lemma D_11d4b4 : decode_any W_11d4b4 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d4b8 : bv 32 := 0xfeb68e23.
Lemma F_11d4b8 : fetch_word BSEGS_I (0x11d4b8 : word) = Some W_11d4b8.
Proof. vm_refl. Qed.
Lemma D_11d4b8 : decode_any W_11d4b8 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d4bc : bv 32 := 0x0af66c63.
Lemma F_11d4bc : fetch_word BSEGS_I (0x11d4bc : word) = Some W_11d4bc.
Proof. vm_refl. Qed.
Lemma D_11d4bc : decode_any W_11d4bc = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d4c0 : bv 32 := 0x40a006bb.
Lemma F_11d4c0 : fetch_word BSEGS_I (0x11d4c0 : word) = Some W_11d4c0.
Proof. vm_refl. Qed.
Lemma D_11d4c0 : decode_any W_11d4c0 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d4c4 : bv 32 := 0x03859813.
Lemma F_11d4c4 : fetch_word BSEGS_I (0x11d4c4 : word) = Some W_11d4c4.
Proof. vm_refl. Qed.
Lemma D_11d4c4 : decode_any W_11d4c4 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d4c8 : bv 32 := 0x101015b7.
Lemma F_11d4c8 : fetch_word BSEGS_I (0x11d4c8 : word) = Some W_11d4c8.
Proof. vm_refl. Qed.
Lemma D_11d4c8 : decode_any W_11d4c8 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d4cc : bv 32 := 0x0036f693.
Lemma F_11d4cc : fetch_word BSEGS_I (0x11d4cc : word) = Some W_11d4cc.
Proof. vm_refl. Qed.
Lemma D_11d4cc : decode_any W_11d4cc = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d4d0 : bv 32 := 0x00459713.
Lemma F_11d4d0 : fetch_word BSEGS_I (0x11d4d0 : word) = Some W_11d4d0.
Proof. vm_refl. Qed.
Lemma D_11d4d0 : decode_any W_11d4d0 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d4d4 : bv 32 := 0x40d60633.
Lemma F_11d4d4 : fetch_word BSEGS_I (0x11d4d4 : word) = Some W_11d4d4.
Proof. vm_refl. Qed.
Lemma D_11d4d4 : decode_any W_11d4d4 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d4d8 : bv 32 := 0x00d505b3.
Lemma F_11d4d8 : fetch_word BSEGS_I (0x11d4d8 : word) = Some W_11d4d8.
Proof. vm_refl. Qed.
Lemma D_11d4d8 : decode_any W_11d4d8 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d4dc : bv 32 := 0x10070693.
Lemma F_11d4dc : fetch_word BSEGS_I (0x11d4dc : word) = Some W_11d4dc.
Proof. vm_refl. Qed.
Lemma D_11d4dc : decode_any W_11d4dc = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d4e0 : bv 32 := 0xffc67713.
Lemma F_11d4e0 : fetch_word BSEGS_I (0x11d4e0 : word) = Some W_11d4e0.
Proof. vm_refl. Qed.
Lemma D_11d4e0 : decode_any W_11d4e0 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d4e4 : bv 32 := 0x02d83633.
Lemma F_11d4e4 : fetch_word BSEGS_I (0x11d4e4 : word) = Some W_11d4e4.
Proof. vm_refl. Qed.
Lemma D_11d4e4 : decode_any W_11d4e4 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d4e8 : bv 32 := 0x00c5a023.
Lemma F_11d4e8 : fetch_word BSEGS_I (0x11d4e8 : word) = Some W_11d4e8.
Proof. vm_refl. Qed.
Lemma D_11d4e8 : decode_any W_11d4e8 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d4ec : bv 32 := 0x00e586b3.
Lemma F_11d4ec : fetch_word BSEGS_I (0x11d4ec : word) = Some W_11d4ec.
Proof. vm_refl. Qed.
Lemma D_11d4ec : decode_any W_11d4ec = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d4f0 : bv 32 := 0xfec6ae23.
Lemma F_11d4f0 : fetch_word BSEGS_I (0x11d4f0 : word) = Some W_11d4f0.
Proof. vm_refl. Qed.
Lemma D_11d4f0 : decode_any W_11d4f0 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d4f4 : bv 32 := 0x08f76063.
Lemma F_11d4f4 : fetch_word BSEGS_I (0x11d4f4 : word) = Some W_11d4f4.
Proof. vm_refl. Qed.
Lemma D_11d4f4 : decode_any W_11d4f4 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d4f8 : bv 32 := 0x00c5a223.
Lemma F_11d4f8 : fetch_word BSEGS_I (0x11d4f8 : word) = Some W_11d4f8.
Proof. vm_refl. Qed.
Lemma D_11d4f8 : decode_any W_11d4f8 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d4fc : bv 32 := 0x00c5a423.
Lemma F_11d4fc : fetch_word BSEGS_I (0x11d4fc : word) = Some W_11d4fc.
Proof. vm_refl. Qed.
Lemma D_11d4fc : decode_any W_11d4fc = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d500 : bv 32 := 0x01900793.
Lemma F_11d500 : fetch_word BSEGS_I (0x11d500 : word) = Some W_11d500.
Proof. vm_refl. Qed.
Lemma D_11d500 : decode_any W_11d500 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d504 : bv 32 := 0xfec6aa23.
Lemma F_11d504 : fetch_word BSEGS_I (0x11d504 : word) = Some W_11d504.
Proof. vm_refl. Qed.
Lemma D_11d504 : decode_any W_11d504 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d508 : bv 32 := 0xfec6ac23.
Lemma F_11d508 : fetch_word BSEGS_I (0x11d508 : word) = Some W_11d508.
Proof. vm_refl. Qed.
Lemma D_11d508 : decode_any W_11d508 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d50c : bv 32 := 0x06f76463.
Lemma F_11d50c : fetch_word BSEGS_I (0x11d50c : word) = Some W_11d50c.
Proof. vm_refl. Qed.
Lemma D_11d50c : decode_any W_11d50c = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d510 : bv 32 := 0x00c5a623.
Lemma F_11d510 : fetch_word BSEGS_I (0x11d510 : word) = Some W_11d510.
Proof. vm_refl. Qed.
Lemma D_11d510 : decode_any W_11d510 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d514 : bv 32 := 0x00c5a823.
Lemma F_11d514 : fetch_word BSEGS_I (0x11d514 : word) = Some W_11d514.
Proof. vm_refl. Qed.
Lemma D_11d514 : decode_any W_11d514 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d518 : bv 32 := 0x00c5aa23.
Lemma F_11d518 : fetch_word BSEGS_I (0x11d518 : word) = Some W_11d518.
Proof. vm_refl. Qed.
Lemma D_11d518 : decode_any W_11d518 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d51c : bv 32 := 0x00c5ac23.
Lemma F_11d51c : fetch_word BSEGS_I (0x11d51c : word) = Some W_11d51c.
Proof. vm_refl. Qed.
Lemma D_11d51c : decode_any W_11d51c = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d520 : bv 32 := 0x0045f793.
Lemma F_11d520 : fetch_word BSEGS_I (0x11d520 : word) = Some W_11d520.
Proof. vm_refl. Qed.
Lemma D_11d520 : decode_any W_11d520 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d524 : bv 32 := 0x02000813.
Lemma F_11d524 : fetch_word BSEGS_I (0x11d524 : word) = Some W_11d524.
Proof. vm_refl. Qed.
Lemma D_11d524 : decode_any W_11d524 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d528 : bv 32 := 0x01878793.
Lemma F_11d528 : fetch_word BSEGS_I (0x11d528 : word) = Some W_11d528.
Proof. vm_refl. Qed.
Lemma D_11d528 : decode_any W_11d528 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d52c : bv 32 := 0x40f70733.
Lemma F_11d52c : fetch_word BSEGS_I (0x11d52c : word) = Some W_11d52c.
Proof. vm_refl. Qed.
Lemma D_11d52c : decode_any W_11d52c = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d530 : bv 32 := 0xfec6a223.
Lemma F_11d530 : fetch_word BSEGS_I (0x11d530 : word) = Some W_11d530.
Proof. vm_refl. Qed.
Lemma D_11d530 : decode_any W_11d530 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d534 : bv 32 := 0xfec6a423.
Lemma F_11d534 : fetch_word BSEGS_I (0x11d534 : word) = Some W_11d534.
Proof. vm_refl. Qed.
Lemma D_11d534 : decode_any W_11d534 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d538 : bv 32 := 0xfec6a623.
Lemma F_11d538 : fetch_word BSEGS_I (0x11d538 : word) = Some W_11d538.
Proof. vm_refl. Qed.
Lemma D_11d538 : decode_any W_11d538 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d53c : bv 32 := 0xfec6a823.
Lemma F_11d53c : fetch_word BSEGS_I (0x11d53c : word) = Some W_11d53c.
Proof. vm_refl. Qed.
Lemma D_11d53c : decode_any W_11d53c = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d540 : bv 32 := 0x03076a63.
Lemma F_11d540 : fetch_word BSEGS_I (0x11d540 : word) = Some W_11d540.
Proof. vm_refl. Qed.
Lemma D_11d540 : decode_any W_11d540 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d544 : bv 32 := 0x02061613.
Lemma F_11d544 : fetch_word BSEGS_I (0x11d544 : word) = Some W_11d544.
Proof. vm_refl. Qed.
Lemma D_11d544 : decode_any W_11d544 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d548 : bv 32 := 0x00f585b3.
Lemma F_11d548 : fetch_word BSEGS_I (0x11d548 : word) = Some W_11d548.
Proof. vm_refl. Qed.
Lemma D_11d548 : decode_any W_11d548 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d54c : bv 32 := 0x02065693.
Lemma F_11d54c : fetch_word BSEGS_I (0x11d54c : word) = Some W_11d54c.
Proof. vm_refl. Qed.
Lemma D_11d54c : decode_any W_11d54c = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d550 : bv 32 := 0x00d66633.
Lemma F_11d550 : fetch_word BSEGS_I (0x11d550 : word) = Some W_11d550.
Proof. vm_refl. Qed.
Lemma D_11d550 : decode_any W_11d550 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d554 : bv 32 := 0x01f00693.
Lemma F_11d554 : fetch_word BSEGS_I (0x11d554 : word) = Some W_11d554.
Proof. vm_refl. Qed.
Lemma D_11d554 : decode_any W_11d554 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d558 : bv 32 := 0x00c5b023.
Lemma F_11d558 : fetch_word BSEGS_I (0x11d558 : word) = Some W_11d558.
Proof. vm_refl. Qed.
Lemma D_11d558 : decode_any W_11d558 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d55c : bv 32 := 0x00c5b423.
Lemma F_11d55c : fetch_word BSEGS_I (0x11d55c : word) = Some W_11d55c.
Proof. vm_refl. Qed.
Lemma D_11d55c : decode_any W_11d55c = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d560 : bv 32 := 0x00c5b823.
Lemma F_11d560 : fetch_word BSEGS_I (0x11d560 : word) = Some W_11d560.
Proof. vm_refl. Qed.
Lemma D_11d560 : decode_any W_11d560 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d564 : bv 32 := 0x00c5bc23.
Lemma F_11d564 : fetch_word BSEGS_I (0x11d564 : word) = Some W_11d564.
Proof. vm_refl. Qed.
Lemma D_11d564 : decode_any W_11d564 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d568 : bv 32 := 0xfe070713.
Lemma F_11d568 : fetch_word BSEGS_I (0x11d568 : word) = Some W_11d568.
Proof. vm_refl. Qed.
Lemma D_11d568 : decode_any W_11d568 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d56c : bv 32 := 0x02058593.
Lemma F_11d56c : fetch_word BSEGS_I (0x11d56c : word) = Some W_11d56c.
Proof. vm_refl. Qed.
Lemma D_11d56c : decode_any W_11d56c = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d570 : bv 32 := 0xfee6e4e3.
Lemma F_11d570 : fetch_word BSEGS_I (0x11d570 : word) = Some W_11d570.
Proof. vm_refl. Qed.
Lemma D_11d570 : decode_any W_11d570 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11d574 : bv 32 := 0x00008067.
Lemma F_11d574 : fetch_word BSEGS_I (0x11d574 : word) = Some W_11d574.
Proof. vm_refl. Qed.
Lemma D_11d574 : decode_any W_11d574 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
