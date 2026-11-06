(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_68b2c : bv 32 := 0x0a842787.
Lemma F_68b2c : fetch_word Ubsan.M.loaded_segments (0x68b6c : word) = Some W_68b2c.
Proof. vm_refl. Qed.
Lemma D_68b2c : decode_any W_68b2c = Some (FLoad FMT_S 15 8 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_68b3c : bv 32 := 0xd0357753.
Lemma F_68b3c : fetch_word Ubsan.M.loaded_segments (0x68b7c : word) = Some W_68b3c.
Proof. vm_refl. Qed.
Lemma D_68b3c : decode_any W_68b3c = Some (Fcvt FC_S FC_LU 14 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_68b44 : bv 32 := 0xd03c76d3.
Lemma F_68b44 : fetch_word Ubsan.M.loaded_segments (0x68b84 : word) = Some W_68b44.
Proof. vm_refl. Qed.
Lemma D_68b44 : decode_any W_68b44 = Some (Fcvt FC_S FC_LU 13 24 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_68b48 : bv 32 := 0x10d7f6d3.
Lemma F_68b48 : fetch_word Ubsan.M.loaded_segments (0x68b88 : word) = Some W_68b48.
Proof. vm_refl. Qed.
Lemma D_68b48 : decode_any W_68b48 = Some (Fari F_MUL FMT_S 13 15 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_68b4c : bv 32 := 0xa0e69553.
Lemma F_68b4c : fetch_word Ubsan.M.loaded_segments (0x68b8c : word) = Some W_68b4c.
Proof. vm_refl. Qed.
Lemma D_68b4c : decode_any W_68b4c = Some (Fcmp F_LT FMT_S 10 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_68b70 : bv 32 := 0x18f777d3.
Lemma F_68b70 : fetch_word Ubsan.M.loaded_segments (0x68bb0 : word) = Some W_68b70.
Proof. vm_refl. Qed.
Lemma D_68b70 : decode_any W_68b70 = Some (Fari F_DIV FMT_S 15 14 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_68b74 : bv 32 := 0x20f7a753.
Lemma F_68b74 : fetch_word Ubsan.M.loaded_segments (0x68bb4 : word) = Some W_68b74.
Proof. vm_refl. Qed.
Lemma D_68b74 : decode_any W_68b74 = Some (Fsgnj F_SGNJX FMT_S 14 15 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_68b78 : bv 32 := 0xa08715d3.
Lemma F_68b78 : fetch_word Ubsan.M.loaded_segments (0x68bb8 : word) = Some W_68b78.
Proof. vm_refl. Qed.
Lemma D_68b78 : decode_any W_68b78 = Some (Fcmp F_LT FMT_S 11 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_68b80 : bv 32 := 0xc007b5d3.
Lemma F_68b80 : fetch_word Ubsan.M.loaded_segments (0x68bc0 : word) = Some W_68b80.
Proof. vm_refl. Qed.
Lemma D_68b80 : decode_any W_68b80 = Some (Fcvt FC_W FC_S 11 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_68b84 : bv 32 := 0xd005b753.
Lemma F_68b84 : fetch_word Ubsan.M.loaded_segments (0x68bc4 : word) = Some W_68b84.
Proof. vm_refl. Qed.
Lemma D_68b84 : decode_any W_68b84 = Some (Fcvt FC_S FC_W 14 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_68b88 : bv 32 := 0x20f707d3.
Lemma F_68b88 : fetch_word Ubsan.M.loaded_segments (0x68bc8 : word) = Some W_68b88.
Proof. vm_refl. Qed.
Lemma D_68b88 : decode_any W_68b88 = Some (Fsgnj F_SGNJ FMT_S 15 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_68b8c : bv 32 := 0xa0f495d3.
Lemma F_68b8c : fetch_word Ubsan.M.loaded_segments (0x68bcc : word) = Some W_68b8c.
Proof. vm_refl. Qed.
Lemma D_68b8c : decode_any W_68b8c = Some (Fcmp F_LT FMT_S 11 9 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_68b94 : bv 32 := 0xa12795d3.
Lemma F_68b94 : fetch_word Ubsan.M.loaded_segments (0x68bd4 : word) = Some W_68b94.
Proof. vm_refl. Qed.
Lemma D_68b94 : decode_any W_68b94 = Some (Fcmp F_LT FMT_S 11 15 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_68ba4 : bv 32 := 0xc0379553.
Lemma F_68ba4 : fetch_word Ubsan.M.loaded_segments (0x68be4 : word) = Some W_68ba4.
Proof. vm_refl. Qed.
Lemma D_68ba4 : decode_any W_68ba4 = Some (Fcvt FC_LU FC_S 10 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_68f60 : bv 32 := 0x03db5613.

Definition W_68f64 : bv 32 := 0x12061a63.

Definition W_68f68 : bv 32 := 0x12a5e863.

Definition W_68f6c : bv 32 := 0x12050663.

Definition W_68f70 : bv 32 := 0x0075f613.

Definition W_68f74 : bv 32 := 0x12061263.

Definition W_68f78 : bv 32 := 0x0005b603.

Definition W_68f7c : bv 32 := 0x00060e63.

Definition W_68f80 : bv 32 := 0x00767513.

Definition W_68f84 : bv 32 := 0x10051a63.

Definition W_68f88 : bv 32 := 0x00063503.

Definition W_68f8c : bv 32 := 0x00adb023.

Definition W_68f90 : bv 32 := 0x01b63023.

Definition W_68f94 : bv 32 := 0x08c0006f.

Definition W_68f98 : bv 32 := 0x02813683.

Definition W_68f9c : bv 32 := 0x0006b603.

Definition W_68fa0 : bv 32 := 0x01b6b023.

Definition W_68fa4 : bv 32 := 0x00cdb023.

Definition W_68fa8 : bv 32 := 0x0e058863.

Definition W_68fac : bv 32 := 0x00d5b023.

Definition W_68fb0 : bv 32 := 0x000db583.

Definition W_68fb4 : bv 32 := 0x06058663.

Definition W_68fb8 : bv 32 := 0x0075f613.

Definition W_68fbc : bv 32 := 0x0c061e63.

Definition W_68fc0 : bv 32 := 0x0085b583.

Definition W_68fc4 : bv 32 := 0xfffc0613.

Definition W_68fc8 : bv 32 := 0x00cc76b3.

Definition W_68fcc : bv 32 := 0x02069263.

Definition W_68fd0 : bv 32 := 0x00c5f5b3.

Definition W_68fd4 : bv 32 := 0x0240006f.

Definition W_68fd8 : bv 32 := 0x000d0793.

Definition W_68fe0 : bv 32 := 0x000b8b13.

Definition W_68fe4 : bv 32 := 0xf61ff06f.

Definition W_68fe8 : bv 32 := 0x038bfb33.

Definition W_68fec : bv 32 := 0xf59ff06f.

Definition W_69000 : bv 32 := 0x08061c63.

Definition W_69004 : bv 32 := 0x00359593.

Definition W_69008 : bv 32 := 0xfff54613.

Definition W_6900c : bv 32 := 0x08b66663.

Definition W_69010 : bv 32 := 0x00b50533.

Definition W_69014 : bv 32 := 0x00757593.

Definition W_69018 : bv 32 := 0x08059063.

Definition W_6901c : bv 32 := 0x01b53023.

Definition W_69020 : bv 32 := 0x0a043503.

Definition W_69024 : bv 32 := 0x00150513.

Definition W_69028 : bv 32 := 0x0aa43023.

Definition W_6902c : bv 32 := 0x01013503.

Definition W_69030 : bv 32 := 0x00adaa23.

Definition W_69034 : bv 32 := 0x00813503.

Definition W_69038 : bv 32 := 0x00adac23.

Definition W_6903c : bv 32 := 0x00fdae23.

Definition W_69040 : bv 32 := 0x0d843503.

