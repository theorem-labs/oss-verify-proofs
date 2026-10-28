(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_5d3c8 : bv 32 := 0xf7010113.
Lemma F_5d3c8 : fetch_word AsanUbsan.M.loaded_segments (0x5d7e0 : word) = Some W_5d3c8.
Proof. vm_refl. Qed.
Lemma D_5d3c8 : decode_any W_5d3c8 = Some (OpImm ALU_ADD 2 2 3952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3cc : bv 32 := 0x08113423.
Lemma F_5d3cc : fetch_word AsanUbsan.M.loaded_segments (0x5d7e4 : word) = Some W_5d3cc.
Proof. vm_refl. Qed.
Lemma D_5d3cc : decode_any W_5d3cc = Some (Store SZ8 2 1 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3d0 : bv 32 := 0x08813023.
Lemma F_5d3d0 : fetch_word AsanUbsan.M.loaded_segments (0x5d7e8 : word) = Some W_5d3d0.
Proof. vm_refl. Qed.
Lemma D_5d3d0 : decode_any W_5d3d0 = Some (Store SZ8 2 8 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3d4 : bv 32 := 0x06913c23.
Lemma F_5d3d4 : fetch_word AsanUbsan.M.loaded_segments (0x5d7ec : word) = Some W_5d3d4.
Proof. vm_refl. Qed.
Lemma D_5d3d4 : decode_any W_5d3d4 = Some (Store SZ8 2 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3d8 : bv 32 := 0x07213823.
Lemma F_5d3d8 : fetch_word AsanUbsan.M.loaded_segments (0x5d7f0 : word) = Some W_5d3d8.
Proof. vm_refl. Qed.
Lemma D_5d3d8 : decode_any W_5d3d8 = Some (Store SZ8 2 18 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3dc : bv 32 := 0x07313423.
Lemma F_5d3dc : fetch_word AsanUbsan.M.loaded_segments (0x5d7f4 : word) = Some W_5d3dc.
Proof. vm_refl. Qed.
Lemma D_5d3dc : decode_any W_5d3dc = Some (Store SZ8 2 19 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3e0 : bv 32 := 0x07413023.
Lemma F_5d3e0 : fetch_word AsanUbsan.M.loaded_segments (0x5d7f8 : word) = Some W_5d3e0.
Proof. vm_refl. Qed.
Lemma D_5d3e0 : decode_any W_5d3e0 = Some (Store SZ8 2 20 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3e4 : bv 32 := 0x05513c23.
Lemma F_5d3e4 : fetch_word AsanUbsan.M.loaded_segments (0x5d7fc : word) = Some W_5d3e4.
Proof. vm_refl. Qed.
Lemma D_5d3e4 : decode_any W_5d3e4 = Some (Store SZ8 2 21 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3e8 : bv 32 := 0x05613823.
Lemma F_5d3e8 : fetch_word AsanUbsan.M.loaded_segments (0x5d800 : word) = Some W_5d3e8.
Proof. vm_refl. Qed.
Lemma D_5d3e8 : decode_any W_5d3e8 = Some (Store SZ8 2 22 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3ec : bv 32 := 0x05713423.
Lemma F_5d3ec : fetch_word AsanUbsan.M.loaded_segments (0x5d804 : word) = Some W_5d3ec.
Proof. vm_refl. Qed.
Lemma D_5d3ec : decode_any W_5d3ec = Some (Store SZ8 2 23 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3f0 : bv 32 := 0x05813023.
Lemma F_5d3f0 : fetch_word AsanUbsan.M.loaded_segments (0x5d808 : word) = Some W_5d3f0.
Proof. vm_refl. Qed.
Lemma D_5d3f0 : decode_any W_5d3f0 = Some (Store SZ8 2 24 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3f4 : bv 32 := 0x03913c23.
Lemma F_5d3f4 : fetch_word AsanUbsan.M.loaded_segments (0x5d80c : word) = Some W_5d3f4.
Proof. vm_refl. Qed.
Lemma D_5d3f4 : decode_any W_5d3f4 = Some (Store SZ8 2 25 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3f8 : bv 32 := 0x03a13823.
Lemma F_5d3f8 : fetch_word AsanUbsan.M.loaded_segments (0x5d810 : word) = Some W_5d3f8.
Proof. vm_refl. Qed.
Lemma D_5d3f8 : decode_any W_5d3f8 = Some (Store SZ8 2 26 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d3fc : bv 32 := 0x03b13423.
Lemma F_5d3fc : fetch_word AsanUbsan.M.loaded_segments (0x5d814 : word) = Some W_5d3fc.
Proof. vm_refl. Qed.
Lemma D_5d3fc : decode_any W_5d3fc = Some (Store SZ8 2 27 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d400 : bv 32 := 0x00058493.
Lemma F_5d400 : fetch_word AsanUbsan.M.loaded_segments (0x5d818 : word) = Some W_5d400.
Proof. vm_refl. Qed.
Lemma D_5d400 : decode_any W_5d400 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d404 : bv 32 := 0x00050c93.
Lemma F_5d404 : fetch_word AsanUbsan.M.loaded_segments (0x5d81c : word) = Some W_5d404.
Proof. vm_refl. Qed.
Lemma D_5d404 : decode_any W_5d404 = Some (OpImm ALU_ADD 25 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d408 : bv 32 := 0x0c4260ef.
Lemma F_5d408 : fetch_word AsanUbsan.M.loaded_segments (0x5d820 : word) = Some W_5d408.
Proof. vm_refl. Qed.
Lemma D_5d408 : decode_any W_5d408 = Some (Jal 1 155844, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d40c : bv 32 := 0x26050463.
Lemma F_5d40c : fetch_word AsanUbsan.M.loaded_segments (0x5d824 : word) = Some W_5d40c.
Proof. vm_refl. Qed.
Lemma D_5d40c : decode_any W_5d40c = Some (Branch BC_EQ 10 0 616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d410 : bv 32 := 0x00050913.
Lemma F_5d410 : fetch_word AsanUbsan.M.loaded_segments (0x5d828 : word) = Some W_5d410.
Proof. vm_refl. Qed.
Lemma D_5d410 : decode_any W_5d410 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d414 : bv 32 := 0x27c260ef.
Lemma F_5d414 : fetch_word AsanUbsan.M.loaded_segments (0x5d82c : word) = Some W_5d414.
Proof. vm_refl. Qed.
Lemma D_5d414 : decode_any W_5d414 = Some (Jal 1 156284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d418 : bv 32 := 0x00050993.
Lemma F_5d418 : fetch_word AsanUbsan.M.loaded_segments (0x5d830 : word) = Some W_5d418.
Proof. vm_refl. Qed.
Lemma D_5d418 : decode_any W_5d418 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d41c : bv 32 := 0x00090513.
Lemma F_5d41c : fetch_word AsanUbsan.M.loaded_segments (0x5d834 : word) = Some W_5d41c.
Proof. vm_refl. Qed.
Lemma D_5d41c : decode_any W_5d41c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d420 : bv 32 := 0x2c8260ef.
Lemma F_5d420 : fetch_word AsanUbsan.M.loaded_segments (0x5d838 : word) = Some W_5d420.
Proof. vm_refl. Qed.
Lemma D_5d420 : decode_any W_5d420 = Some (Jal 1 156360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d424 : bv 32 := 0x2499e863.
Lemma F_5d424 : fetch_word AsanUbsan.M.loaded_segments (0x5d83c : word) = Some W_5d424.
Proof. vm_refl. Qed.
Lemma D_5d424 : decode_any W_5d424 = Some (Branch BC_LTU 19 9 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d428 : bv 32 := 0x00050913.
Lemma F_5d428 : fetch_word AsanUbsan.M.loaded_segments (0x5d840 : word) = Some W_5d428.
Proof. vm_refl. Qed.
Lemma D_5d428 : decode_any W_5d428 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d42c : bv 32 := 0x24a4e463.
Lemma F_5d42c : fetch_word AsanUbsan.M.loaded_segments (0x5d844 : word) = Some W_5d42c.
Proof. vm_refl. Qed.
Lemma D_5d42c : decode_any W_5d42c = Some (Branch BC_LTU 9 10 584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d430 : bv 32 := 0x00000d13.
Lemma F_5d430 : fetch_word AsanUbsan.M.loaded_segments (0x5d848 : word) = Some W_5d430.
Proof. vm_refl. Qed.
Lemma D_5d430 : decode_any W_5d430 = Some (OpImm ALU_ADD 26 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d434 : bv 32 := 0x00001437.
Lemma F_5d434 : fetch_word AsanUbsan.M.loaded_segments (0x5d84c : word) = Some W_5d434.
Proof. vm_refl. Qed.
Lemma D_5d434 : decode_any W_5d434 = Some (Lui 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d438 : bv 32 := 0x000da517.
Lemma F_5d438 : fetch_word AsanUbsan.M.loaded_segments (0x5d850 : word) = Some W_5d438.
Proof. vm_refl. Qed.
Lemma D_5d438 : decode_any W_5d438 = Some (Auipc 10 218, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d43c : bv 32 := 0x000da597.
Lemma F_5d43c : fetch_word AsanUbsan.M.loaded_segments (0x5d854 : word) = Some W_5d43c.
Proof. vm_refl. Qed.
Lemma D_5d43c : decode_any W_5d43c = Some (Auipc 11 218, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d440 : bv 32 := 0x000da617.
Lemma F_5d440 : fetch_word AsanUbsan.M.loaded_segments (0x5d858 : word) = Some W_5d440.
Proof. vm_refl. Qed.
Lemma D_5d440 : decode_any W_5d440 = Some (Auipc 12 218, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d444 : bv 32 := 0x000da697.
Lemma F_5d444 : fetch_word AsanUbsan.M.loaded_segments (0x5d85c : word) = Some W_5d444.
Proof. vm_refl. Qed.
Lemma D_5d444 : decode_any W_5d444 = Some (Auipc 13 218, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d448 : bv 32 := 0x000da717.
Lemma F_5d448 : fetch_word AsanUbsan.M.loaded_segments (0x5d860 : word) = Some W_5d448.
Proof. vm_refl. Qed.
Lemma D_5d448 : decode_any W_5d448 = Some (Auipc 14 218, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d44c : bv 32 := 0xfffb3797.
Lemma F_5d44c : fetch_word AsanUbsan.M.loaded_segments (0x5d864 : word) = Some W_5d44c.
Proof. vm_refl. Qed.
Lemma D_5d44c : decode_any W_5d44c = Some (Auipc 15 1048499, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d450 : bv 32 := 0x008c8433.
Lemma F_5d450 : fetch_word AsanUbsan.M.loaded_segments (0x5d868 : word) = Some W_5d450.
Proof. vm_refl. Qed.
Lemma D_5d450 : decode_any W_5d450 = Some (Op ALU_ADD 8 25 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d454 : bv 32 := 0xc7053b03.
Lemma F_5d454 : fetch_word AsanUbsan.M.loaded_segments (0x5d86c : word) = Some W_5d454.
Proof. vm_refl. Qed.
Lemma D_5d454 : decode_any W_5d454 = Some (Load SZ8 true 22 10 3184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d458 : bv 32 := 0xc745b503.
Lemma F_5d458 : fetch_word AsanUbsan.M.loaded_segments (0x5d870 : word) = Some W_5d458.
Proof. vm_refl. Qed.
Lemma D_5d458 : decode_any W_5d458 = Some (Load SZ8 true 10 11 3188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d45c : bv 32 := 0x00a13c23.
Lemma F_5d45c : fetch_word AsanUbsan.M.loaded_segments (0x5d874 : word) = Some W_5d45c.
Proof. vm_refl. Qed.
Lemma D_5d45c : decode_any W_5d45c = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d460 : bv 32 := 0xc7863503.
Lemma F_5d460 : fetch_word AsanUbsan.M.loaded_segments (0x5d878 : word) = Some W_5d460.
Proof. vm_refl. Qed.
Lemma D_5d460 : decode_any W_5d460 = Some (Load SZ8 true 10 12 3192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d464 : bv 32 := 0x00a13823.
Lemma F_5d464 : fetch_word AsanUbsan.M.loaded_segments (0x5d87c : word) = Some W_5d464.
Proof. vm_refl. Qed.
Lemma D_5d464 : decode_any W_5d464 = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d468 : bv 32 := 0xc7c6b503.
Lemma F_5d468 : fetch_word AsanUbsan.M.loaded_segments (0x5d880 : word) = Some W_5d468.
Proof. vm_refl. Qed.
Lemma D_5d468 : decode_any W_5d468 = Some (Load SZ8 true 10 13 3196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d46c : bv 32 := 0x00a13423.
Lemma F_5d46c : fetch_word AsanUbsan.M.loaded_segments (0x5d884 : word) = Some W_5d46c.
Proof. vm_refl. Qed.
Lemma D_5d46c : decode_any W_5d46c = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d470 : bv 32 := 0xc5873503.
Lemma F_5d470 : fetch_word AsanUbsan.M.loaded_segments (0x5d888 : word) = Some W_5d470.
Proof. vm_refl. Qed.
Lemma D_5d470 : decode_any W_5d470 = Some (Load SZ8 true 10 14 3160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d474 : bv 32 := 0x00a13023.
Lemma F_5d474 : fetch_word AsanUbsan.M.loaded_segments (0x5d88c : word) = Some W_5d474.
Proof. vm_refl. Qed.
Lemma D_5d474 : decode_any W_5d474 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d478 : bv 32 := 0xb1c7bb83.
Lemma F_5d478 : fetch_word AsanUbsan.M.loaded_segments (0x5d890 : word) = Some W_5d478.
Proof. vm_refl. Qed.
Lemma D_5d478 : decode_any W_5d478 = Some (Load SZ8 true 23 15 2844, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d47c : bv 32 := 0x00100393.
Lemma F_5d47c : fetch_word AsanUbsan.M.loaded_segments (0x5d894 : word) = Some W_5d47c.
Proof. vm_refl. Qed.
Lemma D_5d47c : decode_any W_5d47c = Some (OpImm ALU_ADD 7 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d480 : bv 32 := 0x00600e13.
Lemma F_5d480 : fetch_word AsanUbsan.M.loaded_segments (0x5d898 : word) = Some W_5d480.
Proof. vm_refl. Qed.
Lemma D_5d480 : decode_any W_5d480 = Some (OpImm ALU_ADD 28 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d484 : bv 32 := 0x00000a13.
Lemma F_5d484 : fetch_word AsanUbsan.M.loaded_segments (0x5d89c : word) = Some W_5d484.
Proof. vm_refl. Qed.
Lemma D_5d484 : decode_any W_5d484 = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d488 : bv 32 := 0x0100006f.
Lemma F_5d488 : fetch_word AsanUbsan.M.loaded_segments (0x5d8a0 : word) = Some W_5d488.
Proof. vm_refl. Qed.
Lemma D_5d488 : decode_any W_5d488 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d48c : bv 32 := 0x001a0a13.
Lemma F_5d48c : fetch_word AsanUbsan.M.loaded_segments (0x5d8a4 : word) = Some W_5d48c.
Proof. vm_refl. Qed.
Lemma D_5d48c : decode_any W_5d48c = Some (OpImm ALU_ADD 20 20 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d490 : bv 32 := 0x00b00513.
Lemma F_5d490 : fetch_word AsanUbsan.M.loaded_segments (0x5d8a8 : word) = Some W_5d490.
Proof. vm_refl. Qed.
Lemma D_5d490 : decode_any W_5d490 = Some (OpImm ALU_ADD 10 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d494 : bv 32 := 0x1caa0e63.
Lemma F_5d494 : fetch_word AsanUbsan.M.loaded_segments (0x5d8ac : word) = Some W_5d494.
Proof. vm_refl. Qed.
Lemma D_5d494 : decode_any W_5d494 = Some (Branch BC_EQ 20 10 476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d498 : bv 32 := 0x00000d93.
Lemma F_5d498 : fetch_word AsanUbsan.M.loaded_segments (0x5d8b0 : word) = Some W_5d498.
Proof. vm_refl. Qed.
Lemma D_5d498 : decode_any W_5d498 = Some (OpImm ALU_ADD 27 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d49c : bv 32 := 0x058cb503.
Lemma F_5d49c : fetch_word AsanUbsan.M.loaded_segments (0x5d8b4 : word) = Some W_5d49c.
Proof. vm_refl. Qed.
Lemma D_5d49c : decode_any W_5d49c = Some (Load SZ8 true 10 25 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4a0 : bv 32 := 0x00a00593.
Lemma F_5d4a0 : fetch_word AsanUbsan.M.loaded_segments (0x5d8b8 : word) = Some W_5d4a0.
Proof. vm_refl. Qed.
Lemma D_5d4a0 : decode_any W_5d4a0 = Some (OpImm ALU_ADD 11 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4a4 : bv 32 := 0x414585bb.
Lemma F_5d4a4 : fetch_word AsanUbsan.M.loaded_segments (0x5d8bc : word) = Some W_5d4a4.
Proof. vm_refl. Qed.
Lemma D_5d4a4 : decode_any W_5d4a4 = Some (Op32 ALU_SUB 11 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4a8 : bv 32 := 0x006a0a93.
Lemma F_5d4a8 : fetch_word AsanUbsan.M.loaded_segments (0x5d8c0 : word) = Some W_5d4a8.
Proof. vm_refl. Qed.
Lemma D_5d4a8 : decode_any W_5d4a8 = Some (OpImm ALU_ADD 21 20 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4ac : bv 32 := 0xfff00613.
Lemma F_5d4ac : fetch_word AsanUbsan.M.loaded_segments (0x5d8c4 : word) = Some W_5d4ac.
Proof. vm_refl. Qed.
Lemma D_5d4ac : decode_any W_5d4ac = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4b0 : bv 32 := 0x00b615b3.
Lemma F_5d4b0 : fetch_word AsanUbsan.M.loaded_segments (0x5d8c8 : word) = Some W_5d4b0.
Proof. vm_refl. Qed.
Lemma D_5d4b0 : decode_any W_5d4b0 = Some (Op ALU_SLL 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4b4 : bv 32 := 0x3ff5f593.
Lemma F_5d4b4 : fetch_word AsanUbsan.M.loaded_segments (0x5d8cc : word) = Some W_5d4b4.
Proof. vm_refl. Qed.
Lemma D_5d4b4 : decode_any W_5d4b4 = Some (OpImm ALU_AND 11 11 1023, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4b8 : bv 32 := 0xff150613.
Lemma F_5d4b8 : fetch_word AsanUbsan.M.loaded_segments (0x5d8d0 : word) = Some W_5d4b8.
Proof. vm_refl. Qed.
Lemma D_5d4b8 : decode_any W_5d4b8 = Some (OpImm ALU_ADD 12 10 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4bc : bv 32 := 0x414509b3.
Lemma F_5d4bc : fetch_word AsanUbsan.M.loaded_segments (0x5d8d4 : word) = Some W_5d4bc.
Proof. vm_refl. Qed.
Lemma D_5d4bc : decode_any W_5d4bc = Some (Op ALU_SUB 19 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4c0 : bv 32 := 0x00c59c33.
Lemma F_5d4c0 : fetch_word AsanUbsan.M.loaded_segments (0x5d8d8 : word) = Some W_5d4c0.
Proof. vm_refl. Qed.
Lemma D_5d4c0 : decode_any W_5d4c0 = Some (Op ALU_SLL 24 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4c4 : bv 32 := 0xffa98993.
Lemma F_5d4c4 : fetch_word AsanUbsan.M.loaded_segments (0x5d8dc : word) = Some W_5d4c4.
Proof. vm_refl. Qed.
Lemma D_5d4c4 : decode_any W_5d4c4 = Some (OpImm ALU_ADD 19 19 4090, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4c8 : bv 32 := 0x01840c33.
Lemma F_5d4c8 : fetch_word AsanUbsan.M.loaded_segments (0x5d8e0 : word) = Some W_5d4c8.
Proof. vm_refl. Qed.
Lemma D_5d4c8 : decode_any W_5d4c8 = Some (Op ALU_ADD 24 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4cc : bv 32 := 0x04000513.
Lemma F_5d4cc : fetch_word AsanUbsan.M.loaded_segments (0x5d8e4 : word) = Some W_5d4cc.
Proof. vm_refl. Qed.
Lemma D_5d4cc : decode_any W_5d4cc = Some (OpImm ALU_ADD 10 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4d0 : bv 32 := 0x01451533.
Lemma F_5d4d0 : fetch_word AsanUbsan.M.loaded_segments (0x5d8e8 : word) = Some W_5d4d0.
Proof. vm_refl. Qed.
Lemma D_5d4d0 : decode_any W_5d4d0 = Some (Op ALU_SLL 10 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4d4 : bv 32 := 0x02a13023.
Lemma F_5d4d4 : fetch_word AsanUbsan.M.loaded_segments (0x5d8ec : word) = Some W_5d4d4.
Proof. vm_refl. Qed.
Lemma D_5d4d4 : decode_any W_5d4d4 = Some (Store SZ8 2 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4d8 : bv 32 := 0x0240006f.
Lemma F_5d4d8 : fetch_word AsanUbsan.M.loaded_segments (0x5d8f0 : word) = Some W_5d4d8.
Proof. vm_refl. Qed.
Lemma D_5d4d8 : decode_any W_5d4d8 = Some (Jal 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4f0 : bv 32 := 0x001d8d93.
Lemma F_5d4f0 : fetch_word AsanUbsan.M.loaded_segments (0x5d908 : word) = Some W_5d4f0.
Proof. vm_refl. Qed.
Lemma D_5d4f0 : decode_any W_5d4f0 = Some (OpImm ALU_ADD 27 27 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4f4 : bv 32 := 0x013dd533.
Lemma F_5d4f4 : fetch_word AsanUbsan.M.loaded_segments (0x5d90c : word) = Some W_5d4f4.
Proof. vm_refl. Qed.
Lemma D_5d4f4 : decode_any W_5d4f4 = Some (Op ALU_SRL 10 27 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4f8 : bv 32 := 0xf8051ae3.
Lemma F_5d4f8 : fetch_word AsanUbsan.M.loaded_segments (0x5d910 : word) = Some W_5d4f8.
Proof. vm_refl. Qed.
Lemma D_5d4f8 : decode_any W_5d4f8 = Some (Branch BC_NE 10 0 8084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4fc : bv 32 := 0x01bc05b3.
Lemma F_5d4fc : fetch_word AsanUbsan.M.loaded_segments (0x5d914 : word) = Some W_5d4fc.
Proof. vm_refl. Qed.
Lemma D_5d4fc : decode_any W_5d4fc = Some (Op ALU_ADD 11 24 27, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d500 : bv 32 := 0x0005c503.
Lemma F_5d500 : fetch_word AsanUbsan.M.loaded_segments (0x5d918 : word) = Some W_5d500.
Proof. vm_refl. Qed.
Lemma D_5d500 : decode_any W_5d500 = Some (Load SZ1 false 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d504 : bv 32 := 0xfe0506e3.
Lemma F_5d504 : fetch_word AsanUbsan.M.loaded_segments (0x5d91c : word) = Some W_5d504.
Proof. vm_refl. Qed.
Lemma D_5d504 : decode_any W_5d504 = Some (Branch BC_EQ 10 0 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d508 : bv 32 := 0x058cb503.
Lemma F_5d508 : fetch_word AsanUbsan.M.loaded_segments (0x5d920 : word) = Some W_5d508.
Proof. vm_refl. Qed.
Lemma D_5d508 : decode_any W_5d508 = Some (Load SZ8 true 10 25 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d50c : bv 32 := 0xffb50613.
Lemma F_5d50c : fetch_word AsanUbsan.M.loaded_segments (0x5d924 : word) = Some W_5d50c.
Proof. vm_refl. Qed.
Lemma D_5d50c : decode_any W_5d50c = Some (OpImm ALU_ADD 12 10 4091, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d510 : bv 32 := 0x00aa1533.
Lemma F_5d510 : fetch_word AsanUbsan.M.loaded_segments (0x5d928 : word) = Some W_5d510.
Proof. vm_refl. Qed.
Lemma D_5d510 : decode_any W_5d510 = Some (Op ALU_SLL 10 20 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d514 : bv 32 := 0x00c39633.
Lemma F_5d514 : fetch_word AsanUbsan.M.loaded_segments (0x5d92c : word) = Some W_5d514.
Proof. vm_refl. Qed.
Lemma D_5d514 : decode_any W_5d514 = Some (Op ALU_SLL 12 7 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d518 : bv 32 := 0x00a40533.
Lemma F_5d518 : fetch_word AsanUbsan.M.loaded_segments (0x5d930 : word) = Some W_5d518.
Proof. vm_refl. Qed.
Lemma D_5d518 : decode_any W_5d518 = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d51c : bv 32 := 0x00c50533.
Lemma F_5d51c : fetch_word AsanUbsan.M.loaded_segments (0x5d934 : word) = Some W_5d51c.
Proof. vm_refl. Qed.
Lemma D_5d51c : decode_any W_5d51c = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d520 : bv 32 := 0x015d9633.
Lemma F_5d520 : fetch_word AsanUbsan.M.loaded_segments (0x5d938 : word) = Some W_5d520.
Proof. vm_refl. Qed.
Lemma D_5d520 : decode_any W_5d520 = Some (Op ALU_SLL 12 27 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d524 : bv 32 := 0x00c50533.
Lemma F_5d524 : fetch_word AsanUbsan.M.loaded_segments (0x5d93c : word) = Some W_5d524.
Proof. vm_refl. Qed.
Lemma D_5d524 : decode_any W_5d524 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d528 : bv 32 := 0x01853603.
Lemma F_5d528 : fetch_word AsanUbsan.M.loaded_segments (0x5d940 : word) = Some W_5d528.
Proof. vm_refl. Qed.
Lemma D_5d528 : decode_any W_5d528 = Some (Load SZ8 true 12 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d52c : bv 32 := 0xfcc972e3.
Lemma F_5d52c : fetch_word AsanUbsan.M.loaded_segments (0x5d944 : word) = Some W_5d52c.
Proof. vm_refl. Qed.
Lemma D_5d52c : decode_any W_5d52c = Some (Branch BC_GEU 18 12 8132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d530 : bv 32 := 0xfc9670e3.
Lemma F_5d530 : fetch_word AsanUbsan.M.loaded_segments (0x5d948 : word) = Some W_5d530.
Proof. vm_refl. Qed.
Lemma D_5d530 : decode_any W_5d530 = Some (Branch BC_GEU 12 9 8128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d534 : bv 32 := 0x01a58023.
Lemma F_5d534 : fetch_word AsanUbsan.M.loaded_segments (0x5d94c : word) = Some W_5d534.
Proof. vm_refl. Qed.
Lemma D_5d534 : decode_any W_5d534 = Some (Store SZ1 11 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d538 : bv 32 := 0x000b3583.
Lemma F_5d538 : fetch_word AsanUbsan.M.loaded_segments (0x5d950 : word) = Some W_5d538.
Proof. vm_refl. Qed.
Lemma D_5d538 : decode_any W_5d538 = Some (Load SZ8 true 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d53c : bv 32 := 0xfff58613.
Lemma F_5d53c : fetch_word AsanUbsan.M.loaded_segments (0x5d954 : word) = Some W_5d53c.
Proof. vm_refl. Qed.
Lemma D_5d53c : decode_any W_5d53c = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d540 : bv 32 := 0x00c5b6b3.
Lemma F_5d540 : fetch_word AsanUbsan.M.loaded_segments (0x5d958 : word) = Some W_5d540.
Proof. vm_refl. Qed.
Lemma D_5d540 : decode_any W_5d540 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d544 : bv 32 := 0xfff68693.
Lemma F_5d544 : fetch_word AsanUbsan.M.loaded_segments (0x5d95c : word) = Some W_5d544.
Proof. vm_refl. Qed.
Lemma D_5d544 : decode_any W_5d544 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d548 : bv 32 := 0x00c6f6b3.
Lemma F_5d548 : fetch_word AsanUbsan.M.loaded_segments (0x5d960 : word) = Some W_5d548.
Proof. vm_refl. Qed.
Lemma D_5d548 : decode_any W_5d548 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d54c : bv 32 := 0x02a6fc63.
Lemma F_5d54c : fetch_word AsanUbsan.M.loaded_segments (0x5d964 : word) = Some W_5d54c.
Proof. vm_refl. Qed.
Lemma D_5d54c : decode_any W_5d54c = Some (Branch BC_GEU 13 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d550 : bv 32 := 0x01813683.
Lemma F_5d550 : fetch_word AsanUbsan.M.loaded_segments (0x5d968 : word) = Some W_5d550.
Proof. vm_refl. Qed.
Lemma D_5d550 : decode_any W_5d550 = Some (Load SZ8 true 13 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d554 : bv 32 := 0x0006b803.
Lemma F_5d554 : fetch_word AsanUbsan.M.loaded_segments (0x5d96c : word) = Some W_5d554.
Proof. vm_refl. Qed.
Lemma D_5d554 : decode_any W_5d554 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d558 : bv 32 := 0x01013683.
Lemma F_5d558 : fetch_word AsanUbsan.M.loaded_segments (0x5d970 : word) = Some W_5d558.
Proof. vm_refl. Qed.
Lemma D_5d558 : decode_any W_5d558 = Some (Load SZ8 true 13 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d55c : bv 32 := 0x0006b683.
Lemma F_5d55c : fetch_word AsanUbsan.M.loaded_segments (0x5d974 : word) = Some W_5d55c.
Proof. vm_refl. Qed.
Lemma D_5d55c : decode_any W_5d55c = Some (Load SZ8 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d560 : bv 32 := 0xfff80793.
Lemma F_5d560 : fetch_word AsanUbsan.M.loaded_segments (0x5d978 : word) = Some W_5d560.
Proof. vm_refl. Qed.
Lemma D_5d560 : decode_any W_5d560 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d564 : bv 32 := 0x00a7f463.
Lemma F_5d564 : fetch_word AsanUbsan.M.loaded_segments (0x5d97c : word) = Some W_5d564.
Proof. vm_refl. Qed.
Lemma D_5d564 : decode_any W_5d564 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d56c : bv 32 := 0x00813703.
Lemma F_5d56c : fetch_word AsanUbsan.M.loaded_segments (0x5d984 : word) = Some W_5d56c.
Proof. vm_refl. Qed.
Lemma D_5d56c : decode_any W_5d56c = Some (Load SZ8 true 14 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d570 : bv 32 := 0x00073283.
Lemma F_5d570 : fetch_word AsanUbsan.M.loaded_segments (0x5d988 : word) = Some W_5d570.
Proof. vm_refl. Qed.
Lemma D_5d570 : decode_any W_5d570 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d574 : bv 32 := 0x0032d713.
Lemma F_5d574 : fetch_word AsanUbsan.M.loaded_segments (0x5d98c : word) = Some W_5d574.
Proof. vm_refl. Qed.
Lemma D_5d574 : decode_any W_5d574 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d578 : bv 32 := 0x00b708b3.
Lemma F_5d578 : fetch_word AsanUbsan.M.loaded_segments (0x5d990 : word) = Some W_5d578.
Proof. vm_refl. Qed.
Lemma D_5d578 : decode_any W_5d578 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d57c : bv 32 := 0x02a2e863.
Lemma F_5d57c : fetch_word AsanUbsan.M.loaded_segments (0x5d994 : word) = Some W_5d57c.
Proof. vm_refl. Qed.
Lemma D_5d57c : decode_any W_5d57c = Some (Branch BC_LTU 5 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d580 : bv 32 := 0x02a8f663.
Lemma F_5d580 : fetch_word AsanUbsan.M.loaded_segments (0x5d998 : word) = Some W_5d580.
Proof. vm_refl. Qed.
Lemma D_5d580 : decode_any W_5d580 = Some (Branch BC_GEU 17 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d584 : bv 32 := 0xf54e6ce3.
Lemma F_5d584 : fetch_word AsanUbsan.M.loaded_segments (0x5d99c : word) = Some W_5d584.
Proof. vm_refl. Qed.
Lemma D_5d584 : decode_any W_5d584 = Some (Branch BC_LTU 28 20 8024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d588 : bv 32 := 0x00355513.
Lemma F_5d588 : fetch_word AsanUbsan.M.loaded_segments (0x5d9a0 : word) = Some W_5d588.
Proof. vm_refl. Qed.
Lemma D_5d588 : decode_any W_5d588 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d58c : bv 32 := 0x00a585b3.
Lemma F_5d58c : fetch_word AsanUbsan.M.loaded_segments (0x5d9a4 : word) = Some W_5d58c.
Proof. vm_refl. Qed.
Lemma D_5d58c : decode_any W_5d58c = Some (Op ALU_ADD 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d590 : bv 32 := 0x00100513.
Lemma F_5d590 : fetch_word AsanUbsan.M.loaded_segments (0x5d9a8 : word) = Some W_5d590.
Proof. vm_refl. Qed.
Lemma D_5d590 : decode_any W_5d590 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d594 : bv 32 := 0x0175b023.
Lemma F_5d594 : fetch_word AsanUbsan.M.loaded_segments (0x5d9ac : word) = Some W_5d594.
Proof. vm_refl. Qed.
Lemma D_5d594 : decode_any W_5d594 = Some (Store SZ8 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d598 : bv 32 := 0x01455633.
Lemma F_5d598 : fetch_word AsanUbsan.M.loaded_segments (0x5d9b0 : word) = Some W_5d598.
Proof. vm_refl. Qed.
Lemma D_5d598 : decode_any W_5d598 = Some (Op ALU_SRL 12 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d59c : bv 32 := 0x00858593.
Lemma F_5d59c : fetch_word AsanUbsan.M.loaded_segments (0x5d9b4 : word) = Some W_5d59c.
Proof. vm_refl. Qed.
Lemma D_5d59c : decode_any W_5d59c = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5a0 : bv 32 := 0x00150513.
Lemma F_5d5a0 : fetch_word AsanUbsan.M.loaded_segments (0x5d9b8 : word) = Some W_5d5a0.
Proof. vm_refl. Qed.
Lemma D_5d5a0 : decode_any W_5d5a0 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5a4 : bv 32 := 0xfe0608e3.
Lemma F_5d5a4 : fetch_word AsanUbsan.M.loaded_segments (0x5d9bc : word) = Some W_5d5a4.
Proof. vm_refl. Qed.
Lemma D_5d5a4 : decode_any W_5d5a4 = Some (Branch BC_EQ 12 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5a8 : bv 32 := 0xf49ff06f.
Lemma F_5d5a8 : fetch_word AsanUbsan.M.loaded_segments (0x5d9c0 : word) = Some W_5d5a8.
Proof. vm_refl. Qed.
Lemma D_5d5a8 : decode_any W_5d5a8 = Some (Jal 0 2096968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d670 : bv 32 := 0x060c8023.
Lemma F_5d670 : fetch_word AsanUbsan.M.loaded_segments (0x5da88 : word) = Some W_5d670.
Proof. vm_refl. Qed.
Lemma D_5d670 : decode_any W_5d670 = Some (Store SZ1 25 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d674 : bv 32 := 0x08813083.
Lemma F_5d674 : fetch_word AsanUbsan.M.loaded_segments (0x5da8c : word) = Some W_5d674.
Proof. vm_refl. Qed.
Lemma D_5d674 : decode_any W_5d674 = Some (Load SZ8 true 1 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d678 : bv 32 := 0x08013403.
Lemma F_5d678 : fetch_word AsanUbsan.M.loaded_segments (0x5da90 : word) = Some W_5d678.
Proof. vm_refl. Qed.
Lemma D_5d678 : decode_any W_5d678 = Some (Load SZ8 true 8 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d67c : bv 32 := 0x07813483.
Lemma F_5d67c : fetch_word AsanUbsan.M.loaded_segments (0x5da94 : word) = Some W_5d67c.
Proof. vm_refl. Qed.
Lemma D_5d67c : decode_any W_5d67c = Some (Load SZ8 true 9 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d680 : bv 32 := 0x07013903.
Lemma F_5d680 : fetch_word AsanUbsan.M.loaded_segments (0x5da98 : word) = Some W_5d680.
Proof. vm_refl. Qed.
Lemma D_5d680 : decode_any W_5d680 = Some (Load SZ8 true 18 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d684 : bv 32 := 0x06813983.
Lemma F_5d684 : fetch_word AsanUbsan.M.loaded_segments (0x5da9c : word) = Some W_5d684.
Proof. vm_refl. Qed.
Lemma D_5d684 : decode_any W_5d684 = Some (Load SZ8 true 19 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d688 : bv 32 := 0x06013a03.
Lemma F_5d688 : fetch_word AsanUbsan.M.loaded_segments (0x5daa0 : word) = Some W_5d688.
Proof. vm_refl. Qed.
Lemma D_5d688 : decode_any W_5d688 = Some (Load SZ8 true 20 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d68c : bv 32 := 0x05813a83.
Lemma F_5d68c : fetch_word AsanUbsan.M.loaded_segments (0x5daa4 : word) = Some W_5d68c.
Proof. vm_refl. Qed.
Lemma D_5d68c : decode_any W_5d68c = Some (Load SZ8 true 21 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d690 : bv 32 := 0x05013b03.
Lemma F_5d690 : fetch_word AsanUbsan.M.loaded_segments (0x5daa8 : word) = Some W_5d690.
Proof. vm_refl. Qed.
Lemma D_5d690 : decode_any W_5d690 = Some (Load SZ8 true 22 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d694 : bv 32 := 0x04813b83.
Lemma F_5d694 : fetch_word AsanUbsan.M.loaded_segments (0x5daac : word) = Some W_5d694.
Proof. vm_refl. Qed.
Lemma D_5d694 : decode_any W_5d694 = Some (Load SZ8 true 23 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d698 : bv 32 := 0x04013c03.
Lemma F_5d698 : fetch_word AsanUbsan.M.loaded_segments (0x5dab0 : word) = Some W_5d698.
Proof. vm_refl. Qed.
Lemma D_5d698 : decode_any W_5d698 = Some (Load SZ8 true 24 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d69c : bv 32 := 0x03813c83.
Lemma F_5d69c : fetch_word AsanUbsan.M.loaded_segments (0x5dab4 : word) = Some W_5d69c.
Proof. vm_refl. Qed.
Lemma D_5d69c : decode_any W_5d69c = Some (Load SZ8 true 25 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6a0 : bv 32 := 0x03013d03.
Lemma F_5d6a0 : fetch_word AsanUbsan.M.loaded_segments (0x5dab8 : word) = Some W_5d6a0.
Proof. vm_refl. Qed.
Lemma D_5d6a0 : decode_any W_5d6a0 = Some (Load SZ8 true 26 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6a4 : bv 32 := 0x02813d83.
Lemma F_5d6a4 : fetch_word AsanUbsan.M.loaded_segments (0x5dabc : word) = Some W_5d6a4.
Proof. vm_refl. Qed.
Lemma D_5d6a4 : decode_any W_5d6a4 = Some (Load SZ8 true 27 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6a8 : bv 32 := 0x09010113.
Lemma F_5d6a8 : fetch_word AsanUbsan.M.loaded_segments (0x5dac0 : word) = Some W_5d6a8.
Proof. vm_refl. Qed.
Lemma D_5d6a8 : decode_any W_5d6a8 = Some (OpImm ALU_ADD 2 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6ac : bv 32 := 0x00008067.
Lemma F_5d6ac : fetch_word AsanUbsan.M.loaded_segments (0x5dac4 : word) = Some W_5d6ac.
Proof. vm_refl. Qed.
Lemma D_5d6ac : decode_any W_5d6ac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6b0 : bv 32 := 0x00100593.
Lemma F_5d6b0 : fetch_word AsanUbsan.M.loaded_segments (0x5dac8 : word) = Some W_5d6b0.
Proof. vm_refl. Qed.
Lemma D_5d6b0 : decode_any W_5d6b0 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6b4 : bv 32 := 0x06b50023.
Lemma F_5d6b4 : fetch_word AsanUbsan.M.loaded_segments (0x5dacc : word) = Some W_5d6b4.
Proof. vm_refl. Qed.
Lemma D_5d6b4 : decode_any W_5d6b4 = Some (Store SZ1 10 11 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6b8 : bv 32 := 0x00008067.
Lemma F_5d6b8 : fetch_word AsanUbsan.M.loaded_segments (0x5dad0 : word) = Some W_5d6b8.
Proof. vm_refl. Qed.
Lemma D_5d6b8 : decode_any W_5d6b8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d988 : bv 32 := 0xfe010113.
Lemma F_5d988 : fetch_word AsanUbsan.M.loaded_segments (0x5dda0 : word) = Some W_5d988.
Proof. vm_refl. Qed.
Lemma D_5d988 : decode_any W_5d988 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d98c : bv 32 := 0x00113c23.
Lemma F_5d98c : fetch_word AsanUbsan.M.loaded_segments (0x5dda4 : word) = Some W_5d98c.
Proof. vm_refl. Qed.
Lemma D_5d98c : decode_any W_5d98c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d990 : bv 32 := 0x00813823.
Lemma F_5d990 : fetch_word AsanUbsan.M.loaded_segments (0x5dda8 : word) = Some W_5d990.
Proof. vm_refl. Qed.
Lemma D_5d990 : decode_any W_5d990 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d994 : bv 32 := 0x00913423.
Lemma F_5d994 : fetch_word AsanUbsan.M.loaded_segments (0x5ddac : word) = Some W_5d994.
Proof. vm_refl. Qed.
Lemma D_5d994 : decode_any W_5d994 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d998 : bv 32 := 0x01213023.
Lemma F_5d998 : fetch_word AsanUbsan.M.loaded_segments (0x5ddb0 : word) = Some W_5d998.
Proof. vm_refl. Qed.
Lemma D_5d998 : decode_any W_5d998 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d99c : bv 32 := 0x02010413.
Lemma F_5d99c : fetch_word AsanUbsan.M.loaded_segments (0x5ddb4 : word) = Some W_5d99c.
Proof. vm_refl. Qed.
Lemma D_5d99c : decode_any W_5d99c = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9a0 : bv 32 := 0x000da517.
Lemma F_5d9a0 : fetch_word AsanUbsan.M.loaded_segments (0x5ddb8 : word) = Some W_5d9a0.
Proof. vm_refl. Qed.
Lemma D_5d9a0 : decode_any W_5d9a0 = Some (Auipc 10 218, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9a4 : bv 32 := 0x50050513.
Lemma F_5d9a4 : fetch_word AsanUbsan.M.loaded_segments (0x5ddbc : word) = Some W_5d9a4.
Proof. vm_refl. Qed.
Lemma D_5d9a4 : decode_any W_5d9a4 = Some (OpImm ALU_ADD 10 10 1280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9a8 : bv 32 := 0x630050ef.
Lemma F_5d9a8 : fetch_word AsanUbsan.M.loaded_segments (0x5ddc0 : word) = Some W_5d9a8.
Proof. vm_refl. Qed.
Lemma D_5d9a8 : decode_any W_5d9a8 = Some (Jal 1 22064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9ac : bv 32 := 0x00053483.
Lemma F_5d9ac : fetch_word AsanUbsan.M.loaded_segments (0x5ddc4 : word) = Some W_5d9ac.
Proof. vm_refl. Qed.
Lemma D_5d9ac : decode_any W_5d9ac = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9b0 : bv 32 := 0x08048863.
Lemma F_5d9b0 : fetch_word AsanUbsan.M.loaded_segments (0x5ddc8 : word) = Some W_5d9b0.
Proof. vm_refl. Qed.
Lemma D_5d9b0 : decode_any W_5d9b0 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9b4 : bv 32 := 0x0604c503.
Lemma F_5d9b4 : fetch_word AsanUbsan.M.loaded_segments (0x5ddcc : word) = Some W_5d9b4.
Proof. vm_refl. Qed.
Lemma D_5d9b4 : decode_any W_5d9b4 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9b8 : bv 32 := 0x0584b903.
Lemma F_5d9b8 : fetch_word AsanUbsan.M.loaded_segments (0x5ddd0 : word) = Some W_5d9b8.
Proof. vm_refl. Qed.
Lemma D_5d9b8 : decode_any W_5d9b8 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9bc : bv 32 := 0x00050863.
Lemma F_5d9bc : fetch_word AsanUbsan.M.loaded_segments (0x5ddd4 : word) = Some W_5d9bc.
Proof. vm_refl. Qed.
Lemma D_5d9bc : decode_any W_5d9bc = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9c0 : bv 32 := 0x00048513.
Lemma F_5d9c0 : fetch_word AsanUbsan.M.loaded_segments (0x5ddd8 : word) = Some W_5d9c0.
Proof. vm_refl. Qed.
Lemma D_5d9c0 : decode_any W_5d9c0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9c4 : bv 32 := 0x00040593.
Lemma F_5d9c4 : fetch_word AsanUbsan.M.loaded_segments (0x5dddc : word) = Some W_5d9c4.
Proof. vm_refl. Qed.
Lemma D_5d9c4 : decode_any W_5d9c4 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9c8 : bv 32 := 0xa01ff0ef.
Lemma F_5d9c8 : fetch_word AsanUbsan.M.loaded_segments (0x5dde0 : word) = Some W_5d9c8.
Proof. vm_refl. Qed.
Lemma D_5d9c8 : decode_any W_5d9c8 = Some (Jal 1 2095616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9cc : bv 32 := 0xff990593.
Lemma F_5d9cc : fetch_word AsanUbsan.M.loaded_segments (0x5dde4 : word) = Some W_5d9cc.
Proof. vm_refl. Qed.
Lemma D_5d9cc : decode_any W_5d9cc = Some (OpImm ALU_ADD 11 18 4089, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9d0 : bv 32 := 0x00100513.
Lemma F_5d9d0 : fetch_word AsanUbsan.M.loaded_segments (0x5dde8 : word) = Some W_5d9d0.
Proof. vm_refl. Qed.
Lemma D_5d9d0 : decode_any W_5d9d0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9d4 : bv 32 := 0x00b51533.
Lemma F_5d9d4 : fetch_word AsanUbsan.M.loaded_segments (0x5ddec : word) = Some W_5d9d4.
Proof. vm_refl. Qed.
Lemma D_5d9d4 : decode_any W_5d9d4 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9d8 : bv 32 := 0x0005061b.
Lemma F_5d9d8 : fetch_word AsanUbsan.M.loaded_segments (0x5ddf0 : word) = Some W_5d9d8.
Proof. vm_refl. Qed.
Lemma D_5d9d8 : decode_any W_5d9d8 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9dc : bv 32 := 0x08c05263.
Lemma F_5d9dc : fetch_word AsanUbsan.M.loaded_segments (0x5ddf4 : word) = Some W_5d9dc.
Proof. vm_refl. Qed.
Lemma D_5d9dc : decode_any W_5d9dc = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9e0 : bv 32 := 0x000016b7.
Lemma F_5d9e0 : fetch_word AsanUbsan.M.loaded_segments (0x5ddf8 : word) = Some W_5d9e0.
Proof. vm_refl. Qed.
Lemma D_5d9e0 : decode_any W_5d9e0 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9e4 : bv 32 := 0xff190613.
Lemma F_5d9e4 : fetch_word AsanUbsan.M.loaded_segments (0x5ddfc : word) = Some W_5d9e4.
Proof. vm_refl. Qed.
Lemma D_5d9e4 : decode_any W_5d9e4 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9e8 : bv 32 := 0x20000713.
Lemma F_5d9e8 : fetch_word AsanUbsan.M.loaded_segments (0x5de00 : word) = Some W_5d9e8.
Proof. vm_refl. Qed.
Lemma D_5d9e8 : decode_any W_5d9e8 = Some (OpImm ALU_ADD 14 0 512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9ec : bv 32 := 0xfff00793.
Lemma F_5d9ec : fetch_word AsanUbsan.M.loaded_segments (0x5de04 : word) = Some W_5d9ec.
Proof. vm_refl. Qed.
Lemma D_5d9ec : decode_any W_5d9ec = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9f0 : bv 32 := 0x00c71733.
Lemma F_5d9f0 : fetch_word AsanUbsan.M.loaded_segments (0x5de08 : word) = Some W_5d9f0.
Proof. vm_refl. Qed.
Lemma D_5d9f0 : decode_any W_5d9f0 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9f4 : bv 32 := 0x0084b603.
Lemma F_5d9f4 : fetch_word AsanUbsan.M.loaded_segments (0x5de0c : word) = Some W_5d9f4.
Proof. vm_refl. Qed.
Lemma D_5d9f4 : decode_any W_5d9f4 = Some (Load SZ8 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9f8 : bv 32 := 0x00b797b3.
Lemma F_5d9f8 : fetch_word AsanUbsan.M.loaded_segments (0x5de10 : word) = Some W_5d9f8.
Proof. vm_refl. Qed.
Lemma D_5d9f8 : decode_any W_5d9f8 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d9fc : bv 32 := 0xfff50813.
Lemma F_5d9fc : fetch_word AsanUbsan.M.loaded_segments (0x5de14 : word) = Some W_5d9fc.
Proof. vm_refl. Qed.
Lemma D_5d9fc : decode_any W_5d9fc = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da00 : bv 32 := 0x00d485b3.
Lemma F_5da00 : fetch_word AsanUbsan.M.loaded_segments (0x5de18 : word) = Some W_5da00.
Proof. vm_refl. Qed.
Lemma D_5da00 : decode_any W_5da00 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da04 : bv 32 := 0x00e586b3.
Lemma F_5da04 : fetch_word AsanUbsan.M.loaded_segments (0x5de1c : word) = Some W_5da04.
Proof. vm_refl. Qed.
Lemma D_5da04 : decode_any W_5da04 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da08 : bv 32 := 0xfff7c713.
Lemma F_5da08 : fetch_word AsanUbsan.M.loaded_segments (0x5de20 : word) = Some W_5da08.
Proof. vm_refl. Qed.
Lemma D_5da08 : decode_any W_5da08 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da0c : bv 32 := 0x02081813.
Lemma F_5da0c : fetch_word AsanUbsan.M.loaded_segments (0x5de24 : word) = Some W_5da0c.
Proof. vm_refl. Qed.
Lemma D_5da0c : decode_any W_5da0c = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da10 : bv 32 := 0x02085793.
Lemma F_5da10 : fetch_word AsanUbsan.M.loaded_segments (0x5de28 : word) = Some W_5da10.
Proof. vm_refl. Qed.
Lemma D_5da10 : decode_any W_5da10 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da14 : bv 32 := 0x00f607b3.
Lemma F_5da14 : fetch_word AsanUbsan.M.loaded_segments (0x5de2c : word) = Some W_5da14.
Proof. vm_refl. Qed.
Lemma D_5da14 : decode_any W_5da14 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da18 : bv 32 := 0x00178813.
Lemma F_5da18 : fetch_word AsanUbsan.M.loaded_segments (0x5de30 : word) = Some W_5da18.
Proof. vm_refl. Qed.
Lemma D_5da18 : decode_any W_5da18 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da1c : bv 32 := 0x00e678b3.
Lemma F_5da1c : fetch_word AsanUbsan.M.loaded_segments (0x5de34 : word) = Some W_5da1c.
Proof. vm_refl. Qed.
Lemma D_5da1c : decode_any W_5da1c = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da20 : bv 32 := 0x011687b3.
Lemma F_5da20 : fetch_word AsanUbsan.M.loaded_segments (0x5de38 : word) = Some W_5da20.
Proof. vm_refl. Qed.
Lemma D_5da20 : decode_any W_5da20 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da24 : bv 32 := 0x0007c283.
Lemma F_5da24 : fetch_word AsanUbsan.M.loaded_segments (0x5de3c : word) = Some W_5da24.
Proof. vm_refl. Qed.
Lemma D_5da24 : decode_any W_5da24 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da28 : bv 32 := 0x06028663.
Lemma F_5da28 : fetch_word AsanUbsan.M.loaded_segments (0x5de40 : word) = Some W_5da28.
Proof. vm_refl. Qed.
Lemma D_5da28 : decode_any W_5da28 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da2c : bv 32 := 0xfff5051b.
Lemma F_5da2c : fetch_word AsanUbsan.M.loaded_segments (0x5de44 : word) = Some W_5da2c.
Proof. vm_refl. Qed.
Lemma D_5da2c : decode_any W_5da2c = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da30 : bv 32 := 0x00160613.
Lemma F_5da30 : fetch_word AsanUbsan.M.loaded_segments (0x5de48 : word) = Some W_5da30.
Proof. vm_refl. Qed.
Lemma D_5da30 : decode_any W_5da30 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da34 : bv 32 := 0xfe0514e3.
Lemma F_5da34 : fetch_word AsanUbsan.M.loaded_segments (0x5de4c : word) = Some W_5da34.
Proof. vm_refl. Qed.
Lemma D_5da34 : decode_any W_5da34 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da94 : bv 32 := 0x00160613.
Lemma F_5da94 : fetch_word AsanUbsan.M.loaded_segments (0x5deac : word) = Some W_5da94.
Proof. vm_refl. Qed.
Lemma D_5da94 : decode_any W_5da94 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da98 : bv 32 := 0x00100513.
Lemma F_5da98 : fetch_word AsanUbsan.M.loaded_segments (0x5deb0 : word) = Some W_5da98.
Proof. vm_refl. Qed.
Lemma D_5da98 : decode_any W_5da98 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da9c : bv 32 := 0xffb90693.
Lemma F_5da9c : fetch_word AsanUbsan.M.loaded_segments (0x5deb4 : word) = Some W_5da9c.
Proof. vm_refl. Qed.
Lemma D_5da9c : decode_any W_5da9c = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5daa0 : bv 32 := 0x00789893.
Lemma F_5daa0 : fetch_word AsanUbsan.M.loaded_segments (0x5deb8 : word) = Some W_5daa0.
Proof. vm_refl. Qed.
Lemma D_5daa0 : decode_any W_5daa0 = Some (ShiftImm ALU_SLL 17 17 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5daa4 : bv 32 := 0x00c4b423.
Lemma F_5daa4 : fetch_word AsanUbsan.M.loaded_segments (0x5debc : word) = Some W_5daa4.
Proof. vm_refl. Qed.
Lemma D_5daa4 : decode_any W_5daa4 = Some (Store SZ8 9 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5daa8 : bv 32 := 0x00a78023.
Lemma F_5daa8 : fetch_word AsanUbsan.M.loaded_segments (0x5dec0 : word) = Some W_5daa8.
Proof. vm_refl. Qed.
Lemma D_5daa8 : decode_any W_5daa8 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5daac : bv 32 := 0x00d51633.
Lemma F_5daac : fetch_word AsanUbsan.M.loaded_segments (0x5dec4 : word) = Some W_5daac.
Proof. vm_refl. Qed.
Lemma D_5daac : decode_any W_5daac = Some (Op ALU_SLL 12 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dab0 : bv 32 := 0x01251533.
Lemma F_5dab0 : fetch_word AsanUbsan.M.loaded_segments (0x5dec8 : word) = Some W_5dab0.
Proof. vm_refl. Qed.
Lemma D_5dab0 : decode_any W_5dab0 = Some (Op ALU_SLL 10 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dab4 : bv 32 := 0x00c585b3.
Lemma F_5dab4 : fetch_word AsanUbsan.M.loaded_segments (0x5decc : word) = Some W_5dab4.
Proof. vm_refl. Qed.
Lemma D_5dab4 : decode_any W_5dab4 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dab8 : bv 32 := 0x01150533.
Lemma F_5dab8 : fetch_word AsanUbsan.M.loaded_segments (0x5ded0 : word) = Some W_5dab8.
Proof. vm_refl. Qed.
Lemma D_5dab8 : decode_any W_5dab8 = Some (Op ALU_ADD 10 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dabc : bv 32 := 0x00a584b3.
Lemma F_5dabc : fetch_word AsanUbsan.M.loaded_segments (0x5ded4 : word) = Some W_5dabc.
Proof. vm_refl. Qed.
Lemma D_5dabc : decode_any W_5dabc = Some (Op ALU_ADD 9 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dac0 : bv 32 := 0x0084bc23.
Lemma F_5dac0 : fetch_word AsanUbsan.M.loaded_segments (0x5ded8 : word) = Some W_5dac0.
Proof. vm_refl. Qed.
Lemma D_5dac0 : decode_any W_5dac0 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dac4 : bv 32 := 0x06f4bc23.
Lemma F_5dac4 : fetch_word AsanUbsan.M.loaded_segments (0x5dedc : word) = Some W_5dac4.
Proof. vm_refl. Qed.
Lemma D_5dac4 : decode_any W_5dac4 = Some (Store SZ8 9 15 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dac8 : bv 32 := 0x00048513.
Lemma F_5dac8 : fetch_word AsanUbsan.M.loaded_segments (0x5dee0 : word) = Some W_5dac8.
Proof. vm_refl. Qed.
Lemma D_5dac8 : decode_any W_5dac8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dacc : bv 32 := 0x4b8000ef.
Lemma F_5dacc : fetch_word AsanUbsan.M.loaded_segments (0x5dee4 : word) = Some W_5dacc.
Proof. vm_refl. Qed.
Lemma D_5dacc : decode_any W_5dacc = Some (Jal 1 1208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dad0 : bv 32 := 0x00050593.
Lemma F_5dad0 : fetch_word AsanUbsan.M.loaded_segments (0x5dee8 : word) = Some W_5dad0.
Proof. vm_refl. Qed.
Lemma D_5dad0 : decode_any W_5dad0 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dad4 : bv 32 := 0x00048513.
Lemma F_5dad4 : fetch_word AsanUbsan.M.loaded_segments (0x5deec : word) = Some W_5dad4.
Proof. vm_refl. Qed.
Lemma D_5dad4 : decode_any W_5dad4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dad8 : bv 32 := 0x00000613.
Lemma F_5dad8 : fetch_word AsanUbsan.M.loaded_segments (0x5def0 : word) = Some W_5dad8.
Proof. vm_refl. Qed.
Lemma D_5dad8 : decode_any W_5dad8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dadc : bv 32 := 0x0005b023.
Lemma F_5dadc : fetch_word AsanUbsan.M.loaded_segments (0x5def4 : word) = Some W_5dadc.
Proof. vm_refl. Qed.
Lemma D_5dadc : decode_any W_5dadc = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dae0 : bv 32 := 0x0005b423.
Lemma F_5dae0 : fetch_word AsanUbsan.M.loaded_segments (0x5def8 : word) = Some W_5dae0.
Proof. vm_refl. Qed.
Lemma D_5dae0 : decode_any W_5dae0 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dae4 : bv 32 := 0x01813083.
Lemma F_5dae4 : fetch_word AsanUbsan.M.loaded_segments (0x5defc : word) = Some W_5dae4.
Proof. vm_refl. Qed.
Lemma D_5dae4 : decode_any W_5dae4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dae8 : bv 32 := 0x01013403.
Lemma F_5dae8 : fetch_word AsanUbsan.M.loaded_segments (0x5df00 : word) = Some W_5dae8.
Proof. vm_refl. Qed.
Lemma D_5dae8 : decode_any W_5dae8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5daec : bv 32 := 0x00813483.
Lemma F_5daec : fetch_word AsanUbsan.M.loaded_segments (0x5df04 : word) = Some W_5daec.
Proof. vm_refl. Qed.
Lemma D_5daec : decode_any W_5daec = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5daf0 : bv 32 := 0x00013903.
Lemma F_5daf0 : fetch_word AsanUbsan.M.loaded_segments (0x5df08 : word) = Some W_5daf0.
Proof. vm_refl. Qed.
Lemma D_5daf0 : decode_any W_5daf0 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5daf4 : bv 32 := 0x02010113.
Lemma F_5daf4 : fetch_word AsanUbsan.M.loaded_segments (0x5df0c : word) = Some W_5daf4.
Proof. vm_refl. Qed.
Lemma D_5daf4 : decode_any W_5daf4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5daf8 : bv 32 := 0x00008067.
Lemma F_5daf8 : fetch_word AsanUbsan.M.loaded_segments (0x5df10 : word) = Some W_5daf8.
Proof. vm_refl. Qed.
Lemma D_5daf8 : decode_any W_5daf8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db18 : bv 32 := 0xfe010113.
Lemma F_5db18 : fetch_word AsanUbsan.M.loaded_segments (0x5df30 : word) = Some W_5db18.
Proof. vm_refl. Qed.
Lemma D_5db18 : decode_any W_5db18 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db1c : bv 32 := 0x00113c23.
Lemma F_5db1c : fetch_word AsanUbsan.M.loaded_segments (0x5df34 : word) = Some W_5db1c.
Proof. vm_refl. Qed.
Lemma D_5db1c : decode_any W_5db1c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db20 : bv 32 := 0x00813823.
Lemma F_5db20 : fetch_word AsanUbsan.M.loaded_segments (0x5df38 : word) = Some W_5db20.
Proof. vm_refl. Qed.
Lemma D_5db20 : decode_any W_5db20 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db24 : bv 32 := 0x00913423.
Lemma F_5db24 : fetch_word AsanUbsan.M.loaded_segments (0x5df3c : word) = Some W_5db24.
Proof. vm_refl. Qed.
Lemma D_5db24 : decode_any W_5db24 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db28 : bv 32 := 0x01213023.
Lemma F_5db28 : fetch_word AsanUbsan.M.loaded_segments (0x5df40 : word) = Some W_5db28.
Proof. vm_refl. Qed.
Lemma D_5db28 : decode_any W_5db28 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db2c : bv 32 := 0x02010413.
Lemma F_5db2c : fetch_word AsanUbsan.M.loaded_segments (0x5df44 : word) = Some W_5db2c.
Proof. vm_refl. Qed.
Lemma D_5db2c : decode_any W_5db2c = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db30 : bv 32 := 0x000da517.
Lemma F_5db30 : fetch_word AsanUbsan.M.loaded_segments (0x5df48 : word) = Some W_5db30.
Proof. vm_refl. Qed.
Lemma D_5db30 : decode_any W_5db30 = Some (Auipc 10 218, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db34 : bv 32 := 0x37050513.
Lemma F_5db34 : fetch_word AsanUbsan.M.loaded_segments (0x5df4c : word) = Some W_5db34.
Proof. vm_refl. Qed.
Lemma D_5db34 : decode_any W_5db34 = Some (OpImm ALU_ADD 10 10 880, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db38 : bv 32 := 0x4a0050ef.
Lemma F_5db38 : fetch_word AsanUbsan.M.loaded_segments (0x5df50 : word) = Some W_5db38.
Proof. vm_refl. Qed.
Lemma D_5db38 : decode_any W_5db38 = Some (Jal 1 21664, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db3c : bv 32 := 0x00053483.
Lemma F_5db3c : fetch_word AsanUbsan.M.loaded_segments (0x5df54 : word) = Some W_5db3c.
Proof. vm_refl. Qed.
Lemma D_5db3c : decode_any W_5db3c = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db40 : bv 32 := 0x08048863.
Lemma F_5db40 : fetch_word AsanUbsan.M.loaded_segments (0x5df58 : word) = Some W_5db40.
Proof. vm_refl. Qed.
Lemma D_5db40 : decode_any W_5db40 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db44 : bv 32 := 0x0604c503.
Lemma F_5db44 : fetch_word AsanUbsan.M.loaded_segments (0x5df5c : word) = Some W_5db44.
Proof. vm_refl. Qed.
Lemma D_5db44 : decode_any W_5db44 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db48 : bv 32 := 0x0584b903.
Lemma F_5db48 : fetch_word AsanUbsan.M.loaded_segments (0x5df60 : word) = Some W_5db48.
Proof. vm_refl. Qed.
Lemma D_5db48 : decode_any W_5db48 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db4c : bv 32 := 0x00050863.
Lemma F_5db4c : fetch_word AsanUbsan.M.loaded_segments (0x5df64 : word) = Some W_5db4c.
Proof. vm_refl. Qed.
Lemma D_5db4c : decode_any W_5db4c = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db50 : bv 32 := 0x00048513.
Lemma F_5db50 : fetch_word AsanUbsan.M.loaded_segments (0x5df68 : word) = Some W_5db50.
Proof. vm_refl. Qed.
Lemma D_5db50 : decode_any W_5db50 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db54 : bv 32 := 0x00040593.
Lemma F_5db54 : fetch_word AsanUbsan.M.loaded_segments (0x5df6c : word) = Some W_5db54.
Proof. vm_refl. Qed.
Lemma D_5db54 : decode_any W_5db54 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db58 : bv 32 := 0x871ff0ef.
Lemma F_5db58 : fetch_word AsanUbsan.M.loaded_segments (0x5df70 : word) = Some W_5db58.
Proof. vm_refl. Qed.
Lemma D_5db58 : decode_any W_5db58 = Some (Jal 1 2095216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db5c : bv 32 := 0xff790593.
Lemma F_5db5c : fetch_word AsanUbsan.M.loaded_segments (0x5df74 : word) = Some W_5db5c.
Proof. vm_refl. Qed.
Lemma D_5db5c : decode_any W_5db5c = Some (OpImm ALU_ADD 11 18 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db60 : bv 32 := 0x00100513.
Lemma F_5db60 : fetch_word AsanUbsan.M.loaded_segments (0x5df78 : word) = Some W_5db60.
Proof. vm_refl. Qed.
Lemma D_5db60 : decode_any W_5db60 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db64 : bv 32 := 0x00b51533.
Lemma F_5db64 : fetch_word AsanUbsan.M.loaded_segments (0x5df7c : word) = Some W_5db64.
Proof. vm_refl. Qed.
Lemma D_5db64 : decode_any W_5db64 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db68 : bv 32 := 0x0005061b.
Lemma F_5db68 : fetch_word AsanUbsan.M.loaded_segments (0x5df80 : word) = Some W_5db68.
Proof. vm_refl. Qed.
Lemma D_5db68 : decode_any W_5db68 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db6c : bv 32 := 0x08c05263.
Lemma F_5db6c : fetch_word AsanUbsan.M.loaded_segments (0x5df84 : word) = Some W_5db6c.
Proof. vm_refl. Qed.
Lemma D_5db6c : decode_any W_5db6c = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db70 : bv 32 := 0x000016b7.
Lemma F_5db70 : fetch_word AsanUbsan.M.loaded_segments (0x5df88 : word) = Some W_5db70.
Proof. vm_refl. Qed.
Lemma D_5db70 : decode_any W_5db70 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db74 : bv 32 := 0xff190613.
Lemma F_5db74 : fetch_word AsanUbsan.M.loaded_segments (0x5df8c : word) = Some W_5db74.
Proof. vm_refl. Qed.
Lemma D_5db74 : decode_any W_5db74 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db78 : bv 32 := 0x38000713.
Lemma F_5db78 : fetch_word AsanUbsan.M.loaded_segments (0x5df90 : word) = Some W_5db78.
Proof. vm_refl. Qed.
Lemma D_5db78 : decode_any W_5db78 = Some (OpImm ALU_ADD 14 0 896, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db7c : bv 32 := 0xfff00793.
Lemma F_5db7c : fetch_word AsanUbsan.M.loaded_segments (0x5df94 : word) = Some W_5db7c.
Proof. vm_refl. Qed.
Lemma D_5db7c : decode_any W_5db7c = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db80 : bv 32 := 0x00c71733.
Lemma F_5db80 : fetch_word AsanUbsan.M.loaded_segments (0x5df98 : word) = Some W_5db80.
Proof. vm_refl. Qed.
Lemma D_5db80 : decode_any W_5db80 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db84 : bv 32 := 0x0184b603.
Lemma F_5db84 : fetch_word AsanUbsan.M.loaded_segments (0x5df9c : word) = Some W_5db84.
Proof. vm_refl. Qed.
Lemma D_5db84 : decode_any W_5db84 = Some (Load SZ8 true 12 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db88 : bv 32 := 0x00b797b3.
Lemma F_5db88 : fetch_word AsanUbsan.M.loaded_segments (0x5dfa0 : word) = Some W_5db88.
Proof. vm_refl. Qed.
Lemma D_5db88 : decode_any W_5db88 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db8c : bv 32 := 0xfff50813.
Lemma F_5db8c : fetch_word AsanUbsan.M.loaded_segments (0x5dfa4 : word) = Some W_5db8c.
Proof. vm_refl. Qed.
Lemma D_5db8c : decode_any W_5db8c = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db90 : bv 32 := 0x00d485b3.
Lemma F_5db90 : fetch_word AsanUbsan.M.loaded_segments (0x5dfa8 : word) = Some W_5db90.
Proof. vm_refl. Qed.
Lemma D_5db90 : decode_any W_5db90 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db94 : bv 32 := 0x00e586b3.
Lemma F_5db94 : fetch_word AsanUbsan.M.loaded_segments (0x5dfac : word) = Some W_5db94.
Proof. vm_refl. Qed.
Lemma D_5db94 : decode_any W_5db94 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db98 : bv 32 := 0xfff7c713.
Lemma F_5db98 : fetch_word AsanUbsan.M.loaded_segments (0x5dfb0 : word) = Some W_5db98.
Proof. vm_refl. Qed.
Lemma D_5db98 : decode_any W_5db98 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5db9c : bv 32 := 0x02081813.
Lemma F_5db9c : fetch_word AsanUbsan.M.loaded_segments (0x5dfb4 : word) = Some W_5db9c.
Proof. vm_refl. Qed.
Lemma D_5db9c : decode_any W_5db9c = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dba0 : bv 32 := 0x02085793.
Lemma F_5dba0 : fetch_word AsanUbsan.M.loaded_segments (0x5dfb8 : word) = Some W_5dba0.
Proof. vm_refl. Qed.
Lemma D_5dba0 : decode_any W_5dba0 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dba4 : bv 32 := 0x00f607b3.
Lemma F_5dba4 : fetch_word AsanUbsan.M.loaded_segments (0x5dfbc : word) = Some W_5dba4.
Proof. vm_refl. Qed.
Lemma D_5dba4 : decode_any W_5dba4 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dba8 : bv 32 := 0x00178813.
Lemma F_5dba8 : fetch_word AsanUbsan.M.loaded_segments (0x5dfc0 : word) = Some W_5dba8.
Proof. vm_refl. Qed.
Lemma D_5dba8 : decode_any W_5dba8 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dbac : bv 32 := 0x00e678b3.
Lemma F_5dbac : fetch_word AsanUbsan.M.loaded_segments (0x5dfc4 : word) = Some W_5dbac.
Proof. vm_refl. Qed.
Lemma D_5dbac : decode_any W_5dbac = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dbb0 : bv 32 := 0x011687b3.
Lemma F_5dbb0 : fetch_word AsanUbsan.M.loaded_segments (0x5dfc8 : word) = Some W_5dbb0.
Proof. vm_refl. Qed.
Lemma D_5dbb0 : decode_any W_5dbb0 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dbb4 : bv 32 := 0x0007c283.
Lemma F_5dbb4 : fetch_word AsanUbsan.M.loaded_segments (0x5dfcc : word) = Some W_5dbb4.
Proof. vm_refl. Qed.
Lemma D_5dbb4 : decode_any W_5dbb4 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dbb8 : bv 32 := 0x06028663.
Lemma F_5dbb8 : fetch_word AsanUbsan.M.loaded_segments (0x5dfd0 : word) = Some W_5dbb8.
Proof. vm_refl. Qed.
Lemma D_5dbb8 : decode_any W_5dbb8 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dbbc : bv 32 := 0xfff5051b.
Lemma F_5dbbc : fetch_word AsanUbsan.M.loaded_segments (0x5dfd4 : word) = Some W_5dbbc.
Proof. vm_refl. Qed.
Lemma D_5dbbc : decode_any W_5dbbc = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dbc0 : bv 32 := 0x00160613.
Lemma F_5dbc0 : fetch_word AsanUbsan.M.loaded_segments (0x5dfd8 : word) = Some W_5dbc0.
Proof. vm_refl. Qed.
Lemma D_5dbc0 : decode_any W_5dbc0 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dbc4 : bv 32 := 0xfe0514e3.
Lemma F_5dbc4 : fetch_word AsanUbsan.M.loaded_segments (0x5dfdc : word) = Some W_5dbc4.
Proof. vm_refl. Qed.
Lemma D_5dbc4 : decode_any W_5dbc4 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc24 : bv 32 := 0x00160613.
Lemma F_5dc24 : fetch_word AsanUbsan.M.loaded_segments (0x5e03c : word) = Some W_5dc24.
Proof. vm_refl. Qed.
Lemma D_5dc24 : decode_any W_5dc24 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc28 : bv 32 := 0x00100513.
Lemma F_5dc28 : fetch_word AsanUbsan.M.loaded_segments (0x5e040 : word) = Some W_5dc28.
Proof. vm_refl. Qed.
Lemma D_5dc28 : decode_any W_5dc28 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc2c : bv 32 := 0xffb90693.
Lemma F_5dc2c : fetch_word AsanUbsan.M.loaded_segments (0x5e044 : word) = Some W_5dc2c.
Proof. vm_refl. Qed.
Lemma D_5dc2c : decode_any W_5dc2c = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc30 : bv 32 := 0x00c4bc23.
Lemma F_5dc30 : fetch_word AsanUbsan.M.loaded_segments (0x5e048 : word) = Some W_5dc30.
Proof. vm_refl. Qed.
Lemma D_5dc30 : decode_any W_5dc30 = Some (Store SZ8 9 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc34 : bv 32 := 0x00a78023.
Lemma F_5dc34 : fetch_word AsanUbsan.M.loaded_segments (0x5e04c : word) = Some W_5dc34.
Proof. vm_refl. Qed.
Lemma D_5dc34 : decode_any W_5dc34 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc38 : bv 32 := 0x00d51533.
Lemma F_5dc38 : fetch_word AsanUbsan.M.loaded_segments (0x5e050 : word) = Some W_5dc38.
Proof. vm_refl. Qed.
Lemma D_5dc38 : decode_any W_5dc38 = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc3c : bv 32 := 0x00300613.
Lemma F_5dc3c : fetch_word AsanUbsan.M.loaded_segments (0x5e054 : word) = Some W_5dc3c.
Proof. vm_refl. Qed.
Lemma D_5dc3c : decode_any W_5dc3c = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc40 : bv 32 := 0x00989893.
Lemma F_5dc40 : fetch_word AsanUbsan.M.loaded_segments (0x5e058 : word) = Some W_5dc40.
Proof. vm_refl. Qed.
Lemma D_5dc40 : decode_any W_5dc40 = Some (ShiftImm ALU_SLL 17 17 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc44 : bv 32 := 0x01261633.
Lemma F_5dc44 : fetch_word AsanUbsan.M.loaded_segments (0x5e05c : word) = Some W_5dc44.
Proof. vm_refl. Qed.
Lemma D_5dc44 : decode_any W_5dc44 = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc48 : bv 32 := 0x00a58533.
Lemma F_5dc48 : fetch_word AsanUbsan.M.loaded_segments (0x5e060 : word) = Some W_5dc48.
Proof. vm_refl. Qed.
Lemma D_5dc48 : decode_any W_5dc48 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc4c : bv 32 := 0x01160633.
Lemma F_5dc4c : fetch_word AsanUbsan.M.loaded_segments (0x5e064 : word) = Some W_5dc4c.
Proof. vm_refl. Qed.
Lemma D_5dc4c : decode_any W_5dc4c = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc50 : bv 32 := 0x00c504b3.
Lemma F_5dc50 : fetch_word AsanUbsan.M.loaded_segments (0x5e068 : word) = Some W_5dc50.
Proof. vm_refl. Qed.
Lemma D_5dc50 : decode_any W_5dc50 = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc54 : bv 32 := 0x0084bc23.
Lemma F_5dc54 : fetch_word AsanUbsan.M.loaded_segments (0x5e06c : word) = Some W_5dc54.
Proof. vm_refl. Qed.
Lemma D_5dc54 : decode_any W_5dc54 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc58 : bv 32 := 0x1ef4bc23.
Lemma F_5dc58 : fetch_word AsanUbsan.M.loaded_segments (0x5e070 : word) = Some W_5dc58.
Proof. vm_refl. Qed.
Lemma D_5dc58 : decode_any W_5dc58 = Some (Store SZ8 9 15 504, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc5c : bv 32 := 0x00048513.
Lemma F_5dc5c : fetch_word AsanUbsan.M.loaded_segments (0x5e074 : word) = Some W_5dc5c.
Proof. vm_refl. Qed.
Lemma D_5dc5c : decode_any W_5dc5c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc60 : bv 32 := 0x324000ef.
Lemma F_5dc60 : fetch_word AsanUbsan.M.loaded_segments (0x5e078 : word) = Some W_5dc60.
Proof. vm_refl. Qed.
Lemma D_5dc60 : decode_any W_5dc60 = Some (Jal 1 804, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc64 : bv 32 := 0x00050593.
Lemma F_5dc64 : fetch_word AsanUbsan.M.loaded_segments (0x5e07c : word) = Some W_5dc64.
Proof. vm_refl. Qed.
Lemma D_5dc64 : decode_any W_5dc64 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc68 : bv 32 := 0x00048513.
Lemma F_5dc68 : fetch_word AsanUbsan.M.loaded_segments (0x5e080 : word) = Some W_5dc68.
Proof. vm_refl. Qed.
Lemma D_5dc68 : decode_any W_5dc68 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc6c : bv 32 := 0x00000613.
Lemma F_5dc6c : fetch_word AsanUbsan.M.loaded_segments (0x5e084 : word) = Some W_5dc6c.
Proof. vm_refl. Qed.
Lemma D_5dc6c : decode_any W_5dc6c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc70 : bv 32 := 0x0005b023.
Lemma F_5dc70 : fetch_word AsanUbsan.M.loaded_segments (0x5e088 : word) = Some W_5dc70.
Proof. vm_refl. Qed.
Lemma D_5dc70 : decode_any W_5dc70 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc74 : bv 32 := 0x0005b423.
Lemma F_5dc74 : fetch_word AsanUbsan.M.loaded_segments (0x5e08c : word) = Some W_5dc74.
Proof. vm_refl. Qed.
Lemma D_5dc74 : decode_any W_5dc74 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc78 : bv 32 := 0x0005b823.
Lemma F_5dc78 : fetch_word AsanUbsan.M.loaded_segments (0x5e090 : word) = Some W_5dc78.
Proof. vm_refl. Qed.
Lemma D_5dc78 : decode_any W_5dc78 = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc7c : bv 32 := 0x0005bc23.
Lemma F_5dc7c : fetch_word AsanUbsan.M.loaded_segments (0x5e094 : word) = Some W_5dc7c.
Proof. vm_refl. Qed.
Lemma D_5dc7c : decode_any W_5dc7c = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc80 : bv 32 := 0x0205b023.
Lemma F_5dc80 : fetch_word AsanUbsan.M.loaded_segments (0x5e098 : word) = Some W_5dc80.
Proof. vm_refl. Qed.
Lemma D_5dc80 : decode_any W_5dc80 = Some (Store SZ8 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc84 : bv 32 := 0x0205b423.
Lemma F_5dc84 : fetch_word AsanUbsan.M.loaded_segments (0x5e09c : word) = Some W_5dc84.
Proof. vm_refl. Qed.
Lemma D_5dc84 : decode_any W_5dc84 = Some (Store SZ8 11 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc88 : bv 32 := 0x0205b823.
Lemma F_5dc88 : fetch_word AsanUbsan.M.loaded_segments (0x5e0a0 : word) = Some W_5dc88.
Proof. vm_refl. Qed.
Lemma D_5dc88 : decode_any W_5dc88 = Some (Store SZ8 11 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc8c : bv 32 := 0x0205bc23.
Lemma F_5dc8c : fetch_word AsanUbsan.M.loaded_segments (0x5e0a4 : word) = Some W_5dc8c.
Proof. vm_refl. Qed.
Lemma D_5dc8c : decode_any W_5dc8c = Some (Store SZ8 11 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc90 : bv 32 := 0x01813083.
Lemma F_5dc90 : fetch_word AsanUbsan.M.loaded_segments (0x5e0a8 : word) = Some W_5dc90.
Proof. vm_refl. Qed.
Lemma D_5dc90 : decode_any W_5dc90 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc94 : bv 32 := 0x01013403.
Lemma F_5dc94 : fetch_word AsanUbsan.M.loaded_segments (0x5e0ac : word) = Some W_5dc94.
Proof. vm_refl. Qed.
Lemma D_5dc94 : decode_any W_5dc94 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc98 : bv 32 := 0x00813483.
Lemma F_5dc98 : fetch_word AsanUbsan.M.loaded_segments (0x5e0b0 : word) = Some W_5dc98.
Proof. vm_refl. Qed.
Lemma D_5dc98 : decode_any W_5dc98 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc9c : bv 32 := 0x00013903.
Lemma F_5dc9c : fetch_word AsanUbsan.M.loaded_segments (0x5e0b4 : word) = Some W_5dc9c.
Proof. vm_refl. Qed.
Lemma D_5dc9c : decode_any W_5dc9c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dca0 : bv 32 := 0x02010113.
Lemma F_5dca0 : fetch_word AsanUbsan.M.loaded_segments (0x5e0b8 : word) = Some W_5dca0.
Proof. vm_refl. Qed.
Lemma D_5dca0 : decode_any W_5dca0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dca4 : bv 32 := 0x00008067.
Lemma F_5dca4 : fetch_word AsanUbsan.M.loaded_segments (0x5e0bc : word) = Some W_5dca4.
Proof. vm_refl. Qed.
Lemma D_5dca4 : decode_any W_5dca4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df84 : bv 32 := 0x000d9597.
Lemma F_5df84 : fetch_word AsanUbsan.M.loaded_segments (0x5e39c : word) = Some W_5df84.
Proof. vm_refl. Qed.
Lemma D_5df84 : decode_any W_5df84 = Some (Auipc 11 217, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df88 : bv 32 := 0x1245b583.
Lemma F_5df88 : fetch_word AsanUbsan.M.loaded_segments (0x5e3a0 : word) = Some W_5df88.
Proof. vm_refl. Qed.
Lemma D_5df88 : decode_any W_5df88 = Some (Load SZ8 true 11 11 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df8c : bv 32 := 0x0005b583.
Lemma F_5df8c : fetch_word AsanUbsan.M.loaded_segments (0x5e3a4 : word) = Some W_5df8c.
Proof. vm_refl. Qed.
Lemma D_5df8c : decode_any W_5df8c = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df90 : bv 32 := 0xfff58613.
Lemma F_5df90 : fetch_word AsanUbsan.M.loaded_segments (0x5e3a8 : word) = Some W_5df90.
Proof. vm_refl. Qed.
Lemma D_5df90 : decode_any W_5df90 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df94 : bv 32 := 0x00c5b6b3.
Lemma F_5df94 : fetch_word AsanUbsan.M.loaded_segments (0x5e3ac : word) = Some W_5df94.
Proof. vm_refl. Qed.
Lemma D_5df94 : decode_any W_5df94 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df98 : bv 32 := 0xfff68693.
Lemma F_5df98 : fetch_word AsanUbsan.M.loaded_segments (0x5e3b0 : word) = Some W_5df98.
Proof. vm_refl. Qed.
Lemma D_5df98 : decode_any W_5df98 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df9c : bv 32 := 0x00c6f6b3.
Lemma F_5df9c : fetch_word AsanUbsan.M.loaded_segments (0x5e3b4 : word) = Some W_5df9c.
Proof. vm_refl. Qed.
Lemma D_5df9c : decode_any W_5df9c = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dfa0 : bv 32 := 0x04a6f263.
Lemma F_5dfa0 : fetch_word AsanUbsan.M.loaded_segments (0x5e3b8 : word) = Some W_5dfa0.
Proof. vm_refl. Qed.
Lemma D_5dfa0 : decode_any W_5dfa0 = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dfa4 : bv 32 := 0x000d9697.
Lemma F_5dfa4 : fetch_word AsanUbsan.M.loaded_segments (0x5e3bc : word) = Some W_5dfa4.
Proof. vm_refl. Qed.
Lemma D_5dfa4 : decode_any W_5dfa4 = Some (Auipc 13 217, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dfa8 : bv 32 := 0x10c6b683.
Lemma F_5dfa8 : fetch_word AsanUbsan.M.loaded_segments (0x5e3c0 : word) = Some W_5dfa8.
Proof. vm_refl. Qed.
Lemma D_5dfa8 : decode_any W_5dfa8 = Some (Load SZ8 true 13 13 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dfac : bv 32 := 0x000d9717.
Lemma F_5dfac : fetch_word AsanUbsan.M.loaded_segments (0x5e3c4 : word) = Some W_5dfac.
Proof. vm_refl. Qed.
Lemma D_5dfac : decode_any W_5dfac = Some (Auipc 14 217, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dfb0 : bv 32 := 0x10c73703.
Lemma F_5dfb0 : fetch_word AsanUbsan.M.loaded_segments (0x5e3c8 : word) = Some W_5dfb0.
Proof. vm_refl. Qed.
Lemma D_5dfb0 : decode_any W_5dfb0 = Some (Load SZ8 true 14 14 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dfb4 : bv 32 := 0x0006b803.
Lemma F_5dfb4 : fetch_word AsanUbsan.M.loaded_segments (0x5e3cc : word) = Some W_5dfb4.
Proof. vm_refl. Qed.
Lemma D_5dfb4 : decode_any W_5dfb4 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dfb8 : bv 32 := 0x00073683.
Lemma F_5dfb8 : fetch_word AsanUbsan.M.loaded_segments (0x5e3d0 : word) = Some W_5dfb8.
Proof. vm_refl. Qed.
Lemma D_5dfb8 : decode_any W_5dfb8 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dfbc : bv 32 := 0xfff80793.
Lemma F_5dfbc : fetch_word AsanUbsan.M.loaded_segments (0x5e3d4 : word) = Some W_5dfbc.
Proof. vm_refl. Qed.
Lemma D_5dfbc : decode_any W_5dfbc = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dfc0 : bv 32 := 0x00a7f463.
Lemma F_5dfc0 : fetch_word AsanUbsan.M.loaded_segments (0x5e3d8 : word) = Some W_5dfc0.
Proof. vm_refl. Qed.
Lemma D_5dfc0 : decode_any W_5dfc0 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dfc8 : bv 32 := 0x000d9717.
Lemma F_5dfc8 : fetch_word AsanUbsan.M.loaded_segments (0x5e3e0 : word) = Some W_5dfc8.
Proof. vm_refl. Qed.
Lemma D_5dfc8 : decode_any W_5dfc8 = Some (Auipc 14 217, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dfcc : bv 32 := 0x0f873703.
Lemma F_5dfcc : fetch_word AsanUbsan.M.loaded_segments (0x5e3e4 : word) = Some W_5dfcc.
Proof. vm_refl. Qed.
Lemma D_5dfcc : decode_any W_5dfcc = Some (Load SZ8 true 14 14 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dfd0 : bv 32 := 0x00073283.
Lemma F_5dfd0 : fetch_word AsanUbsan.M.loaded_segments (0x5e3e8 : word) = Some W_5dfd0.
Proof. vm_refl. Qed.
Lemma D_5dfd0 : decode_any W_5dfd0 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dfd4 : bv 32 := 0x0032d713.
Lemma F_5dfd4 : fetch_word AsanUbsan.M.loaded_segments (0x5e3ec : word) = Some W_5dfd4.
Proof. vm_refl. Qed.
Lemma D_5dfd4 : decode_any W_5dfd4 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dfd8 : bv 32 := 0x00b708b3.
Lemma F_5dfd8 : fetch_word AsanUbsan.M.loaded_segments (0x5e3f0 : word) = Some W_5dfd8.
Proof. vm_refl. Qed.
Lemma D_5dfd8 : decode_any W_5dfd8 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dfdc : bv 32 := 0x00a2ea63.
Lemma F_5dfdc : fetch_word AsanUbsan.M.loaded_segments (0x5e3f4 : word) = Some W_5dfdc.
Proof. vm_refl. Qed.
Lemma D_5dfdc : decode_any W_5dfdc = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dfe0 : bv 32 := 0x00a8f863.
Lemma F_5dfe0 : fetch_word AsanUbsan.M.loaded_segments (0x5e3f8 : word) = Some W_5dfe0.
Proof. vm_refl. Qed.
Lemma D_5dfe0 : decode_any W_5dfe0 = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dfe4 : bv 32 := 0x00355513.
Lemma F_5dfe4 : fetch_word AsanUbsan.M.loaded_segments (0x5e3fc : word) = Some W_5dfe4.
Proof. vm_refl. Qed.
Lemma D_5dfe4 : decode_any W_5dfe4 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dfe8 : bv 32 := 0x00a58533.
Lemma F_5dfe8 : fetch_word AsanUbsan.M.loaded_segments (0x5e400 : word) = Some W_5dfe8.
Proof. vm_refl. Qed.
Lemma D_5dfe8 : decode_any W_5dfe8 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dfec : bv 32 := 0x00008067.
Lemma F_5dfec : fetch_word AsanUbsan.M.loaded_segments (0x5e404 : word) = Some W_5dfec.
Proof. vm_refl. Qed.
Lemma D_5dfec : decode_any W_5dfec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
