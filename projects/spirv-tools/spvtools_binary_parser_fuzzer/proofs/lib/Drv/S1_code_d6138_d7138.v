(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_d70a0 : bv 32 := 0x07800813.

Definition W_d70a4 : bv 32 := 0x07013503.

Definition W_d70a8 : bv 32 := 0xfff39597.

Definition W_d70ac : bv 32 := 0x47058713.

Definition W_d70b0 : bv 32 := 0x04050463.

Definition W_d70b4 : bv 32 := 0x02087593.

Definition W_d70b8 : bv 32 := 0x0b010b93.

Definition W_d70bc : bv 32 := 0x00f57613.

Definition W_d70c0 : bv 32 := 0xfff75697.

Definition W_d70c4 : bv 32 := 0xc0c68693.

Definition W_d70c8 : bv 32 := 0x00c68633.

Definition W_d70cc : bv 32 := 0x00064603.

Definition W_d70d0 : bv 32 := 0x00455513.

Definition W_d70d4 : bv 32 := 0x00b66633.

Definition W_d70d8 : bv 32 := 0xfecb8fa3.

Definition W_d70dc : bv 32 := 0xfffb8b93.

Definition W_d70e0 : bv 32 := 0xfc051ee3.

Definition W_d70e4 : bv 32 := 0x008c7513.

Definition W_d70e8 : bv 32 := 0x0c051263.

Definition W_d70ec : bv 32 := 0x00e13023.

Definition W_d70f0 : bv 32 := 0x00013c23.

Definition W_d70f4 : bv 32 := 0x1640006f.

Definition W_d70f8 : bv 32 := 0x00e13023.

Definition W_d70fc : bv 32 := 0x00013c23.

Definition W_d7100 : bv 32 := 0x0b010b93.

Definition W_d7104 : bv 32 := 0x1540006f.

Definition W_d7108 : bv 32 := 0x440c8263.

Definition W_d710c : bv 32 := 0x07013903.

Definition W_d7110 : bv 32 := 0x00000b93.

Definition W_d7114 : bv 32 := 0x00090d13.

Definition W_d7118 : bv 32 := 0x000d2583.

Definition W_d711c : bv 32 := 0x02058263.

Definition W_d7120 : bv 32 := 0x08c10513.

Definition W_d7124 : bv 32 := 0xa31fe0ef.

Definition W_d7128 : bv 32 := 0x60054663.

Definition W_d712c : bv 32 := 0x417c85b3.

Definition W_d7130 : bv 32 := 0x00a5e863.

Definition W_d7134 : bv 32 := 0x00ab8bb3.

