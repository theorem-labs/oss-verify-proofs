(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require CTabKB.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
Open Scope bv_scope.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Definition W_b175c : bv 32 := 0x000b4503.
Lemma F_b175c : CTabKB.F 0xb175c W_b175c.
Proof. vm_refl. Qed.
Lemma D_b175c : CTabKB.D W_b175c (Load SZ1 false 10 22 0).
Proof. vm_refl. Qed.
