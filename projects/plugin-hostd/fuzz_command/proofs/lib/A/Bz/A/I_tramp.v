From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.P Require Import Str_tac Startup_glue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* Each exported wrapper symbol is a one-instruction trampoline, a jump to the interceptor body. *)

Definition tramp_step (from to : Z) : Prop :=
  forall (Q : machine_state -> Prop) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte),
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 to) fc None m (seg_rom asegs)) ->
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 from) fc None m (seg_rom asegs)).

Ltac tramp_proof := unfold tramp_step; intros; lstep; assumption.

Lemma tramp_strlen : tramp_step 0x45130 0x451e8. Proof. tramp_proof. Qed.
Lemma tramp_strnlen : tramp_step 0x45134 0x4547c. Proof. tramp_proof. Qed.
Lemma tramp_memchr : tramp_step 0x45158 0x47b30. Proof. tramp_proof. Qed.
Lemma tramp_memcpy : tramp_step 0x5762c 0x57ffc. Proof. tramp_proof. Qed.
Lemma tramp_bcmp : tramp_step 0x45154 0x47a74. Proof. tramp_proof. Qed.
Lemma tramp_strncmp : tramp_step 0x45140 0x45f58. Proof. tramp_proof. Qed.
Lemma tramp_memcmp : tramp_step 0x45150 0x479b8. Proof. tramp_proof. Qed.
Lemma tramp_memset : tramp_step 0x57628 0x57d0c. Proof. tramp_proof. Qed.
Lemma tramp_strcpy : tramp_step 0x451d8 0x4c760. Proof. tramp_proof. Qed.
Lemma tramp_strcat : tramp_step 0x451d4 0x4c060. Proof. tramp_proof. Qed.
Lemma tramp_strtol : tramp_step 0x451e0 0x4d048. Proof. tramp_proof. Qed.
Lemma tramp_atoi : tramp_step 0x451e4 0x4d10c. Proof. tramp_proof. Qed.
