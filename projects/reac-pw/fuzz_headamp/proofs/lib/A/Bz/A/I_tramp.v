(* Modified by Theorem Labs, 2026-10: proofs/plugin-hostd/fuzz_command/lib/A/Bz/A/I_tramp.v at 2d2ff01bb6f; module paths changed to reac-pw/fuzz_headamp; 16 numeral(s) moved from fuzz_command.asan to fuzz_headamp.asan by alreloc a5c53bb2bed4; the trampolines of bcmp, strcpy, strcat and atoi removed (fuzz_headamp.asan has none of the four). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz.P Require Import Str_tac Startup_glue.
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

Lemma tramp_strlen : tramp_step 0x41b98 0x41c2c. Proof. tramp_proof. Qed.
Lemma tramp_strnlen : tramp_step 0x41b9c 0x41ec0. Proof. tramp_proof. Qed.
Lemma tramp_memchr : tramp_step 0x41bb0 0x43898. Proof. tramp_proof. Qed.
Lemma tramp_memcpy : tramp_step 0x51d08 0x526d8. Proof. tramp_proof. Qed.
Lemma tramp_strncmp : tramp_step 0x41ba4 0x4268c. Proof. tramp_proof. Qed.
Lemma tramp_memcmp : tramp_step 0x41bac 0x437dc. Proof. tramp_proof. Qed.
Lemma tramp_memset : tramp_step 0x51d04 0x523e8. Proof. tramp_proof. Qed.
Lemma tramp_strtol : tramp_step 0x41c28 0x47a58. Proof. tramp_proof. Qed.
