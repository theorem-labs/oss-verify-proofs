From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.P Require Import Str_tac Startup_glue.
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

Lemma tramp_strlen : tramp_step 0x43a98 0x43b48. Proof. tramp_proof. Qed.
Lemma tramp_strnlen : tramp_step 0x43a9c 0x43ddc. Proof. tramp_proof. Qed.
Lemma tramp_memchr : tramp_step 0x43ac8 0x46fc8. Proof. tramp_proof. Qed.
Lemma tramp_memcpy : tramp_step 0x55968 0x56338. Proof. tramp_proof. Qed.
Lemma tramp_bcmp : tramp_step 0x43ac4 0x46f0c. Proof. tramp_proof. Qed.
Lemma tramp_strncmp : tramp_step 0x43aa4 0x445a8. Proof. tramp_proof. Qed.
Lemma tramp_memcmp : tramp_step 0x43ac0 0x46e50. Proof. tramp_proof. Qed.
Lemma tramp_memset : tramp_step 0x55964 0x56048. Proof. tramp_proof. Qed.
Lemma tramp_strtol : tramp_step 0x43b44 0x4b6b8. Proof. tramp_proof. Qed.
