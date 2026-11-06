From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.P Require Import Str_tac Startup_glue.
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

Lemma tramp_strlen : tramp_step 0x4218c 0x42230. Proof. tramp_proof. Qed.
Lemma tramp_strnlen : tramp_step 0x42190 0x424c4. Proof. tramp_proof. Qed.
Lemma tramp_memchr : tramp_step 0x421b0 0x44548. Proof. tramp_proof. Qed.
Lemma tramp_memcpy : tramp_step 0x52724 0x53464. Proof. tramp_proof. Qed.
Lemma tramp_bcmp : tramp_step 0x421ac 0x4448c. Proof. tramp_proof. Qed.
Lemma tramp_strncmp : tramp_step 0x4219c 0x42fa0. Proof. tramp_proof. Qed.
Lemma tramp_memcmp : tramp_step 0x421a8 0x443d0. Proof. tramp_proof. Qed.
Lemma tramp_memset : tramp_step 0x52720 0x53174. Proof. tramp_proof. Qed.
