(* Ported by a Theorem Labs lane from a working branch affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/A/I_tramp.v, unchanged. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.P Require Import Str_tac Startup_glue.
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

Lemma tramp_strlen : tramp_step 0x412c8 0x41364. Proof. tramp_proof. Qed.
Lemma tramp_strnlen : tramp_step 0x412cc 0x415f8. Proof. tramp_proof. Qed.
Lemma tramp_memchr : tramp_step 0x412ec 0x43b78. Proof. tramp_proof. Qed.
Lemma tramp_memcpy : tramp_step 0x51a64 0x52434. Proof. tramp_proof. Qed.
Lemma tramp_bcmp : tramp_step 0x412e8 0x43abc. Proof. tramp_proof. Qed.
Lemma tramp_strncmp : tramp_step 0x412d4 0x41dc4. Proof. tramp_proof. Qed.
Lemma tramp_memcmp : tramp_step 0x412e4 0x43a00. Proof. tramp_proof. Qed.
Lemma tramp_memset : tramp_step 0x51a60 0x52144. Proof. tramp_proof. Qed.
Lemma tramp_strncasecmp : tramp_step 0x412d8 0x423a0. Proof. tramp_proof. Qed.
