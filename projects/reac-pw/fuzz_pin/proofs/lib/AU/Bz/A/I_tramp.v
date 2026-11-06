(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_boxreg/lib/A/Bz/A/I_tramp.v at origin/ossv/recipes f26f9fbd8777; module paths changed; 16 address numerals relocated from fuzz_boxreg.asan to fuzz_pin.asan (provenance/reloc-WStrncmp/ledger-bz.tsv). *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/Bz/A/I_tramp.v of this library, for reac-pw/fuzz_pin's asan-ubsan image (fuzz_pin.asan-ubsan d6f83d301522) instead of its asan image (fuzz_pin.asan 3e4859aed23f): module paths lib.A -> lib.AU; no numeral changed (every address numeral checked on the asan-ubsan image). The comment lines above describe how lib/A/Bz/A/I_tramp.v was made and quote the asan image's values; the code and comments below carry the asan-ubsan values. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.Bz.P Require Import Str_tac Startup_glue.
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

Lemma tramp_strlen : tramp_step 0x41908 0x419a0. Proof. tramp_proof. Qed.
Lemma tramp_strnlen : tramp_step 0x4190c 0x41c34. Proof. tramp_proof. Qed.
Lemma tramp_memchr : tramp_step 0x41928 0x43b50. Proof. tramp_proof. Qed.
Lemma tramp_memcpy : tramp_step 0x51a3c 0x521cc. Proof. tramp_proof. Qed.
Lemma tramp_bcmp : tramp_step 0x41924 0x43a94. Proof. tramp_proof. Qed.
Lemma tramp_strncmp : tramp_step 0x41914 0x42400. Proof. tramp_proof. Qed.
Lemma tramp_memcmp : tramp_step 0x41920 0x439d8. Proof. tramp_proof. Qed.
Lemma tramp_memset : tramp_step 0x51a38 0x51edc. Proof. tramp_proof. Qed.
