(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/A/I_tramp.v (a working branch 3e35620c52e); relocated to libreac/fuzz_disco.asan-ubsan by reloc.py (target disco-Y): module paths changed; 15 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan-ubsan, symbol + offset; its relocation table is not kept). *)
(* Ported by a Theorem Labs lane from a working branch affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/A/I_tramp.v, unchanged. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.B.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.B.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.B.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.B.Bz.P Require Import Str_tac Startup_glue.
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

Lemma tramp_strlen : tramp_step 0x42a3c 0x42acc. Proof. tramp_proof. Qed.
Lemma tramp_strnlen : tramp_step 0x42a40 0x42d60. Proof. tramp_proof. Qed.
Lemma tramp_memchr : tramp_step 0x42a54 0x44218. Proof. tramp_proof. Qed.
Lemma tramp_memcpy : tramp_step 0x52104 0x52ad4. Proof. tramp_proof. Qed.
Lemma tramp_bcmp : tramp_step 0x42a50 0x4415c. Proof. tramp_proof. Qed.
(* tramp_strncmp and tramp_strncasecmp are dropped (provenance/evidence/g9-gxa/gates/numerals-rest.tsv, its four I_tramp.v
   rows): __interceptor_trampoline_strncmp / _strncasecmp and ___interceptor_strncmp / _strncasecmp are ABSENT from
   fuzz_disco.asan-ubsan (provenance/evidence/g9-gxa/codeid/pairs.tsv), and no route file uses either lemma. *)
Lemma tramp_memcmp : tramp_step 0x42a4c 0x440a0. Proof. tramp_proof. Qed.
Lemma tramp_memset : tramp_step 0x52100 0x527e4. Proof. tramp_proof. Qed.
