(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/A/I_tramp.v (cold/port-fm-rtprintf-param 3e35620c52e); relocated to libreac/fuzz_disco.asan by g9/tool (reloc.py target disco-A): module paths changed; 15 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan, symbol + offset; table g9/tool/tables/disco-A/Bz/A/I_tramp.table). *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/Bz/A/I_tramp.v at 2d2ff01bb6f2 relocated to reac-pw/fuzz_rate's ASan image A: module paths changed; numerals by port_core 1e42da8952ec (ledger provenance/reloc/A-Snp.tsv). *)
(* Ported by RtStr from cold/c-asan-rt-fmio-n affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/A/I_tramp.v, unchanged. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Bz.P Require Import Str_tac Startup_glue.
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

Lemma tramp_strlen : tramp_step 0x42194 0x42224. Proof. tramp_proof. Qed.
Lemma tramp_strnlen : tramp_step 0x42198 0x424b8. Proof. tramp_proof. Qed.
Lemma tramp_memchr : tramp_step 0x421ac 0x43970. Proof. tramp_proof. Qed.
Lemma tramp_memcpy : tramp_step 0x5185c 0x5222c. Proof. tramp_proof. Qed.
Lemma tramp_bcmp : tramp_step 0x421a8 0x438b4. Proof. tramp_proof. Qed.
(* tramp_strncmp and tramp_strncasecmp are dropped (g9 P0 stop item, pieces/P4b-A-kit.md:17, numerals-rest.md rows
   35-38): __interceptor_trampoline_strncmp / _strncasecmp and ___interceptor_strncmp / _strncasecmp are ABSENT from
   fuzz_disco.asan (codeid-A.tsv), and no route file uses either lemma. *)
Lemma tramp_memcmp : tramp_step 0x421a4 0x437f8. Proof. tramp_proof. Qed.
Lemma tramp_memset : tramp_step 0x51858 0x51f3c. Proof. tramp_proof. Qed.
