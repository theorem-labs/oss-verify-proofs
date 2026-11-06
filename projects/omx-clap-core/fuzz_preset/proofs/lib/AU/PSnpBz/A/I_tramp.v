(* Modified by Theorem Labs, 2026-10: moved from image B (fuzz_preset.asan-ubsan f8f98a95), commit 3244f5c71f6, to the #102 pin B' (fuzz_preset.asan-ubsan d663f82d, unstripped c90d4fa5): 14 address numerals by the frozen alreloc (sha256 c4338d099cfb8025, commit d99acc3edd9, same-unit move, --assume-source), each by symbol + offset in both images, or for a .rodata string by its unique content in both; GXA keys and history lines kept (report and decisions: the relocation record, the internal file resolve-B-why.tsv). *)
(* Modified by Theorem Labs, 2026-10: relocated onto omx-clap-core/fuzz_preset.asan-ubsan (image B, f8f98a95) from commit 3e35620c52e proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/A/I_tramp.v: module paths (lib/A/Bz -> lib/AU/PSnpBz) and the address numerals by alreloc (sha256 c4338d099cfb8025, commit d99acc3edd97, --build asan-ubsan --from-build asan), each by symbol + offset in both images (per-numeral report: the relocation record, B-run); tramp_strncmp and tramp_strncasecmp DELETED: fuzz_preset has no strncmp / strncasecmp interceptor (no ___interceptor_strncmp / ___interceptor_strncasecmp symbol in either image). *)
(* Ported by the runtime port from commit affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/A/I_tramp.v, unchanged. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Lib Require Import StoreFast.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.P Require Import Str_tac Startup_glue.
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

Lemma tramp_strlen : tramp_step 0x42e04 0x42e94. Proof. tramp_proof. Qed.
Lemma tramp_strnlen : tramp_step 0x42e08 0x43128. Proof. tramp_proof. Qed.
Lemma tramp_memchr : tramp_step 0x42e1c 0x445e0. Proof. tramp_proof. Qed.
Lemma tramp_memcpy : tramp_step 0x524cc 0x52e9c. Proof. tramp_proof. Qed.
Lemma tramp_bcmp : tramp_step 0x42e18 0x44524. Proof. tramp_proof. Qed.
Lemma tramp_memcmp : tramp_step 0x42e14 0x44468. Proof. tramp_proof. Qed.
Lemma tramp_memset : tramp_step 0x524c8 0x52bac. Proof. tramp_proof. Qed.
