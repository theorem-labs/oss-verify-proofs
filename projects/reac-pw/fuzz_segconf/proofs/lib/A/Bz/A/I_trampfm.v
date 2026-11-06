(* The strncasecmp trampoline of reac-pw/fuzz_segconf.asan: __interceptor_trampoline_strncasecmp 0x43a20 is one jump
   to __interceptor_strncasecmp 0x44ffc. omx-clap-core/fuzz_manifest states it in its lib/A/Bz/A/I_tramp.v
   (tramp_strncasecmp, at fm.asan's 0x412d8 -> 0x423a0); this tree's A/Bz/A/I_tramp.v is fuzz_command's, which has no
   strncasecmp entry, so the one lemma is stated here with that file's tramp_step and tramp_proof. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A Require Import I_tramp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma tramp_strncasecmp : tramp_step 0x43a20 0x44ffc. Proof. tramp_proof. Qed.
