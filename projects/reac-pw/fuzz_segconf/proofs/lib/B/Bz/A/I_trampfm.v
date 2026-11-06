(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Bz/A/I_trampfm.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
(* The strncasecmp trampoline of reac-pw/fuzz_segconf.asan-ubsan: __interceptor_trampoline_strncasecmp 0x43aac is one jump
   to __interceptor_strncasecmp 0x45088. omx-clap-core/fuzz_manifest states it in its lib/A/Bz/A/I_tramp.v
   (tramp_strncasecmp, at fm.asan's 0x412d8 -> 0x423a0); this tree's A/Bz/A/I_tramp.v is fuzz_command's, which has no
   strncasecmp entry, so the one lemma is stated here with that file's tramp_step and tramp_proof. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A Require Import I_tramp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma tramp_strncasecmp : tramp_step 0x43aac 0x45088. Proof. tramp_proof. Qed.
