(* libreac/fuzz_identity, build asan-ubsan (fuzz_identity.asan-ubsan): the contract of the strcmp wrapper as the
   program code calls it. STRCMP_ENTRY is the trampoline __interceptor_trampoline_strcmp, which jumps to
   ___interceptor_strcmp. Since 2026-10-29 the statement itself is NOT written here: it is
   lib/Reusable/AStrcmpDef.astrcmp_realizes, the text of record for the strcmp trampoline contract in the
   registry (proved on libreac/fuzz_grant image A at a working branch 97c611eec86). This
   file keeps the name the identity callers cite and the asan-ubsan entry address. The earlier identity-local
   statement is superseded; `strcmp_res c1 c2 = 0 <-> c1 = c2` gives its result clause back in one step.
   Address check against the pinned binary
   (sha256 baf1a4d065e02f55521d39f05d8c8d9ed763a0ef798c70cc3eabe5816ffb3f66):
   | pc      | word       | instruction                              |
   |---------|------------|------------------------------------------|
   | 0x421fc | 0x5b40006f | j 0x427b0 <___interceptor_strcmp>        |
   | 0x427b0 | 0x81010113 | addi sp,sp,-2032 (___interceptor_strcmp) |
   | 0x427ac | 0x00008067 | ret (__sanitizer_weak_hook_strcmp)       |
*)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YM05 YK0s YK0i YK15 YK0j YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import AStrcmpDef.
Import ListNotations.
Open Scope Z_scope.
Definition STRCMP_ENTRY : Z := 0x421fc.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition astrcmp_realizes (segs : list Segment) (B : asyms) (pc : Z) : Prop :=
  AStrcmpDef.astrcmp_realizes segs B pc.
End b.
