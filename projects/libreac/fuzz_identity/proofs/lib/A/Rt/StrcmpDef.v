(* libreac/fuzz_identity, build asan (fuzz_identity.asan): the contract of the strcmp wrapper as the program code
   calls it. STRCMP_ENTRY is the trampoline __interceptor_trampoline_strcmp, which jumps to ___interceptor_strcmp.
   Since 2026-10-29 the statement itself is NOT written here: it is lib/Reusable/AStrcmpDef.astrcmp_realizes, the text
   of record for the strcmp trampoline contract in the registry (proved on libreac/fuzz_grant
   image A at a working branch 97c611eec86). This file keeps the name the identity callers cite and the entry
   address. The earlier identity-local statement (the same premises, with the result stated as `v = w64 0` exactly
   when the bytes at k are equal instead of the CharCmpX value) is superseded; `strcmp_res c1 c2 = 0 <-> c1 = c2`
   gives it back in one step.
   Address check: the pinned binary (sha256 c954b804786cb87fc218414447199e35235b9788453ec0db312f97cd0dc4291b) against
   cgif_file_fuzzer.asan (sha256 7093581aab040cfd94ed56f83bf44a37e6ec3c34db39cc57bf467e2949e870f0):
   | pc      | word       | instruction                              | cgif_file_fuzzer counterpart          |
   |---------|------------|------------------------------------------|---------------------------------------|
   | 0x42194 | 0x5b40006f | j 0x42748 <___interceptor_strcmp>        | 0x418f8 0x5bc0006f j 0x41eb4          |
   | 0x42748 | 0x81010113 | addi sp,sp,-2032 (___interceptor_strcmp) | 0x41eb4 0x81010113 (funcmatch `same`) |
   | 0x42744 | 0x00008067 | ret (__sanitizer_weak_hook_strcmp)       | 0x41eb0 0x00008067                    |
*)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YM05 YK0s YK0i YK15 YK0j YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import AStrcmpDef.
Import ListNotations.
Open Scope Z_scope.
Definition STRCMP_ENTRY : Z := 0x42194.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition astrcmp_realizes (segs : list Segment) (B : asyms) (pc : Z) : Prop :=
  AStrcmpDef.astrcmp_realizes segs B pc.
End b.
