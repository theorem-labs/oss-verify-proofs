From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l YP0b YP0a YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0d YP0c YI0w YI0z YC4a.
Import ListNotations.
Open Scope Z_scope.

Definition RA_LLVMF : Z := 0x80eb8.

Section d. Context {rc : YM05.RunCeil}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Definition d_sites (B : asyms) : list (list Z) :=
  [[pc_malloc_ra0 (as_code B); BASE + 0x6fc; RA_LLVMF]; [pc_malloc_ra0 (as_code B); BASE + 0xaf0; RA_LLVMF];
   [pc_malloc_ra0 (as_code B); BASE + 0xd74; RA_LLVMF]; [pc_free_ra0 (as_code B); BASE + 0x1d34; RA_LLVMF];
   [pc_free_ra0 (as_code B); BASE + 0x2268; RA_LLVMF]; [pc_free_ra0 (as_code B); BASE + 0x24a8; RA_LLVMF];
   [pc_malloc_ra0 (as_code B); BASE + 0x6fc]; [pc_malloc_ra0 (as_code B); BASE + 0xaf0];
   [pc_malloc_ra0 (as_code B); BASE + 0xd74]; [pc_free_ra0 (as_code B); BASE + 0x1d34];
   [pc_free_ra0 (as_code B); BASE + 0x2268]; [pc_free_ra0 (as_code B); BASE + 0x24a8]].
End f.
End d.
