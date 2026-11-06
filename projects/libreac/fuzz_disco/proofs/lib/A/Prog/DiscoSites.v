From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05 YG00 YG0f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable DiscoSyms DiscoList DiscoAddr DiscoPa.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Definition RA_LLVMF : Z := 0x80e40.

Section f. Context {rc : YM05.RunCeil}.
Context {PI : PAImg disco_listing}.
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Definition d_sites (B : asyms) : list (list Z) :=
  [[pc_malloc_ra0 (as_code B); BASE + 0x718; RA_LLVMF]; [pc_malloc_ra0 (as_code B); BASE + 0xa98; RA_LLVMF];
   [pc_malloc_ra0 (as_code B); BASE + 0xc7c; RA_LLVMF]; [pc_free_ra0 (as_code B); BASE + 0x1b5c; RA_LLVMF];
   [pc_free_ra0 (as_code B); BASE + 0x22c8; RA_LLVMF]; [pc_free_ra0 (as_code B); BASE + 0x2554; RA_LLVMF];
   [pc_malloc_ra0 (as_code B); BASE + 0x718]; [pc_malloc_ra0 (as_code B); BASE + 0xa98];
   [pc_malloc_ra0 (as_code B); BASE + 0xc7c]; [pc_free_ra0 (as_code B); BASE + 0x1b5c];
   [pc_free_ra0 (as_code B); BASE + 0x22c8]; [pc_free_ra0 (as_code B); BASE + 0x2554]].
End f.
