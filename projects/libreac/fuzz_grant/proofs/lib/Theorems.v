From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require GrantEnd.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require GrantEnd.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require AgreeGrant.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A Require GrantTop.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require GrantBTop.

Definition libreac_fuzz_grant_plain_halts :=
  OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog.GrantEnd.plain_halts_holds.
Definition libreac_fuzz_grant_ubsan_halts :=
  OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog.GrantEnd.ubsan_halts_holds.
Definition libreac_fuzz_grant_ubsan_agrees :=
  OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog.AgreeGrant.ubsan_agrees_holds.
Definition libreac_fuzz_grant_asan_agrees :=
  OSSVerify.Proofs.libreac.fuzz_grant.lib.A.GrantTop.grant_asan_agrees_of_parts.
Definition libreac_fuzz_grant_asan_halts :=
  OSSVerify.Proofs.libreac.fuzz_grant.lib.A.GrantTop.grant_asan_halts_of_parts.
Definition libreac_fuzz_grant_asan_ubsan_agrees :=
  OSSVerify.Proofs.libreac.fuzz_grant.lib.B.GrantBTop.grant_asan_ubsan_agrees_of_parts.
Definition libreac_fuzz_grant_asan_ubsan_halts :=
  OSSVerify.Proofs.libreac.fuzz_grant.lib.B.GrantBTop.grant_asan_ubsan_halts_of_parts.
