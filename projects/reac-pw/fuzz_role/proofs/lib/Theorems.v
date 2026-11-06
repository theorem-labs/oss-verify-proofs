From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require RoleTop.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require RoleTop.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require AgreeRole.

Definition reac_pw_fuzz_role_plain_halts :=
  OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog.RoleTop.plain_halts_holds.
Definition reac_pw_fuzz_role_ubsan_halts :=
  OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog.RoleTop.ubsan_halts_holds.
Definition reac_pw_fuzz_role_ubsan_agrees :=
  OSSVerify.Proofs.reac_pw.fuzz_role.lib.AgreeRole.ubsan_agrees_holds.
