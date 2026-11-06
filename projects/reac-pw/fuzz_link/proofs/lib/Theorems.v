From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require LTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require LinkClose.

Definition reac_pw_fuzz_link_plain_halts :=
  OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot.LTop.plain_halts_holds.

Definition reac_pw_fuzz_link_asan_agrees :=
  OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.LinkClose.link_asan_agrees_of_parts.

Definition reac_pw_fuzz_link_asan_halts :=
  OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.LinkClose.link_asan_halts_of_parts.
