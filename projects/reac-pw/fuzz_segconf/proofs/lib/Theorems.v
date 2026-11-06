From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require SegTop.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require SegTop.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require SegTopAgree.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require SegClose.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require SegTopB.

Definition reac_pw_fuzz_segconf_plain_halts :=
  OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.SegTop.plain_halts_holds.
Definition reac_pw_fuzz_segconf_ubsan_halts :=
  OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.SegTop.ubsan_halts_holds.
Definition reac_pw_fuzz_segconf_ubsan_agrees :=
  OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.SegTopAgree.ubsan_agrees_holds.
Definition reac_pw_fuzz_segconf_asan_halts :=
  OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.SegClose.seg_asan_halts_closed.
Definition reac_pw_fuzz_segconf_asan_agrees :=
  OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.SegClose.seg_asan_agrees_closed.
Definition reac_pw_fuzz_segconf_asan_ubsan_halts :=
  OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.SegTopB.seg_asan_ubsan_halts_of_parts.
Definition reac_pw_fuzz_segconf_asan_ubsan_agrees :=
  OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.SegTopB.seg_asan_ubsan_agrees_of_parts.
