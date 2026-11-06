From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require DiscoEnd.

Definition libreac_fuzz_disco_plain_halts :=
  OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.DiscoEnd.plain_halts_holds.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require DiscoEnd.

Definition libreac_fuzz_disco_ubsan_halts :=
  OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog.DiscoEnd.ubsan_halts_holds.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require DiscoAgree.

Definition libreac_fuzz_disco_ubsan_agrees :=
  OSSVerify.Proofs.libreac.fuzz_disco.lib.DiscoAgree.ubsan_agrees_holds.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AD2p DiscoRoA.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require DiscoLibX.

Definition libreac_fuzz_disco_asan_halts :=
  OSSVerify.Proofs.libreac.fuzz_disco.lib.A.AD2p.disco_asan_halts_of_parts
    OSSVerify.Proofs.libreac.fuzz_disco.lib.A.DiscoRoA.disco_H_RO
    OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog.DiscoLibX.disco_lib_x_all_acfn.

Definition libreac_fuzz_disco_asan_agrees :=
  OSSVerify.Proofs.libreac.fuzz_disco.lib.A.AD2p.disco_asan_agrees_of_parts
    OSSVerify.Proofs.libreac.fuzz_disco.lib.A.DiscoRoA.disco_H_RO
    OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog.DiscoLibX.disco_lib_x_all_acfn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YD2p.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require DiscoYLibX.

Definition libreac_fuzz_disco_asan_ubsan_halts :=
  OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable.YD2p.disco_asan_ubsan_halts_of_parts
    OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog.DiscoYLibX.tfib_lib_x_all_ycfn.

Definition libreac_fuzz_disco_asan_ubsan_agrees :=
  OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable.YD2p.disco_asan_ubsan_agrees_of_parts
    OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog.DiscoYLibX.tfib_lib_x_all_ycfn.
