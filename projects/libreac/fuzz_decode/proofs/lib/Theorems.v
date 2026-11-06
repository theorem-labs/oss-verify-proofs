From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require LLVMFuzzerTestOneInput_halts.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require LLVMFuzzerTestOneInput_halts.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require LLVMFuzzerTestOneInput_agree.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require DecodeClose.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require DecodeBClose.

Definition libreac_fuzz_decode_plain_halts :=
  OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog.LLVMFuzzerTestOneInput_halts.plain_halts_holds.
Definition libreac_fuzz_decode_ubsan_halts :=
  OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog.LLVMFuzzerTestOneInput_halts.ubsan_halts_holds.
Definition libreac_fuzz_decode_ubsan_agrees :=
  OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog.LLVMFuzzerTestOneInput_agree.ubsan_agrees_holds.
Definition libreac_fuzz_decode_asan_halts :=
  OSSVerify.Proofs.libreac.fuzz_decode.lib.A.DecodeClose.decode_asan_halts_of_parts.
Definition libreac_fuzz_decode_asan_agrees :=
  OSSVerify.Proofs.libreac.fuzz_decode.lib.A.DecodeClose.decode_asan_agrees_of_parts.
Definition libreac_fuzz_decode_asan_ubsan_halts :=
  OSSVerify.Proofs.libreac.fuzz_decode.lib.B.DecodeBClose.decode_asan_ubsan_halts_of_parts.
Definition libreac_fuzz_decode_asan_ubsan_agrees :=
  OSSVerify.Proofs.libreac.fuzz_decode.lib.B.DecodeBClose.decode_asan_ubsan_agrees_of_parts.
