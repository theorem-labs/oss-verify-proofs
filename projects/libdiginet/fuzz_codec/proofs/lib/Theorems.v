From OSSVerify.libdiginet.fuzz_codec Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require LLVMFuzzerTestOneInput_c CodecEnd CodecMainProved.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require LLVMFuzzerTestOneInput_c CodecEnd CodecMainProved.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require AgreeCodec.

(* Each top over its build's main contract (codec_main_contract of Prog/ and U/Prog/LLVMFuzzerTestOneInput_c). *)

Definition libdiginet_fuzz_codec_plain_halts :
  OSSVerify.libdiginet.fuzz_codec.Statements.plain_halts :=
  OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog.CodecEnd.plain_halts_holds
    OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog.CodecMainProved.codec_main_proved.
Definition libdiginet_fuzz_codec_ubsan_halts :
  OSSVerify.libdiginet.fuzz_codec.Statements.ubsan_halts :=
  OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog.CodecEnd.ubsan_halts_holds
    OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog.CodecMainProved.codec_main_proved.
Definition libdiginet_fuzz_codec_ubsan_agrees :
  OSSVerify.libdiginet.fuzz_codec.Statements.ubsan_agrees :=
  OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AgreeCodec.ubsan_agrees_holds
    OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog.CodecMainProved.codec_main_proved
    OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog.CodecMainProved.codec_main_proved.
Definition libdiginet_fuzz_codec_plain_halts_may_fail :
  OSSVerify.libdiginet.fuzz_codec.Statements.plain_halts_may_fail :=
  OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog.CodecEnd.plain_halts_may_fail_holds
    OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog.CodecMainProved.codec_main_proved.
Definition libdiginet_fuzz_codec_ubsan_halts_may_fail :
  OSSVerify.libdiginet.fuzz_codec.Statements.ubsan_halts_may_fail :=
  OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog.CodecEnd.ubsan_halts_may_fail_holds
    OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog.CodecMainProved.codec_main_proved.
