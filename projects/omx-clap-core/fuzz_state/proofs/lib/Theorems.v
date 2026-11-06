From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Link.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Link.

Definition omx_clap_core_fuzz_state_plain_halts :=
  OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.Link.plain_halts_proved.
Definition omx_clap_core_fuzz_state_ubsan_halts :=
  OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.Link.ubsan_halts_proved.
