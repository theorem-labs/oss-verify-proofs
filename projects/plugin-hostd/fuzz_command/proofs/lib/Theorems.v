From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require CmdEnd.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require CmdEnd.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require AgreeCmd.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require CmdTop.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtDtorExit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdProgClosed.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require CmdTopB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtDtorExit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdProgClosed.

Definition plugin_hostd_fuzz_command_plain_halts :=
  OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.CmdEnd.plain_halts_holds.
Definition plugin_hostd_fuzz_command_ubsan_halts :=
  OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CmdEnd.ubsan_halts_holds.
Definition plugin_hostd_fuzz_command_ubsan_agrees :=
  OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.AgreeCmd.ubsan_agrees_holds.
Definition plugin_hostd_fuzz_command_asan_agrees :=
  @OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.CmdTop.cmd_asan_agrees_of_parts
    OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt.RtDtorExit.cmd_dtor_exit
    (fun rc => @OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog.CmdProgClosed.cmd_ltoi_all rc).
Definition plugin_hostd_fuzz_command_asan_halts :=
  @OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.CmdTop.cmd_asan_halts_of_parts
    OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt.RtDtorExit.cmd_dtor_exit
    (fun rc => @OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog.CmdProgClosed.cmd_ltoi_all rc).
Definition plugin_hostd_fuzz_command_asan_ubsan_agrees :=
  @OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.CmdTopB.cmd_asan_ubsan_agrees_of_parts
    OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt.RtDtorExit.cmd_dtor_exit_b
    (fun rc => @OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog.CmdProgClosed.cmd_ltoi_all_B rc).
Definition plugin_hostd_fuzz_command_asan_ubsan_halts :=
  @OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.CmdTopB.cmd_asan_ubsan_halts_of_parts
    OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt.RtDtorExit.cmd_dtor_exit_b
    (fun rc => @OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog.CmdProgClosed.cmd_ltoi_all_B rc).
