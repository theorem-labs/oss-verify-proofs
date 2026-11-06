From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YG0f YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtFDefs.
Open Scope Z_scope.

(* THE PIECE TO BE TAKEN FROM ELSEWHERE. musl vsnprintf 0x9e490 (the value of the REAL(vsnprintf) slot 0xa8198) and
   everything it reaches on this image: musl vfprintf through the vfprintf trampoline 0x45174 (the interceptor
   0x497a4 and its printf_common call sit in between), printf_core 0x9b514, pop_arg, pad, __fwritex, sn_write, and
   the memset / memcpy / strnlen interceptor trampolines 0x57628 / 0x5762c / 0x45134. The contract is RtFDefs.v's
   avsnprintf_realizes at the window MUSL_VSN_STK and the stack-protector cells of RtAPI.v (0xa7098 -> 0x6045d8):
   every format pf_parse accepts (%d %c %s %04x %02x %llu %.*s and literal bytes).
   The walks of the snprintf and sprintf entries take it as the Section hypothesis
     Hypothesis MUSL_VSNPRINTF : musl_vsnprintf_ext segs B.
   The walk of the vfprintf interceptor 0x497a4 is in this directory's RtF files; a proof of this statement uses it
   at the vfprintf trampoline. *)
Definition musl_vsnprintf_ext {fx : YK11.FPState} {rc : YM05.RunCeil} (segs : list Segment) (B : asyms) : Prop :=
avsnprintf_realizes segs B MUSL_VSN_STK PC_musl_vsnprintf 0xa7098 0x6045d8.
