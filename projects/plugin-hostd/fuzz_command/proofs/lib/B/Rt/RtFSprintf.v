(* Modified by Theorem Labs, 2026-10: relocated from lib/A/<same path> to fuzz_command.asan-ubsan by the image-B address relocator (the A-to-B address map, keyed by the image maps' symbol names and by code; GXA symbol keys kept), whose check table lists every changed numeral *)
(* The sprintf contract of lib/B/Rt/RtFormat.v (asprintf_realizes = RtPFCmd.asprintf_sh, fuzz_manifest's shared
   sprintf text at FR_cmd) at PC_sprintf = 0x451cc, the trampoline of ___interceptor_sprintf 0x49f74, which calls
   ___interceptor_vsprintf 0x49bbc, which calls REAL(vsprintf) = musl vsprintf 0x9e194 (slot 0xa7d00), which tail-jumps
   to the vsnprintf trampoline 0x451c4 (`j 0x498a4`) with n = 0x7fffffff.
   The walk (RtFSprintfRun.v, RtFSprintfE.v, RtFSprintfW.v) steps the three bodies and TryAsanInitFromRtl; the write-range
   check site 0x49c5c .. 0x49ca4 is RtFSprintfChk2.v spf_check_srr (its range check 0x5a1f8 by RtSRegion.cmd_region_band).
   Window CMD_SP_K = 3 * ESTACK: the two frames 2,240, then the vsnprintf interceptor's window 2 * ESTACK (SP_KVS) or
   printf_common's ESTACK (SP_KPC) below them.
   The two callee contracts are omx-clap-core/fuzz_manifest's GXA route at this image (relocated by the GXA address
   relocator), instantiated at FR_cmd in RtFSnprintf.v:
   - printf_common 0x48d28, sh_apcommon_realizesUz at the window SP_KPC = ESTACK (RtFSnprintf.cmd_pcommon, from
     RT_pf_shU.pcom_shzK at fuzz_command's pieces, for every window K >= 2320);
   - the vsnprintf interceptor ___interceptor_vsnprintf 0x498a4 (run B steps its trampoline 0x451c4),
     sh_avsnprintf_icpt_realizesUa at the window SP_KVS = 2 * ESTACK (RtFSnprintf.cmd_vsni, FMsnprintfSvsni.svsni_ok
     over musl vsnprintf, the vfprintf interceptor and the seam at musl vfprintf; n = 0x7fffffff meets its
     1 <= n < 2^31).
   Both with the read-only list CMD_SP_CR (RtPFCmd.v) and, for the vsnprintf interceptor, the stack-protector cells
   0xa6bf8 -> 0x604158 and the image range 0x10000 .. 0x606000 (dest_off_globals); their extra premises (the va area
   below 2^47, at or above the callee's sp and off the destination, the destination's slack word) come from the
   sprintf contract's own premises (RtPFCmd.v sh_asprintf_realizes). The world field w_H8 the seam uses is the class
   RtWH8.WH8, resolved by its instance (the core's world field). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0s YK0i YK15 YK0j YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtPFShared RtPFSx RtPFCmd RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtFSprintfRun RtFSprintfE RtFSprintfW.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtFSprintfChk1 RtFSprintfChk2.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtWH8 RtFSnprintf.
Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Theorem cmd_sprintf : forall B, AR_laws tfibsegs B -> CmdBSyms B ->
  RtFormat.asprintf_realizes tfibsegs B PC_sprintf A_SSP_GOT A_SSP_GUARD.
Proof.
intros B LAWS TB.
exact (spf_walk B LAWS TB RtFSprintfChk1.SPC_SCR ltac:(unfold RtFSprintfChk1.SPC_SCR, ESTACK; lia)
  (fun fx0 => @RtFSprintfChk2.spf_check_srr fx0 rc B LAWS TB)
  (RtFSnprintf.cmd_pcommon B LAWS TB SP_KPC ltac:(unfold SP_KPC, ESTACK; lia)) (RtFSnprintf.cmd_vsni B LAWS TB)).
Qed.
End c.
