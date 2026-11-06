(* The strcspn contract of lib/B/Rt/RtString.v (astrcspn_realizes, window 2 * ESTACK) at PC_strcspn = 0x45198, the
   one-instruction trampoline `j 0x46ce4` of ___interceptor_strcspn. The two halves meet at the contract of musl's
   strcspn (RtSStrcspnDef.amcspn_realizes, entry 0x9ee10, window 80 + 16 + ESTACK):
   - the interceptor half, RtSStrcspnIW.cmd_strcspn_icpt, walks the interceptor from its trampoline to its return
     and takes musl's strcspn at its REAL call (sp0 - 2160, return address 0x46d3c);
   - the musl half, RtSStrcspnM.cmd_mcspn, is fuzz_command's released plain walk of musl strcspn 0x9ee10 and
     strchrnul 0x9ec10 (lib/Prog/strcspn.v, lib/R_strchr.v) moved to this ASan+UBSan image and lifted into the SRr
     form; it calls the strlen interceptor under RtSStrlen.cmd_strlen and the memset interceptor 0x57674 under
     aintrin_realizes OSet.
   The memset interceptor's contract is the premise AMEMSET, as on image A (lib/A/Rt/RtSStrcspn.v), until a
   relocation of cgif's memset walk (memset_icpt_realizes, cgif_file_fuzzer's lib/YE32.v) is in this tree. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YK0i YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtAPI RtSStrcspnDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtSStrcspnIW RtSStrcspnM.
Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Theorem cmd_strcspn : forall (B : asyms), AR_laws tfibsegs B -> CmdBSyms B ->
aintrin_realizes tfibsegs B OSet 0x57674 ->
astrcspn_realizes tfibsegs B PC_strcspn A_SSP_GOT A_SSP_GUARD.
Proof.
intros B LAWS TB AMEMSET.
exact (RtSStrcspnIW.cmd_strcspn_icpt B LAWS TB (RtSStrcspnM.cmd_mcspn B LAWS TB AMEMSET)).
Qed.

End c.
